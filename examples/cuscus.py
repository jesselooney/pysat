#!/usr/bin/env python3

from __future__ import annotations

import argparse
import collections
import csv
from dataclasses import dataclass
from pathlib import Path
import sys
import time

from pysat._fileio import FileObject
from pysat.card import ISeqCounter
from pysat.formula import IDPool
from pysat.solvers import Solver


# Use our own formula and parser because PySAT's builtin has some bugs.
# TODO: Document.
@dataclass
class WCNF:
    soft_clauses: list[tuple[list[int], int]]
    hard_clauses: list[list[int]]
    # The largest variable id used in the formula. Equivalent to the maximum
    # absolute value of any literal. If the formula has no variables, we define
    # `top_id` to be zero.
    top_id: int

    @classmethod
    def from_path(cls, path):
        # Read the file, using the extension to determine how to decompress.
        with FileObject(name=path, mode="r", compression="use_ext") as file:
            return cls.from_file(file.fp)

    @classmethod
    def from_file(cls, file):
        soft_clauses: list[tuple[list[int], int]] = []
        hard_clauses: list[list[int]] = []

        variables: set[int] = set()

        for line_number, line in enumerate(file.readlines(), start=1):
            stripped_line = line.strip()

            # Ignore empty lines.
            if not stripped_line:
                continue

            parts: list[str] = stripped_line.split()

            if parts[0] == "h":
                # Hard clause.
                clause = WCNF._parse_literals(line_number, stripped_line, parts)
                variables |= {abs(lit) for lit in clause}
                hard_clauses.append(clause)
            elif WCNF._is_int(parts[0]):
                # Soft clause.
                weight = int(parts[0])
                if weight <= 0:
                    raise ValueError(
                        f"Invalid clause on line {line_number}: '{stripped_line}'\n"
                        f"Soft clauses must have positive weight, but {weight} is not positive."
                    )
                clause = WCNF._parse_literals(line_number, stripped_line, parts)
                variables |= {abs(lit) for lit in clause}
                soft_clauses.append((clause, weight))
            elif parts[0][0] in "pc":
                # Problem statement or comment line; ignore.
                continue
            else:
                raise ValueError(
                    f"Invalid line header on line {line_number}: '{stripped_line}'\n"
                    f"Lines must start with 'p', 'c', 'h', or a numeric weight, not '{parts[0]}'."
                )

        if variables:
            top_id = max(variables)
        else:
            top_id = 0

        return cls(soft_clauses=soft_clauses, hard_clauses=hard_clauses, top_id=top_id)

    @staticmethod
    def _is_int(string: str) -> bool:
        try:
            int(string)
        except ValueError:
            return False
        return True

    @staticmethod
    def _parse_literals(
        line_number: int, stripped_line: str, parts: list[str]
    ) -> list[int]:
        if parts[-1] != "0":
            raise ValueError(
                f"Invalid clause on line {line_number}: '{stripped_line}'\n"
                f"Clauses must end with '0', not '{parts[-1]}'."
            )

        literals: list[int] = []
        for index, literal_str in enumerate(parts[1:-1]):
            try:
                literal = int(literal_str)
            except ValueError:
                raise ValueError(
                    f"Invalid clause on line {line_number}: '{stripped_line}'\n"
                    f"Clauses literals must be integers, but '{literal_str}' (index {index}) is not an integer."
                )

            if literal == 0:
                raise ValueError(
                    f"Invalid clause on line {line_number}: '{stripped_line}'\n"
                    f"Clauses may not contain the variable 0 (found at index {index})."
                )

            literals.append(literal)

        if not literals:
            raise ValueError(
                f"Invalid clause on line {line_number}: '{stripped_line}'\n"
                "Empty clauses are not allowed."
            )

        return literals


@dataclass
class CardinalityMetadata:
    encoder: ISeqCounter
    prefixes: list[tuple[int, int]]
    prefix_index: int
    upper_bound: int

    def __post_init__(self):
        if self.prefix_index not in range(len(self.prefixes)):
            raise ValueError(
                f"`prefix_index` must index `prefixes`, but {self.prefix_index} is not in [0, {len(self.prefixes)})"
            )
        # A negative upper bound is impossible and not supported by
        # `ISeqCounter`.
        if self.upper_bound < 0:
            raise ValueError(
                f"`upper_bound` must be non-negative, but {self.upper_bound} < 0"
            )
        # An upper bound equal to or exceeding the number of literals being
        # bounded is trivial and not supported by `ISeqCounter`.
        if self.upper_bound >= self.prefix_len:
            raise ValueError(
                f"`upper_bound` must be less than `prefix_len`, but {self.upper_bound} >= {self.prefix_len}"
            )

    @property
    def prefix(self) -> tuple[int, int]:
        return self.prefixes[self.prefix_index]

    @property
    def prefix_len(self) -> int:
        return self.prefix[0]

    @property
    def weight(self) -> int:
        return self.prefix[1]

    @property
    def consequents(self) -> list[CardinalityMetadata]:
        """The cardinality constraints most directly implied by this one."""
        consequents: list[CardinalityMetadata] = []

        # Add both of the consequents, skipping any that are invalid.

        try:
            consequents.append(
                CardinalityMetadata(
                    encoder=self.encoder,
                    prefixes=self.prefixes,
                    prefix_index=self.prefix_index,
                    upper_bound=self.upper_bound + 1,
                )
            )
        except ValueError:
            pass

        try:
            consequents.append(
                CardinalityMetadata(
                    encoder=self.encoder,
                    prefixes=self.prefixes,
                    prefix_index=self.prefix_index - 1,
                    upper_bound=self.upper_bound,
                )
            )
        except ValueError:
            pass

        return consequents


class Cuscus:
    def __init__(
        self,
        formula: WCNF,
        *,
        should_harden_unit_cores: bool = False,
        should_minimize: bool = False,
        should_transform_am1s: bool = False,
        solver_name: str = "cadical195",
        verbosity: int = 0,
        watched_models: list[tuple[list[int], int | None]] = [],
    ):
        self.should_harden_unit_cores = should_harden_unit_cores
        self.should_minimize = should_minimize
        self.should_transform_am1s = should_transform_am1s
        self.verbosity = verbosity
        # A list of models and their expected costs to watch as the solver
        # runs. If a watched model's calculated cost ever differs from its
        # given expected cost, an error is thrown. If the expected cost is set
        # to `None`, its initial cost (calculated before the formula is ever
        # transformed) will be used as the expected cost. This setting is
        # intended to be used for debugging.
        # TODO: Give an example input and its interpretation.
        self.watched_models: list[tuple[list[int], int | None]] = watched_models

        self.solver_name = solver_name
        self.minimization_max_conflicts = 1000

        # The set of variables that appear in the original formula we were
        # given. Used to filter the model returned.
        self._original_vars: set[int] = set(range(1, formula.top_id + 1))
        # A mapping from selector literals to the weight of the clause each
        # one enables.
        self._selector_weights: dict[int, int] = {}
        # The set of all selectors that have been relaxed (i.e. removed because
        # they were part of a core). Used to prevent reactivating a selector
        # that was previously removed, which would be a logic error.
        self._relaxed_selectors: set[int] = set()
        # A mapping from selector literals representing cardinality constraints
        # to metadata for the constraint.
        self._cardinality_metadata: dict[int, CardinalityMetadata] = {}
        # Selectors that are intended to be added but which have been deferred.
        # May include already relaxed selectors, so check against
        # `self._relaxed_selectors`. Intended for use in model watching.
        self._deferred_selectors: set[int] = set()

        self._id_pool = IDPool(start_from=formula.top_id + 1)
        self._oracle = Solver(
            name=self.solver_name, bootstrap_with=formula.hard_clauses, use_timer=True
        )

        # Add the initial soft clauses to the problem formula.
        for clause, weight in formula.soft_clauses:
            self._add_soft_clause(clause, weight)

    def __del__(self):
        # TODO: Perform any necessary cleanup.
        pass

    def _add_soft_clause(self, clause: list[int], weight: int) -> int:
        """
        Add a soft clause to the problem formula with a given weight.

        Returns the selector literal that activates the clause.
        """
        assert weight > 0  # TODO: Document that we dont except weights <= 0.
        # TODO: For unit clauses, perhaps reuse the literal as the selector.
        selector = self._id_pool.id()
        self._oracle.add_clause(clause + [-selector])
        self._selector_weights[selector] = weight
        return selector

    def _add_hard_clause(self, clause: list[int]):
        """Add a hard clause to the problem formula."""
        self._oracle.add_clause(clause)

    def _get_cost(self, model: list[int], active_selectors: list[int]) -> int | None:
        """
        Compute the cost of a model given some active selectors.

        `model` must be a list of literals representing a partial (or total)
        assignment to the variables of the problem formula.

        Returns the total weight of all selectors in `active_selectors`
        contradicted by the model, or `None` if the model does not satisfy the
        current hard clauses of the formula.
        """
        if not self._oracle.solve(assumptions=model):
            return None

        # We test each selector individually to see if it is contradicted.
        contradicted_selectors: list[int] = []
        cost = 0
        for selector in active_selectors:
            if not self._oracle.solve(assumptions=model + [selector]):
                contradicted_selectors.append(selector)
                cost += self._selector_weights[selector]

        if self.verbosity >= 2:
            print(f"c watched model contradicted selectors: {contradicted_selectors}")

        return cost

    def _verify_watched_models(self, active_selectors: list[int], accrued_cost: int):
        for model_index, (model, expected_cost) in enumerate(self.watched_models):
            active_cost = self._get_cost(model, active_selectors)

            pending_selectors: set[int] = self._deferred_selectors - (self._relaxed_selectors | set(active_selectors))
            pending_cost = self._get_cost(model, list(pending_selectors))

            if active_cost is None or pending_cost is None:
                raise Exception(
                    f"watched model {model_index} contradicts the hard clauses"
                )
            
            model_cost: int = active_cost + pending_cost

            computed_cost = model_cost + accrued_cost

            # Initialize the expected cost if one was not given.
            if expected_cost is None:
                expected_cost = computed_cost
                self.watched_models[model_index] = (model, expected_cost)

            if computed_cost != expected_cost:
                raise Exception(
                    f"watched model {model_index} has unexpected cost\n"
                    f"\texpected cost: {expected_cost}\n"
                    f"\tcomputed cost: {computed_cost}"
                )

    def solve(self) -> tuple[int, list[int]] | None:
        """
        Find the minimum cost to satisfy the problem formula.

        Returns a pair `(cost, model)`, where `model` is an assignment with
        minimal cost `cost`. If the hard clauses of the formula are
        unsatisfiable, this method returns `None` instead.
        """
        if not self._oracle.solve():
            # The hard clauses are unsatisfiable.
            return None

        # The set of selectors whose clauses should be activated. We start by
        # activating all selectors.
        active_selectors: list[int] = list(self._selector_weights.keys())
        # The cost accrued so far due to forced clause falsifications.
        cost = 0

        all_weights = {self._selector_weights[s] for s in active_selectors}
        # TODO: Maybe set this parameter somewhere else.
        self.diversity_threshold = len(all_weights) / 2.0
        # Not a typo. We initialize the minimum weight threshold to the highest
        # weight in the formula and then iteratively decrease it to add in
        # smaller weight clauses.
        min_weight = max(all_weights) if all_weights else 0

        # TODO: Figure out a way around this hack.
        next_min_weight = self._get_next_min_weight(min_weight, active_selectors)
        if next_min_weight is not None:
            min_weight = next_min_weight
        
        while min_weight:
            active_selectors, cost = self.solve_with_threshold(active_selectors, cost, min_weight)
            # TODO: Harden clauses
            min_weight = self._get_next_min_weight(min_weight, active_selectors)

        model: list[int] = self._oracle.get_model()

        # `model` contains extraneous variables added during solving, so we
        # filter it to return a model containing only variables that appeared
        # in the original formula we were given.
        original_model: list[int] = [
            lit for lit in model if abs(lit) in self._original_vars
        ]

        return cost, original_model

    def _get_next_min_weight(self, min_weight: int, active_selectors: list[int]) -> int | None:
        all_weights: set[int] = {self._selector_weights[s] for s in active_selectors}
        smaller_weights = sorted([weight for weight in all_weights if weight < min_weight], reverse=True)

        if not smaller_weights:
            return None

        for new_min_weight in smaller_weights[:-1]:
            # The weight of each active selector whose weight is less than `new_min_weight`.
            # TODO: This is a really confusing name given `smaller_weights` above.
            smaller_selector_weights = [s for s in active_selectors if self._selector_weights[s] < new_min_weight]

            # The number of selectors with weight less than `new_min_weight`.
            smaller_selector_count = len(smaller_selector_weights)

            # The sum of the weights of those selectors.
            smaller_weight_total = sum(smaller_selector_weights)

            # "partial BLO" according to RC2
            # TODO: why check that `smaller_weight_total != 0`?
            if new_min_weight > smaller_weight_total and smaller_weight_total != 0:
                return new_min_weight

            if smaller_selector_count / float(len(set(smaller_selector_weights))) > self.diversity_threshold:
                return new_min_weight

        return smaller_weights[-1]

    def solve_with_threshold(self, active_selectors: list[int], cost: int, min_weight: int) -> tuple[list[int], int]:
        # Verify any watched models against the initial selectors and cost.
        if self.watched_models:
            self._verify_watched_models(active_selectors, cost)

        core_count = 0
        total_processing_time = 0
        total_core_size = 0

        if self.should_transform_am1s:
            active_selectors, cost = self._transform_am1s(active_selectors, cost)
            # Verify any watched models after transforming am1s.
            if self.watched_models:
                self._verify_watched_models(active_selectors, cost)

        while not self._oracle.solve(assumptions=[s for s in active_selectors if self._selector_weights[s] >= min_weight]):
            start_time = time.perf_counter()

            core: list[int] = self._oracle.get_core()
            assert core
            core_count += 1

            reduced_core: list[int] = self._reduce_core(core)
            total_core_size += len(reduced_core)

            active_selectors, cost = self._transform_core(
                set(reduced_core), active_selectors, cost
            )

            # TODO: Add core exhaustion.

            end_time = time.perf_counter()
            processing_time = end_time - start_time
            processing_time += processing_time

            if self.verbosity >= 1:
                print(
                    f"c cores found: {core_count}; cost: {cost}; core size: {len(reduced_core)}; soft size: {len(active_selectors)}; processing time: {processing_time}"
                )
            if self.verbosity >= 2:
                print(f"c reduced core: {reduced_core}")
                print(f"c active_selectors: {active_selectors}")

            # Verify any watched models against the new selectors and cost.
            if self.watched_models:
                self._verify_watched_models(active_selectors, cost)

            # Ensure we haven't accidentally activated a previously relaxed selector.
            assert set(active_selectors).isdisjoint(self._relaxed_selectors)
            # Ensure `active_selectors` has no duplicate values, as there is no
            # reason to have duplicates. Also, keeping this invariant may
            # reduce the likelihood of unexpected behavior.
            assert len(active_selectors) == len(set(active_selectors))

        if self.verbosity >= 1:
            print(f"c oracle time: {self._oracle.time_accum()}")
            print(f"c total processing time: {total_processing_time}")
            print(f"c cores found: {core_count}")
            if core_count:
                print(f"c mean core size: {total_core_size / float(core_count)}")

        # We have relaxed the problem formula enough to make it satisfiable.
        return active_selectors, cost

    def _reduce_core(self, core: list[int]) -> list[int]:
        # TODO: Document.
        reduced_core = core

        if self.should_minimize:
            reduced_core = self._minimize_core(reduced_core)

        return reduced_core

    def _minimize_core(self, core: list[int]) -> list[int]:
        # TODO: Better documentation.
        """Attempt to minimize a core `core`."""
        if len(core) < 2:
            # The core is unit or empty, so minimization will not help.
            return core

        sorted_core: list[int] = sorted(core, key=lambda s: self._selector_weights[s])

        # Limit the number of conflicts allowed in the following
        # `solve_limited()` calls.
        self._oracle.conf_budget(self.minimization_max_conflicts)

        for i in range(len(sorted_core)):
            # Exclude a single selector from the original core.
            possible_core: list[int] = sorted_core[:i] + sorted_core[i + 1 :]

            match self._oracle.solve_limited(assumptions=possible_core):
                case False:
                    # `possible_core` is a (smaller) core.
                    return possible_core
                case True:
                    # `possible_core` is not a core; keep trying.
                    continue
                case None:
                    # We ran out of conflicts while checking; core minimization
                    # is too expensive and we should stop.
                    break

        # If we did not find a smaller core, return the original one.
        return core

    def _relax_selectors(self, victim_selectors: set[int], active_selectors: list[int]) -> list[int]:
        assert victim_selectors <= set(active_selectors)
        assert victim_selectors.isdisjoint(self._relaxed_selectors)

        # Remove the victim selectors.
        self._relaxed_selectors |= victim_selectors
        next_active_selectors: list[int] = [
            s for s in active_selectors if s not in victim_selectors
        ]

        # Introduce any deferred cardinality constraints previously shadowed by
        # the ones we just relaxed.
        revealed_selectors: set[int] = set()
        for selector in victim_selectors:
            if selector in self._cardinality_metadata:
                revealed_selectors |= self._get_consequent_selectors(
                    self._cardinality_metadata[selector]
                )

        next_active_selectors += [
            s for s in revealed_selectors if s not in next_active_selectors
        ]

        return next_active_selectors

    def _transform_core(
        self, core: set[int], active_selectors: list[int], cost: int
    ) -> tuple[list[int], int]:
        # TODO: Document.
        # Needed for the reasoning behind removing the at-most-zero constraint.
        assert len(core) >= 1

        next_active_selectors = self._relax_selectors(core, active_selectors)
        next_cost = cost

        # If the core is unit, we short-circuit here since the constraints
        # below would be trivial.
        if len(core) == 1:
            # The sole selector in `core`.
            selector = next(iter(core))
            next_cost += self._selector_weights[selector]
            if self.should_harden_unit_cores:
                self._add_hard_clause([-selector])
            return next_active_selectors, next_cost

        # Initialize a set of cardinality constraints on the variables of
        # `core`. That is equivalent to the original selectors in `core` but
        # can be incrementally relaxed. The initial `at_most_zero` constraint
        # implies all the rest of the constraints, so we need not add them all
        # immediately.
        at_most_zero = self._initialize_cardinality_constraint(core)
        assert at_most_zero.prefix_len == len(core)
       
        # Track the deferred cardinality constraints if we are watching models.
        # Note that this does add clauses to the oracle, so it may change the
        # behavior.
        if self.watched_models:
            new_deferred_selectors: set[int] = set()
            for prefix_index in range(len(at_most_zero.prefixes)):
                for upper_bound in range(at_most_zero.prefix_len):
                    if prefix_index == len(at_most_zero.prefixes) - 1 and upper_bound == 0:
                        continue
                    try:
                        new_deferred_selectors.add(
                            self._create_cardinality_selector(
                                CardinalityMetadata(
                                    encoder=at_most_zero.encoder,
                                    prefixes=at_most_zero.prefixes,
                                    prefix_index=prefix_index,
                                    upper_bound=upper_bound,
                                )
                            )
                        )
                    except ValueError:
                        pass
            self._deferred_selectors |= new_deferred_selectors

        # We already know the `at_most_zero` constraint is unsatisfiable,
        # because the core `core` tells us at least one of the selectors must
        # be falsified, so we can just increment the cost and relax this
        # constraint.
        next_cost += at_most_zero.weight
        new_selectors: set[int] = self._get_consequent_selectors(at_most_zero)

        next_active_selectors += [
            s for s in new_selectors if s not in next_active_selectors
        ]

        return next_active_selectors, next_cost

    def _get_consequent_selectors(
        self, cardinality_metadata: CardinalityMetadata
    ) -> set[int]:
        """
        Return the selectors for consequents of `cardinality_metadata`.

        When a cardinality selector is deactivated, we must introduce any
        cardinality constraints that are no longer made redundant. Each
        cardinality constraint has at most two direct consequents, all of which
        we return selectors for. This approach is greedy, adding some
        cardinality constraints earlier than necessary. In particular, we may
        try to add the same constraint twice, so we prevent this by filtering
        against `self._relaxed_selectors`.

        Returns selectors for the consequents of `cardinality_metadata`. These
        should be activated in the next round of solving.
        """
        consequents: list[CardinalityMetadata] = cardinality_metadata.consequents
        selectors: list[int] = [
            self._create_cardinality_selector(c) for c in consequents
        ]
        return {s for s in selectors if s not in self._relaxed_selectors}

    def _create_cardinality_selector(
        self, cardinality_metadata: CardinalityMetadata
    ) -> int:
        """
        Create a selector that enforces constraint denoted by `cardinality_metadata`.

        Idempotently updates the underlying constraint encoding to ensure this
        constraint exists, and then records the selector and its data.

        Returns the created selector.
        """
        encoder = cardinality_metadata.encoder
        prefix_len, marginal_weight = cardinality_metadata.prefix
        upper_bound = cardinality_metadata.upper_bound

        # Ensure that the maximum bound in the encoder is at least
        # `upper_bound`, so the desired constraint is guaranteed to exist.
        encoder.increase(ubound=upper_bound, top_id=self._id_pool.top)
        self._id_pool.top = encoder.top_id
        # Add only the new clauses generated by the encoder.
        if encoder.nof_new > 0:
            for clause in encoder.cnf.clauses[-encoder.nof_new :]:
                self._add_hard_clause(clause)

        # The negation of this literal will enforce the cardinality constraint.
        constraint_literal = encoder.get_constraint(prefix_len, upper_bound)
        assert constraint_literal is not None

        selector = -constraint_literal
        if selector not in self._selector_weights:
            self._selector_weights[selector] = marginal_weight
            self._cardinality_metadata[selector] = cardinality_metadata
        else:
            # These assertions would detect if we erroneously used the same
            # selector literal for two different purposes. It is still up to
            # the caller to ensure that we don't add activate this selector on
            # more than one occasion.
            assert self._selector_weights[selector] == marginal_weight
            assert self._cardinality_metadata[selector] == cardinality_metadata

        return selector

    def _initialize_cardinality_constraint(self, core: set[int]) -> CardinalityMetadata:
        """
        Initialize a cardinality constraint relaxing the core `core`.

        Initializes a cardinality constraint encoding requiring that the
        number of selectors in `core` that are falsified is bounded above by
        some number. The upper bound can be changed, incrementally growing the
        encoding if it is increased. This method does not enforce any
        particular cardinality constraint, but rather performs the setup needed
        to do so. Particular cardinality constraints are introduced using
        `self._add_cardinality_constraint()`.

        Returns metadata representing a cardinality constraint that at most
        zero of all the selectors in `core` are falsified (but does not impose
        this constraint).
        """
        prefixes, sorted_core = self._get_prefixes(core)

        # We impose a bound on the number of selectors in `core` that can be
        # falsified. We ensure the order of variables in `sorted_core` and
        # `relaxation_literals` are the same, so that the computed `prefixes`
        # map correctly onto both.
        relaxation_literals: list[int] = [-lit for lit in sorted_core]

        # Initialize the encoding.
        encoder = ISeqCounter(
            lits=relaxation_literals, ubound=0, top_id=self._id_pool.top
        )
        self._id_pool.top = encoder.top_id
        for clause in encoder.cnf.clauses:
            self._add_hard_clause(clause)

        return CardinalityMetadata(
            encoder=encoder,
            prefixes=prefixes,
            # Use the last prefix, which is always the entire core.
            prefix_index=len(prefixes) - 1,
            upper_bound=0,
        )

    def _get_prefixes(
        self, selectors: set[int]
    ) -> tuple[list[tuple[int, int]], list[int]]:
        """
        Compute the prefixes of a set of selectors.

        Note that a literal is only considered a "selector" if it is tracked in
        `self._selector_weights`. This method does not work for arbitrary
        literals.

        Returns a pair `(prefixes, sorted_selectors)`, where `prefixes` is a
        list of tuples of the form `(prefix_len, marginal_weight)`, each
        denoting that the first `prefix_len` selectors of `sorted_selectors`
        (i.e. `sorted_selectors[:prefix_len]`) form a prefix with marginal
        weight `marginal_weight`.
        """
        if not selectors:
            # `selectors` is empty, so there are no prefixes.
            return [], []

        # Sort the selectors in order of decreasing weight.
        sorted_selectors: list[int] = sorted(
            selectors, key=lambda s: self._selector_weights[s], reverse=True
        )
        weights: list[int] = [self._selector_weights[s] for s in sorted_selectors]

        prefixes: list[tuple[int, int]] = []
        for i, weight in enumerate(weights[:-1]):
            if weight != weights[i + 1]:
                prefixes.append((i + 1, weight - weights[i + 1]))
        prefixes.append((len(weights), weights[-1]))

        return prefixes, sorted_selectors

    def _transform_am1s(
        self, active_selectors: list[int], cost: int
    ) -> tuple[list[int], int]:
        am1s, unit_cores = self._find_am1s(active_selectors)

        next_active_selectors = active_selectors[:]
        next_cost = cost

        for core_selector in unit_cores:
            next_active_selectors, next_cost = self._transform_core(
                {core_selector}, next_active_selectors, next_cost
            )
            if self.verbosity >= 1:
                print(f"c found unit core; cost: {next_cost}")

        for am1 in am1s:
            next_active_selectors, next_cost = self._transform_am1(
                am1, next_active_selectors, next_cost
            )
            if self.verbosity >= 1:
                print(f"c am1 size: {len(am1)}; cost: {next_cost}")

        return next_active_selectors, next_cost

    def _find_am1s(
        self, active_selectors: list[int]
    ) -> tuple[list[set[int]], set[int]]:
        """
        Find intrinsic at-most-one constraints among selectors in `active_selectors`.

        Identifies disjoint sets of selectors of which at most one can be true.
        We do this by building a graph whose vertices are active selectors, with
        vertices considered adjacent if their selectors are incompatible---that
        is, if at most one of the pair can be true. We find disjoint maximal
        cliques in the graph, which are then sets of selectors with the desired
        property.

        While identifying the selectors incompatible with a given one, we may
        find selectors that intrinsically false on their own, forming unit
        cores. These are excluded from the graph to be handled separately.

        Returns `(am1s, unit_cores)` where `am1s` is a list of cliques found
        and `unit_cores` is a set containing intrinsically false selectors.
        """

        # The graph we will build, represented as adjacency lists. `incompatibles[s]`
        # will give the selectors incompatible with a selector `s`.
        incompatibles: dict[int, set[int]] = collections.defaultdict(lambda: set())
        unit_cores: set[int] = set()

        # Identify the incompatibles for each active selector.
        for s in active_selectors:
            # TODO: How to choose the phase-saving parameter? I just got this
            # straight from RC2.
            is_satisfiable, consequents = self._oracle.propagate(
                assumptions=[s], phase_saving=2
            )

            if not is_satisfiable:
                # `s` forms a unit core, which we can handle separately.
                unit_cores.add(s)
                continue

            for t in consequents:
                if -t in active_selectors:
                    # `s` and `-t` are both in `active_selectors` (so we care
                    # about them) but at most one of them can be true.
                    incompatibles[s].add(-t)
                    incompatibles[-t].add(s)

        # Filter out any unit cores we found so they do not appear as keys or
        # in the incompatibility sets and bloat the constraints. We also
        # eliminate any selectors whose incompatibles are reduced to the empty
        # set by this operation.
        incompatibles = {
            k: v - unit_cores
            for k, v in incompatibles.items()
            if k not in unit_cores and len(v - unit_cores) > 0
        }

        # We find intrinsic at-most-one constraints by finding cliques in the
        # graph defined by `incompatibles`. Cliques of size less than two
        # represent trivial at-most-one constraints, so we omit them.
        am1s: list[set[int]] = [
            c for c in self._find_disjoint_maximal_cliques(incompatibles) if len(c) >= 2
        ]

        return am1s, unit_cores

    def _find_disjoint_maximal_cliques(
        self, graph: dict[int, set[int]]
    ) -> list[set[int]]:
        # TODO: Document.
        # It is important that we find *disjoint* cliques, because the am1s we ultimately want to find must be disjoint for our processing to work.

        cliques: list[set[int]] = []

        while graph:
            # Start from some vertex. We will find a maximal clique containing it.
            base_vertex = min(graph.keys(), key=lambda v: len(graph[v]))
            clique: set[int] = {base_vertex}

            # Greedily add neighbors to the clique (until it cannot be grown further).
            neighbors = sorted(graph[base_vertex], key=lambda v: len(graph[v]))
            for vertex in neighbors:
                if clique <= graph[vertex]:
                    # The clique is entirely contained in the neighborhood of
                    # `vertex`, so we can grow the clique by adding `vertex`.
                    clique.add(vertex)

            # Remove the clique from the graph so we don't repeat our work.
            # TODO: Explain why we do not need to filter out keys mapped to
            # empty sets like above (we would have added such a key to the clique).
            graph = {
                vertex: neighbors - clique
                for vertex, neighbors in graph.items()
                if vertex not in clique
            }

            cliques.append(clique)

        return cliques

    def _transform_am1(
        self, am1: set[int], active_selectors: list[int], cost: int
    ) -> tuple[list[int], int]:
        assert am1 <= set(active_selectors)
        assert len(am1) >= 2

        # Relax the original individual constraints.
        next_active_selectors = self._relax_selectors(am1, active_selectors)
        next_cost = cost

        prefixes, sorted_am1 = self._get_prefixes(am1)

        for prefix_len, marginal_weight in prefixes:
            assert prefix_len >= 1
            # We know `prefix_len - 1` at-least-i clauses in this prefix are false.
            next_cost += (prefix_len - 1) * marginal_weight

            # We add the remaining at-least-1 clause that may or may not be
            # satisfiable.
            new_selector = self._add_soft_clause(
                [s for s in sorted_am1[:prefix_len]],
                marginal_weight,
            )
            next_active_selectors.append(new_selector)

        return next_active_selectors, next_cost


def bitstr_from_model(model: list[int]) -> str:
    # TODO: Document.
    if not model:
        return ""

    var_count = max(abs(lit) for lit in model)
    bitstr = ["0"] * var_count
    for literal in model:
        if literal > 0:
            index = abs(literal) - 1
            bitstr[index] = "1"

    return "".join(bitstr)


def model_from_bitstr(bitstr: str) -> list[int]:
    # TODO: Document.
    model = []
    for index, char in enumerate(bitstr):
        var = index + 1
        if char == "0":
            model.append(-var)
        elif char == "1":
            model.append(var)
        else:
            raise Exception(
                f"invalid model bitstring: the bitstring must contain only 0s and 1s but '{char}' was found at index {index}"
            )

    return model


def parse_watched_models(var_count: int) -> list[tuple[list[int], int | None]]:
    # TODO: Document.
    with args.watched_models_csv.open(mode="r", newline="") as csv_file:
        reader = csv.DictReader(csv_file)

        watched_models = []
        for row_index, row in enumerate(reader):
            # TODO: Handle the possible exception raised by `model_from_bitstr`.
            if row["model"] is None:
                raise Exception(
                    f"invalid data row at index {row_index}: missing value for column 'model'"
                )
            model = model_from_bitstr(row["model"].strip())
            if len(model) != var_count:
                raise Exception(
                    f"invalid data row at index {row_index}: expected {var_count} variables, but model bitstring gives {len(model)}"
                )

            if row["cost"] is None:
                raise Exception(
                    f"invalid data row at index {row_index}: missing value for column 'cost'"
                )
            cost_str = row["cost"].strip()
            if cost_str:
                try:
                    cost = int(cost_str)
                except ValueError:
                    raise Exception(
                        f"invalid data row at index {row_index}: cost must be an integer, but '{cost_str}' is not"
                    )
            else:
                cost = None

            watched_models.append((model, cost))

    return watched_models


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        prog="cuscus", description="An RC2-like MaxSAT solver without cloning."
    )

    # TODO: Document the arguments with help text.
    parser.add_argument("wcnf_file", type=Path)
    parser.add_argument("-a", "--transform-am1s", action="store_true")
    parser.add_argument("-m", "--minimize", action="store_true")
    parser.add_argument("-o", "--oracle", default="cadical195")
    parser.add_argument("-u", "--harden-unit-cores", action="store_true")
    parser.add_argument("-v", "--verbose", action="count", default=0)
    parser.add_argument("-w", "--watched-models-csv", type=Path)

    args = parser.parse_args()

    # Parse the input according to the MaxSAT Evaluation WCNF 2024 standard.
    formula = WCNF.from_path(args.wcnf_file)

    if args.watched_models_csv:
        watched_models = parse_watched_models(formula.top_id)
    else:
        watched_models = []

    solver = Cuscus(
        formula,
        should_minimize=args.minimize,
        should_harden_unit_cores=args.harden_unit_cores,
        should_transform_am1s=args.transform_am1s,
        solver_name=args.oracle,
        verbosity=args.verbose,
        watched_models=watched_models,
    )

    result = solver.solve()

    # Report the solution and exit according to the MaxSAT Evaluation 2024 standard.
    if result is not None:
        cost, model = result

        print("s OPTIMUM FOUND")
        print(f"o {cost}")

        model_bitstr = bitstr_from_model(model)
        print(f"v {model_bitstr}")

        sys.exit(30)
    else:
        print("s UNSATISFIABLE")

        sys.exit(20)
