#!/usr/bin/env python3

import argparse
from dataclasses import dataclass
from pathlib import Path
import sys
import time
from typing import Self

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
        soft_clauses = []
        hard_clauses = []

        variables = set()

        for line_number, line in enumerate(file.readlines(), start=1):
            stripped_line = line.strip()

            # Ignore empty lines.
            if not stripped_line:
                continue

            parts = stripped_line.split()

            if parts[0] == "h":
                # Hard clause.
                clause = WCNF._parse_literals(line_number, stripped_line, parts)
                variables |= {abs(l) for l in clause}
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
                variables |= {abs(l) for l in clause}
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
    def _parse_literals(line_number: int, stripped_line: str, parts: list[str]) -> list[int]:
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
            raise ValueError(f"`prefix_index` must index `prefixes`, but {self.prefix_index} is not in [0, {len(self.prefixes)})")
        # A negative upper bound is impossible and not supported by
        # `ISeqCounter`.
        if self.upper_bound < 0:
            raise ValueError(f"`upper_bound` must be non-negative, but {self.upper_bound} < 0")
        # An upper bound equal to or exceeding the number of literals being
        # bounded is trivial and not supported by `ISeqCounter`.
        if self.upper_bound >= self.prefix_len:
            raise ValueError(f"`upper_bound` must be less than `prefix_len`, but {self.upper_bound} >= {self.prefix_len}")

    @property
    def prefix(self):
        return self.prefixes[self.prefix_index]

    @property
    def prefix_len(self):
        return self.prefix[0]

    @property
    def weight(self):
        return self.prefix[1]

    @property
    def consequents(self) -> list[Self]:
        """The cardinality constraints most directly implied by this one."""
        consequents: list[CardinalityMetadata] = []

        # Add both of the consequents, skipping any that are invalid.

        try:
            consequents.append(CardinalityMetadata(
                encoder=self.encoder,
                prefixes=self.prefixes,
                prefix_index=self.prefix_index,
                upper_bound=self.upper_bound + 1
            ))
        except ValueError:
            pass

        try:
            consequents.append(CardinalityMetadata(
                encoder=self.encoder,
                prefixes=self.prefixes,
                prefix_index=self.prefix_index - 1,
                upper_bound=self.upper_bound
            ))
        except ValueError:
            pass

        return consequents


class Cuscus:
    def __init__(self, formula: WCNF, should_minimize=False, should_harden_unit_cores=False, verbosity=0):
        self.should_minimize = should_minimize
        self.should_harden_unit_cores = should_harden_unit_cores
        self.verbosity = verbosity

        self.solver_name = "cadical195"
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

        self._id_pool = IDPool(start_from=formula.top_id + 1)
        self._oracle = Solver(
                name=self.solver_name,
                bootstrap_with=formula.hard_clauses,
                use_timer=True
            )

        # Add the initial soft clauses to the problem formula.
        for clause, weight in formula.soft_clauses:
            selector = self._add_soft_clause(clause, weight)

    def __del__(self):
        # TODO: Perform any necessary cleanup.
        pass

    def _add_soft_clause(self, clause: list[int], weight: int) -> int:
        """
        Add a soft clause to the problem formula with a given weight.

        Returns the selector literal that activates the clause.
        """
        assert weight > 0 # TODO: Document that we dont except weights <= 0.
        # TODO: For unit clauses, perhaps reuse the literal as the selector.
        selector = self._id_pool.id()
        self._oracle.add_clause(clause + [-selector])
        self._selector_weights[selector] = weight
        return selector

    def _add_hard_clause(self, clause: list[int]):
        """Add a hard clause to the problem formula."""
        self._oracle.add_clause(clause)

    def solve(self) -> tuple[int, list[int]] | None:
        """
        Find the minimum cost to satisfy the problem formula.

        Returns a pair `(cost, model)`, where `model` is an assignment with
        minimal cost `cost`. If the hard clauses of the formula are
        unsatisfiable, this method returns `None` instead.
        """

        # The set of selectors whose clauses should be activated. We start by
        # activating all selectors.
        active_selectors: set[int] = set(self._selector_weights.keys())
        # The cost accrued so far due to forced clause falsifications.
        cost: int = 0

        # TODO: Detect intrinsic at-most-1 constraints.

        # TODO: Add stratification.

        oracle_call_count = 1
        total_processing_time = 0
        total_core_size = 0

        while not self._oracle.solve(assumptions=list(active_selectors)):
            start_time = time.perf_counter()

            core: list[int] = self._oracle.get_core()

            if not core:
                # The core is empty, so the hard clauses are unsatisfiable.
                return None

            reduced_core = self._reduce_core(core)

            active_selectors, cost = self._relax_core(reduced_core, active_selectors, cost)

            if len(core) == 1 and self.should_harden_unit_cores:
                self._add_hard_clause([-core[0]])

            # TODO: Add core exhaustion.

            # Ensure we haven't accidentally activated a previously relaxed selector.
            assert active_selectors.isdisjoint(self._relaxed_selectors)

            end_time = time.perf_counter()
            processing_time = end_time - start_time

            if self.verbosity >= 1:
                print(f"c oracle calls: {oracle_call_count}; cost: {cost}; core size: {len(reduced_core)}; processing time: {processing_time}")
            if self.verbosity >= 2:
                print(f"c core: {reduced_core}")
            oracle_call_count += 1
            processing_time += processing_time
            total_core_size += len(reduced_core)

        # We have relaxed the problem formula enough to make it satisfiable.

        model: list[int] = self._oracle.get_model()

        # `model` contains extraneous variables added during solving, so we
        # filter it to return a model containing only variables that appeared
        # in the original formula we were given.
        original_model: list[int] = [
                l for l in model
                if abs(l) in self._original_vars
            ]

        if self.verbosity >= 1:
            print(f"c oracle time: {self._oracle.time_accum()}")
            print(f"c total processing time: {total_processing_time}")
            print(f"c oracle calls: {oracle_call_count}")
            print(f"c mean core size: {total_core_size / float(oracle_call_count - 1)}")

        return cost, original_model
    
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

        sorted_core = sorted(core, key=lambda s: self._selector_weights[s])

        # Limit the number of conflicts allowed in the following
        # `solve_limited()` calls.
        self._oracle.conf_budget(self.minimization_max_conflicts)

        for i in range(len(sorted_core)):
            # Exclude a single selector from the original core.
            possible_core = sorted_core[:i] + sorted_core[i + 1:]

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


    def _relax_core(self, core: list[int], active_selectors: set[int], cost: int) -> tuple[set[int], int]:
        # TODO: Document.
        # Needed for the reasoning behind removing the at-most-zero constraint.
        assert len(core) >= 1

        # Relax the core literals.
        core_set = set(core)
        self._relaxed_selectors |= core_set
        next_active_selectors = active_selectors - core_set
        next_cost = cost

        # Introduce any deferred cardinality constraints previously shadowed by
        # the ones we just deactivated.
        for selector in core:
            if selector in self._cardinality_metadata:
                next_active_selectors |= self._get_consequent_selectors(
                        self._cardinality_metadata[selector]
                    )

        # If the core is unit, we short-circuit here since the constraints
        # below would be trivial.
        if len(core) == 1:
            next_cost += self._selector_weights[core[0]]
            return next_active_selectors, next_cost

        # Initialize a set of cardinality constraints on the variables of
        # `core`. That is equivalent to the original selectors in `core` but
        # can be incrementally relaxed. The initial `at_most_zero` constraint
        # implies all the rest of the constraints, so we need not add them all
        # immediately.
        at_most_zero = self._initialize_cardinality_constraint(core)

        # We already know the `at_most_zero` constraint is unsatisfiable,
        # because the core `core` tells us at least one of the selectors must
        # be falsified, so we can just increment the cost and relax this
        # constraint.
        next_cost += at_most_zero.weight
        next_active_selectors |= self._get_consequent_selectors(at_most_zero)
        
        return next_active_selectors, next_cost

    def _get_consequent_selectors(self, cardinality_metadata: CardinalityMetadata) -> set[int]:
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
        consequents = cardinality_metadata.consequents
        selectors = [self._create_cardinality_selector(c) for c in consequents]
        return {s for s in selectors if s not in self._relaxed_selectors}

    def _create_cardinality_selector(self, cardinality_metadata: CardinalityMetadata) -> int:
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
            for clause in encoder.cnf.clauses[-encoder.nof_new:]:
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

    def _initialize_cardinality_constraint(self, core: list[int]) -> CardinalityMetadata:
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
        relaxation_literals = [-l for l in sorted_core]
    
        # Initialize the encoding.
        encoder = ISeqCounter(lits=relaxation_literals, ubound=0, top_id=self._id_pool.top)
        self._id_pool.top = encoder.top_id
        for clause in encoder.cnf.clauses:
            self._add_hard_clause(clause)

        return CardinalityMetadata(
                encoder=encoder,
                prefixes=prefixes,
                # Use the last prefix, which is always the entire core.
                prefix_index=len(prefixes) - 1,
                upper_bound=0
            )

    def _get_prefixes(self, selectors: list[int]) -> tuple[list[tuple[int, int]], list[int]]: 
        """
        Compute the prefixes of a list of selectors.

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
        sorted_selectors = sorted(selectors, key=lambda s: self._selector_weights[s], reverse=True)
        weights = [self._selector_weights[s] for s in sorted_selectors]
   
        prefixes: list[tuple[int, int]] = []
        for i, weight in enumerate(weights[:-1]):
            if weight != weights[i + 1]:
                prefixes.append((i + 1, weight - weights[i + 1]))
        prefixes.append((len(weights), weights[-1]))

        return prefixes, sorted_selectors



if __name__ == "__main__":
    parser = argparse.ArgumentParser(
            prog="cuscus",
            description="An RC2-like MaxSAT solver without cloning."
        )
    
    parser.add_argument("wcnf_file", type=Path)
    parser.add_argument("-m", "--minimize", action="store_true")
    parser.add_argument("-u", "--harden-unit-cores", action="store_true")
    parser.add_argument("-v", "--verbose", action="count", default=0)

    args = parser.parse_args()

    # Parse the input according to the MaxSAT Evaluation WCNF 2024 standard.
    formula = WCNF.from_path(args.wcnf_file)

    solver = Cuscus(formula, should_minimize=args.minimize, should_harden_unit_cores=args.harden_unit_cores, verbosity=args.verbose)
    result = solver.solve()

    # Report the solution and exit according to the MaxSAT Evaluation 2024 standard.
    if result is not None:
        cost, model = result

        print("s OPTIMUM FOUND")
        print(f"o {cost}")

        model_str = "".join(str(int(l > 0)) for l in sorted(model, key=lambda l: abs(l)))
        print(f"v {model_str}")

        sys.exit(30)
    else:
        print("s UNSATISFIABLE")

        sys.exit(20)

