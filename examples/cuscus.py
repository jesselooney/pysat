#!/usr/bin/env python3

import argparse
from pathlib import Path
import sys

from pysat.formula import IDPool, WCNFPlus
from pysat.solvers import Solver


class Cuscus:
    def __init__(self, formula: WCNFPlus):
        self._solver_name = "cadical195"

        # The set of variables that appear in the original formula we were
        # given. Used to filter the model returned.
        self._original_vars: set[int] = set(range(1, formula.nv + 1))
        # A mapping from selector literals to the weight of the clause each
        # one enables.
        self._selector_weights: dict[int, int] = {}

        self._id_pool = IDPool(start_from=formula.nv + 1)
        self._oracle = Solver(
                name=self._solver_name,
                bootstrap_with=formula.hard
            )

        # Add the initial soft clauses to the problem formula.
        for clause, weight in zip(formula.soft, formula.wght):
            selector = self._add_soft_clause(clause, weight)

    def __del__(self):
        # TODO: Perform any necessary cleanup.
        pass

    def _add_soft_clause(self, clause: list[int], weight: int) -> int:
        """
        Add a soft clause to the problem formula with a given weight.

        Returns the selector literal that activates the clause.
        """
        assert weight >= 0
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
        # activating all selectors with positive weight; zero-weighted clauses
        # can effectively be ignored as they incur no cost to falsify.
        active_selectors: set[int] = set(
                selector for (selector, weight) in self._selector_weights.items()
                if weight > 0
            )
        # The cost accrued so far due to forced clause falsifications.
        cost: int = 0

        # TODO: Detect intrinsic at-most-1 constraints.

        # TODO: Add stratification.

        # TODO: Add core exhaustion.

        while not self._oracle.solve(assumptions=list(active_selectors)):
            core: list[int] = self._oracle.get_core()

            if not core:
                # The core is empty, so the hard clauses are unsatisfiable.
                return None

            reduced_core: list[int] = self._reduce_core(core)

            active_selectors, cost = self._relax_core(reduced_core, active_selectors, cost)

            # TODO: Add some debug output tracking the progress.

        # We have relaxed the problem formula enough to make it satisfiable.

        model: list[int] = self._oracle.get_model()

        # `model` contains extraneous variables added during solving, so we
        # filter it to return a model containing only variables that appeared
        # in the original formula we were given.
        original_model: list[int] = [
                literal for literal in model
                if abs(literal) in self._original_vars
            ]

        return cost, original_model
    
    def _reduce_core(self, core: list[int]) -> list[int]:
        # TODO: Implement and document.
        # Should call either minimization or trimming or combination.
        pass

    def _relax_core(self, core: list[int], active_selectors: list[int], cost: int) -> tuple[list[int], int]:
        # TODO: Implement and document.
        pass


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
            prog="cuscus",
            description="An RC2-like MaxSAT solver without cloning."
        )
    
    parser.add_argument("wcnf_file", type=Path)

    args = parser.parse_args()

    # TODO: Use our own WCNF parser.
    # Parse the input according to the MaxSAT Evaluation WCNF 2024 standard.
    formula = WCNFPlus(from_file=args.wcnf_file)
    assert len(formula.atms) == 0

    solver = Cuscus(formula)
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

