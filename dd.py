from argparse import ArgumentParser
from pathlib import Path
import random
import subprocess
from tempfile import NamedTemporaryFile


def run_solver(solver_command: str, input_file: str) -> tuple[str, int]:
    """Run the given solver command on the input file and return the output."""
    full_command = f"{solver_command} {str(input_file)}"
    result = subprocess.run(full_command, shell=True, capture_output=True, text=True, timeout=3)
    return result.stdout, result.returncode


def parse_optimum(solver_output: str) -> int | None:
    """Extract the optimum value from the solver's output."""
    for line in reversed(solver_output.splitlines()):
        if line.startswith("o "):
            return int(line.split()[1])
    return None


def do_lines_induce_bug(
    trusted_solver_command: str, test_solver_command: str, wcnf_lines: list[str]
) -> bool:
    with NamedTemporaryFile(mode="w") as f:
        f.writelines(wcnf_lines)
        f.seek(0)

        try:
            trusted_output, trusted_returncode = run_solver(trusted_solver_command, f.name)
            test_output, test_returncode = run_solver(test_solver_command, f.name)
        except subprocess.TimeoutExpired:
            # We can't solve this instance fast enough, so just move on.
            return False

        assert trusted_returncode in [20, 30]

        if test_returncode != trusted_returncode:
            print(f"mismatched return codes: {trusted_returncode} (trusted) vs {test_returncode}")
            return True

        trusted_optimum = parse_optimum(trusted_output)
        test_optimum = parse_optimum(test_output)

        if trusted_returncode == 30:
            # Trusted solver found an optimum, so we compare with the test solver.
            if test_optimum != trusted_optimum:
                print(f"mismatched optima: {trusted_optimum} (trusted) vs {test_optimum}")
                return True

        return False


def minimize_lines(
    trusted_solver_command: str, test_solver_command: str, wcnf_lines: list[str]
) -> list[str]:
    lines = wcnf_lines[:]

    level = 0
    while lines:
        level += 1
        print(f"# starting level {level}")

        indices = list(range(len(lines)))
        random.shuffle(indices)

        for i in indices:
            print(f"exluding line {i}")
            # All the lines except the one at index `i`.
            new_lines = lines[:i] + lines[i + 1 :]
            if do_lines_induce_bug(
                trusted_solver_command, test_solver_command, new_lines
            ):
                print("bug found")
                lines = new_lines
                break
        else:
            # The for loop exitted normally without breaking, so we could not
            # reduce the lines while keeping the bug. Hence, we are done.
            print("could not reduce formula further")
            return lines

    return lines


if __name__ == "__main__":
    parser = ArgumentParser()
    parser.add_argument("trusted_solver")
    parser.add_argument("test_wcnf", type=Path)
    parser.add_argument("out_wcnf", type=Path)
    parser.add_argument("test_solver")
    args = parser.parse_args()

    with args.test_wcnf.open("r") as f:
        lines = f.readlines()

    random.seed(3)
    minimal_lines = minimize_lines(args.trusted_solver, args.test_solver, lines)
    print(f"found minimal buggy lines with length {len(minimal_lines)}")

    with args.out_wcnf.open("w") as f:
        f.writelines(minimal_lines)
