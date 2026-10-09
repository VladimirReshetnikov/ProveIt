"""Build the article and optionally regenerate its computational evidence."""

from pathlib import Path
import argparse
import subprocess
import sys


ROOT = Path(__file__).resolve().parent


def run(*command, cwd=ROOT):
    print("Running:", " ".join(map(str, command)), flush=True)
    subprocess.run(list(map(str, command)), cwd=cwd, check=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--figures", action="store_true")
    parser.add_argument("--validate", action="store_true")
    parser.add_argument("--full-validation", action="store_true",
                        help="Regenerate all numerical data, plots and tests; takes minutes")
    args = parser.parse_args()
    if args.full_validation:
        run(sys.executable, "code/generate_inverse.py", "--order", "6")
        run(sys.executable, "code/validate_algorithm.py")
        run(sys.executable, "code/bose_certified.py", "--validation",
            "data/certified_validation.json")
        run(sys.executable, "code/validate_temperature.py")
        run(sys.executable, "code/validate_independent.py")
        run(sys.executable, "code/lattice_validate.py")
    if args.validate or args.full_validation:
        run(sys.executable, "-m", "pytest", "-q")
    if args.figures or args.full_validation:
        run(sys.executable, "code/make_figures.py")
    run("latexmk", "-xelatex", "-interaction=nonstopmode", "-halt-on-error",
        "marginal_bose_crossover.tex", cwd=ROOT / "article")


if __name__ == "__main__":
    main()
