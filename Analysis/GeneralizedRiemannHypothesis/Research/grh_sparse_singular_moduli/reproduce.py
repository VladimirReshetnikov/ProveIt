"""Run all finite mathematical checks using Python and a C++17 compiler."""
from pathlib import Path
from subprocess import PIPE, STDOUT, run
from tempfile import TemporaryDirectory
import os
import sys

ROOT = Path(__file__).resolve().parent


def python_check(script, expected=None, combined=False):
    result = run([sys.executable, str(ROOT/script)], cwd=ROOT,
                 stdout=PIPE, stderr=STDOUT if combined else None, text=True)
    if result.returncode:
        print(result.stdout, file=sys.stderr, flush=True)
        result.check_returncode()
    if expected is not None:
        assert result.stdout == (ROOT/expected).read_text(), script
    print(result.stdout, end="", flush=True)


def main():
    if not __debug__ or os.environ.get("PYTHONOPTIMIZE"):
        raise SystemExit("Enable Python assertions before running the certificates.")
    python_check("cm/verify_class_polynomials.py")
    python_check("cm/verify_disks.py")
    python_check("cm/verify_all_cubics.py")
    python_check("cm/verify_all_quartics.py")
    python_check("cm/verify_quintic_list.py")
    python_check("checks/verify_last_quintic.py", "checks/last_quintic.txt")
    python_check("checks/independent_quintic.py")
    python_check("checks/global_five.py", "checks/global_five.txt")
    python_check("checks/verify_five_small.py")
    python_check("checks/verify_five_sieves.py", "checks/five_sieves.txt")
    python_check("checks/fast_sieve/verify.py", "checks/fast_sieve/result.txt", combined=True)
    python_check("checks/check_exact_family.py")
    python_check("checks/check_prime_conductor_density.py", "checks/check_prime_conductor_density.txt")
    python_check("checks/check_frobenius_weights.py", "checks/check_frobenius_weights.txt")
    python_check("previous/verify_four_term.py", "previous/four_term.out")
    python_check("previous/verify_4075.py", "previous/4075.out")
    assert (ROOT/"previous/cm_small_unresolved.txt").read_bytes() == (ROOT/"cm/discriminants.txt").read_bytes()
    run(["sh", str(ROOT/"previous/run_cm_small.sh")], check=True)
    with TemporaryDirectory() as temp:
        exe = Path(temp)/"range_sieve"
        run([os.environ.get("CXX", "c++"), "-std=c++17", "-O3", str(ROOT/"previous/cm_range.cpp"),
             "-o", str(exe)], check=True)
        result = run([str(exe)], check=True, capture_output=True)
        assert result.stdout == (ROOT/"previous/cm_range.out").read_bytes()
    print("Both earlier range sieves and all current arithmetic certificates passed.")


if __name__ == "__main__":
    main()
