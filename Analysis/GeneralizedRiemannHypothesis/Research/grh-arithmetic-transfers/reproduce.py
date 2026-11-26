"""Reproduce and compare the finite proof transcripts shipped with the paper."""
import difflib
import os
from pathlib import Path
import subprocess
import sys
from tempfile import TemporaryDirectory

CHECKS = Path(__file__).resolve().parent / "checks"

def compare(command, reference):
    actual = subprocess.check_output(command, text=True)
    expected = (CHECKS / reference).read_text()
    if expected != actual:
        report = difflib.unified_diff(expected.splitlines(True), actual.splitlines(True),
                                      fromfile=reference, tofile="new run")
        raise SystemExit("".join(report))
    print(f"verified {reference}", flush=True)

def main():
    transcripts = {
        "prime_plus_cube_multiple.py": "prime_plus_cube_multiple.out",
        "isogeny_sieve.py": "isogeny_sieve.out",
        "simultaneous_witness.py": "simultaneous_witness.out",
        "verify_large.py": "large.txt",
        "alternating.py": "alternating.txt",
        "rigidity.py": "rigidity.json",
    }
    for program, output in transcripts.items():
        compare([sys.executable, "-B", str(CHECKS / program)], output)
    with TemporaryDirectory() as temp:
        for program in ("cubic_tail", "least_primes", "progression_windows"):
            executable = Path(temp) / program
            subprocess.run([os.environ.get("CXX", "g++"), "-std=c++17", "-O3",
                            str(CHECKS / (program + ".cpp")), "-o", str(executable)], check=True)
            compare([str(executable)], program + ".out")

if __name__ == "__main__":
    main()
