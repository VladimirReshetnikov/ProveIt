"""Replay the finite checks and compare the two detailed enumerations to their transcripts."""
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent / "checks"
SCRIPTS = (
    "verify_class_polynomials", "global_sieve", "degree_131",
    "suzuki_constants", "suzuki_density", "suzuki_fixed_q", "prime_race_triangle",
)

if __name__ == "__main__":
    for script in SCRIPTS:
        result = subprocess.run([sys.executable, "-B", str(ROOT / (script + ".py"))],
                                capture_output=True, check=True, text=True)
        expected = ROOT / (script + ".txt")
        if expected.is_file() and result.stdout != expected.read_text():
            raise ValueError(f"Output differs from {expected.name}")
        print(script)
        print(result.stdout.rstrip() if script != "global_sieve" else
              "\n".join(result.stdout.splitlines()[-7:]))
