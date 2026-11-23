"""Run the eight exact computation suites and, with --lean, the four standalone Lean files."""
import argparse
import os
from pathlib import Path
import subprocess
import sys


ROOT = Path(__file__).resolve().parent
PYTHON_SUITES = (
    "check_colorings.py", "jones_states.py", "alexander_braids.py",
    "check_borromean.py", "descending_certificate.py", "polygon_caps.py",
    "polygon_geometry.py", "check_finite_type.py",
)
LEAN_SUITES = ("EquationalFox.lean", "DiagramCore.lean", "Fox.lean", "SurfaceCore.lean")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", action="store_true", help="also run Lean 4.32.0 from PATH or LEAN_BIN")
    args = parser.parse_args()
    for name in PYTHON_SUITES:
        print(name, flush=True)
        subprocess.run([sys.executable, str(ROOT / "code" / name)], check=True)
    if args.lean:
        lean = os.environ.get("LEAN_BIN", "lean")
        subprocess.run([lean, "--version"], check=True)
        for name in LEAN_SUITES:
            print(name, flush=True)
            subprocess.run([lean, str(ROOT / "lean" / name)], check=True)


if __name__ == "__main__":
    main()
