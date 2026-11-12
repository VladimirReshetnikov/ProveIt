"""Run the portable verification packages. No network or third-party modules."""
import argparse
import hashlib
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--skip-manifest", action="store_true")
    args = parser.parse_args()
    manifest = ROOT / "SHA256SUMS"
    if manifest.exists() and not args.skip_manifest:
        for row in manifest.read_text().splitlines():
            expected, name = row.split("  ", 1)
            if hashlib.sha256((ROOT / name).read_bytes()).hexdigest() != expected:
                raise SystemExit("Manifest mismatch: " + name)
    for script in ["goal_checker/reproduce.py", "forward/verify.py"]:
        subprocess.run([sys.executable, str(ROOT / script)], cwd=ROOT, check=True)
    print("All packaged verification tasks passed.")


if __name__ == "__main__":
    main()
