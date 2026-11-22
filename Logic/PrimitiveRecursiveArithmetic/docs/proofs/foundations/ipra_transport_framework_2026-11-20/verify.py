"""Run exact reference checks, optionally followed by all Lean files."""
import argparse
from pathlib import Path
import subprocess
import sys

BASE = Path(__file__).resolve().parent

def run(command, cwd=None, env=None):
    label = Path(command[-1]).name
    print("\n" + label, flush=True)
    result = subprocess.run(command, cwd=cwd, env=env, capture_output=True, text=True)
    output = result.stdout + result.stderr
    if output:
        print(output.rstrip(), flush=True)
    if result.returncode or "sorryAx" in output or "declaration uses 'sorry'" in output:
        raise SystemExit(f"verification failed for {label}")
    print("PASS", flush=True)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--proveit", type=Path,
                        help="configured and built ProveIt checkout using Lean 4.32.0")
    args = parser.parse_args()
    for script in sorted((BASE / "checks").glob("*.py")):
        run([sys.executable, str(script)])
    if args.proveit is None:
        return
    repo = args.proveit.resolve()
    print("\nLean provider",flush=True)
    for cmd in (["git","rev-parse","HEAD"], ["lake","env","lean","--version"]):
        subprocess.run(cmd, cwd=repo, check=True)
    # Use Lake's full configured environment, including shared library paths.
    subprocess.run(["lake","env",sys.executable,str(BASE/"verify_lean.py"),str(BASE/"lean")],
                   cwd=repo, check=True)

if __name__ == "__main__":
    main()
