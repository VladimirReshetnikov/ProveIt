"""Kernel-check all companion sources with Lean 4.32.0; no external packages."""
import os
from pathlib import Path
import subprocess
import tempfile


def main():
    root = Path(__file__).resolve().parent
    lean_binary = os.environ.get("LEAN", "lean")
    version = subprocess.check_output([lean_binary, "--version"], text=True).strip()
    print(version, flush=True)
    with tempfile.TemporaryDirectory() as directory:
        env = {**os.environ, "LEAN_PATH": directory}
        for name in ("OrdinalCore", "Limits", "Threshold", "Power", "Finite"):
            output = Path(directory) / (name + ".olean")
            subprocess.run([lean_binary, "-o", str(output), name + ".lean"],
                           cwd=root, env=env, check=True)
            print("Checked", name + ".lean", flush=True)


if __name__ == "__main__":
    main()
