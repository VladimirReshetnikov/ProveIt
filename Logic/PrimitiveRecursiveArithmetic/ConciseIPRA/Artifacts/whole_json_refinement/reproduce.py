"""Reproduce the two profiles, selected controls, and rejected parity experiment."""
import json
from pathlib import Path
import subprocess
import sys

from verify import measure

ROOT = Path(__file__).resolve().parent


def main():
    subprocess.run([sys.executable, str(ROOT / "verify.py")],
                   cwd=ROOT, check=True)
    subprocess.run([sys.executable, str(ROOT / "negative/verify_parity.py")],
                   cwd=ROOT / "negative", check=True)
    expected = {
        "reference/whole_json_tokens249.py": (249, 278, 607),
        "reference/whole_json_ast269.py": (255, 269, 605),
        "reference/whole_json_bytes473.py": (272, 308, 473),
        "code/checker_tokens248.py": (248, 277, 615),
        "code/checker_ast268.py": (254, 268, 613),
    }
    rows = {name: measure(ROOT / name) for name in expected}
    exact_runtime = sys.version_info[:3] == (3, 12, 14)
    result = {
        "python_version": sys.version.split()[0],
        "exact_reference_runtime": exact_runtime,
        "old_whole_json_envelope": [249, 269, 473],
        "new_whole_json_envelope": [248, 268, 473],
        "envelope_attained_by_different_programs": True,
        "new_axiomatization_claimed": False,
        "measurements": rows,
    }
    (ROOT / "evidence/comparison.json").write_text(
        json.dumps(result, indent=2) + "\n")
    if exact_runtime:
        for name, vector in expected.items():
            actual = tuple(rows[name][key] for key in ("tokens", "ast_nodes", "bytes"))
            if actual != vector:
                raise SystemExit(f"Metric mismatch for {name}: {actual} != {vector}")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
