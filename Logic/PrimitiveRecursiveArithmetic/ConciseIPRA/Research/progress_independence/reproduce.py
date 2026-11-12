"""Run the packaged finite evidence, without network access or external data."""
from pathlib import Path
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def main():
    subprocess.run([sys.executable, str(ROOT / "checker/reproduce.py")],
                   cwd=ROOT / "checker", check=True)
    outputs = []
    for script, receipt in [
        ("check_finite_clocks.py", "finite_clock_checks.json"),
        ("check_initial_model.py", "initial_model_checks.json"),
    ]:
        run = subprocess.run([sys.executable, str(ROOT / "mathematics" / script)],
                             cwd=ROOT, check=True, capture_output=True, text=True)
        data = json.loads(run.stdout)
        (ROOT / "mathematics" / receipt).write_text(json.dumps(data, indent=2) + "\n")
        outputs.append({"script": script, "receipt": receipt, "result": data})
    (ROOT / "evidence").mkdir(exist_ok=True)
    (ROOT / "evidence/mathematical_examples.json").write_text(
        json.dumps(outputs, indent=2) + "\n")
    print("Packaged finite checks passed. They are not formal proofs of the infinite model.")


if __name__ == "__main__":
    main()
