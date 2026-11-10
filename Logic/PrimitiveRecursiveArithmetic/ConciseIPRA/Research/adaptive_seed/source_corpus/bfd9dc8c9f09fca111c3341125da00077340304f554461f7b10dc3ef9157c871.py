"""Recheck symbolic certificates and the frozen whole-program comparison."""
from pathlib import Path
import hashlib
import importlib.util
import json
import platform
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def main():
    provenance = json.loads((ROOT / "evidence/reference_provenance.json").read_text())
    for item in provenance:
        actual = hashlib.sha256((ROOT / item["file"]).read_bytes()).hexdigest()
        if actual != item["sha256"]:
            raise SystemExit("Reference hash mismatch: " + item["file"])
    subprocess.run([sys.executable, "code/validate.py"], cwd=ROOT, check=True)
    spec = importlib.util.spec_from_file_location("measure", ROOT / "reference/source_measure.py")
    measure = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(measure)
    expected = json.loads((ROOT / "evidence/comparison_metrics.json").read_text())
    records = []
    keys = ("normalized_tokens", "ast_nodes", "normalized_bytes", "sha256")
    for row in expected["programs"]:
        actual = measure.metrics(ROOT / row["file"])
        if platform.python_version() == expected["python"]:
            for key in keys:
                if actual[key] != row[key]:
                    raise SystemExit("Metric mismatch: " + row["file"] + ": " + key)
        records.append({"file": row["file"], **{k: actual[k] for k in keys}})
    result = {"python": platform.python_version(), "references_verified": len(provenance),
              "measured_programs": len(records), "programs": records,
              "coordinate_minima": {k: min(r[k] for r in records) for k in keys[:3]},
              "certificate_validation": json.loads((ROOT / "certificates/validation.json").read_text())}
    (ROOT / "evidence/reproduction.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"status": "PASS", "python": result["python"],
                      "complete_programs": len(records),
                      "coordinate_minima": result["coordinate_minima"]}, indent=2))


if __name__ == "__main__":
    main()
