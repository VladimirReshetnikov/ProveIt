"""Run the package's actual checkers and diagnostics; no historical code scan is executed."""
import hashlib
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def run(relative):
    result = subprocess.run([sys.executable, str(ROOT / relative)], cwd=ROOT,
                            text=True, capture_output=True)
    if result.returncode:
        raise RuntimeError(relative + " failed:\n" + result.stdout + result.stderr)
    print(relative + ": passed")
    return result.stdout


def main():
    manifest = ROOT / "MANIFEST.sha256.json"
    if manifest.exists():
        for name, digest in json.loads(manifest.read_text()).items():
            path = ROOT / name
            if hashlib.sha256(path.read_bytes()).hexdigest() != digest:
                raise ValueError("Delivered payload changed: " + name)
        print("Delivered payload hashes: passed")

    run("measure.py")
    run("validation/composition/verify_composition.py")
    diagnostics = {}
    for name in ("acyclicity", "right_predecessor"):
        diagnostics[name] = json.loads(run("validation/arithmetic/" + name + "_diagnostic.py"))

    # Run the actual public modules against the saved independent named cases.
    cases = json.loads((ROOT / "validation/composition/cases.json").read_text())["cases"]
    records = []
    for filename in ("checker_compact.py", "checker_explicit.py", "readable_checker.py"):
        for optimized in (False, True):
            for case in cases:
                command = [sys.executable] + (["-O"] if optimized else []) + [str(ROOT / "code" / filename)]
                result = subprocess.run(command, input=json.dumps(case["packet"]),
                                        text=True, capture_output=True, timeout=15)
                accepted = result.returncode == 0 and result.stdout == "ACCEPT\n"
                records.append({"checker": filename, "optimized": optimized,
                                "case": case["name"], "expected": case["accept"],
                                "accepted": accepted, "pass": accepted == case["accept"]})
    if not all(record["pass"] for record in records):
        raise RuntimeError("A public-module certificate expectation failed")
    receipt = {"status": "passed", "public_module_expectations": len(records),
               "records": records, "arithmetic": diagnostics,
               "metatheorems_formalized": False}
    (ROOT / "evidence/reproduction.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print("Public-module certificate expectations:", len(records), "passed")
    print("No proof-assistant verification of the metatheorems is claimed.")


if __name__ == "__main__":
    main()
