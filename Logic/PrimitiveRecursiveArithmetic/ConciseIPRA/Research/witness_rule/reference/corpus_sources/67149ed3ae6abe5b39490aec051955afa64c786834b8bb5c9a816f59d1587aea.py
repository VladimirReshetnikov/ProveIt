"""Reproduce the finite evidence; universal metatheorems are written proofs."""
from pathlib import Path
import hashlib
import importlib.util
import json
import sys

ROOT = Path(__file__).resolve().parent
sys.dont_write_bytecode = True


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, ROOT / path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def main():
    manifest = json.loads((ROOT / "MANIFEST.json").read_text())
    checked = 0
    for record in manifest["files"]:
        path = ROOT / record["path"]
        raw = path.read_bytes()
        if len(raw) != record["bytes"] or hashlib.sha256(raw).hexdigest() != record["sha256"]:
            raise AssertionError("Payload identity mismatch: " + record["path"])
        checked += 1
    measurement = load("ipra_measure", "measure.py").collect()
    expected = json.loads((ROOT / "evidence/measurements.json").read_text())
    if measurement != expected:
        raise AssertionError("Measurements differ; compare Python/zlib versions and run measure.py")
    results = load("ipra_verify", "tests/verify.py").verify()
    model = load("ipra_ec_model", "code/eventually_constant.py").examples()
    if model != json.loads((ROOT / "evidence/model_examples.json").read_text()):
        raise AssertionError("Sequence-model examples changed")
    receipt = {"payload_files_verified": checked, "measurements_match": True,
               "finite_checker_suite": results, "exact_model_examples_match": True,
               "metatheorem_status": "Written mathematical proofs; no proof-assistant verification"}
    print(json.dumps(receipt, indent=2))


if __name__ == "__main__":
    main()
