"""Verify a build receipt against its output files and this companion source."""
import argparse
import hashlib
import json
from pathlib import Path


def verify(manifest_path):
    source = Path(__file__).resolve().parent
    output = manifest_path.resolve().parent
    data = json.loads(manifest_path.read_text())
    if data.get("schema") != "cylindrical-kings-companion-build-v1" or data.get("status") != "PASS":
        raise RuntimeError("Unsupported or unsuccessful build manifest")
    for section,root in (("inputs_sha256",source),("outputs_sha256",output)):
        for name,expected in data[section].items():
            path = root / name
            if Path(name).is_absolute() or root not in path.resolve().parents:
                raise RuntimeError("Manifest path leaves its expected directory: "+name)
            actual = hashlib.sha256(path.read_bytes()).hexdigest()
            if actual != expected:
                raise RuntimeError("SHA-256 mismatch: "+name)
    return len(data["inputs_sha256"]),len(data["outputs_sha256"])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("manifest",type=Path)
    args = parser.parse_args()
    inputs,outputs = verify(args.manifest)
    print(f"PASS: verified {inputs} inputs and {outputs} result files")


if __name__ == "__main__":
    main()
