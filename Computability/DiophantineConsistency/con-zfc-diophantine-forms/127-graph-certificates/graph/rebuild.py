#!/usr/bin/env python3
"""Rebuild all graph profiles offline and compare every exact JSON artifact."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--receipt", type=Path)
    args = parser.parse_args()
    here = Path(__file__).resolve().parent
    profiles = json.loads((here/"PROFILES.json").read_text())
    pins = json.loads((here/"SOURCE_PINS.json").read_text())
    results = []
    for profile in profiles:
        source = here/profile["source"]
        digest = hashlib.sha256(source.read_bytes()).hexdigest()
        if digest != pins[source.name]["sha256"]:
            raise ValueError("Source hash mismatch: "+source.name)
        with tempfile.TemporaryDirectory(prefix="conzfc-graph-") as directory:
            temporary = Path(directory)
            command = [sys.executable, "-B", str(here/"build.py"), "--source", str(source),
                       "--hubs", str(profile["hubs"]), "--out", str(temporary/"base")]
            if profile["square_aliases"]:
                command.append("--square-aliases")
            subprocess.run(command, check=True, capture_output=True, text=True)
            subprocess.run([sys.executable, "-B", str(here/"compress_aliases.py"),
                            "--input", str(temporary/"base"), "--output", str(temporary/"result")],
                           check=True, capture_output=True, text=True)
            checks = {}
            for filename in ("polynomial.json", "certificate.json", "metrics.json", "COMPRESSION.json"):
                expected = (here/profile["name"]/filename).read_bytes()
                actual = (temporary/"result"/filename).read_bytes()
                if actual != expected:
                    raise ValueError("Rebuild differs: "+profile["name"]+"/"+filename)
                checks[filename] = hashlib.sha256(actual).hexdigest()
            results.append({"profile": profile["name"], "source_sha256": digest,
                            "byte_identical": checks})
    receipt = {"status": "pass", "profiles": results,
               "scope": "Deterministic offline rebuild; no claim of consistency or formal-kernel verification."}
    output = json.dumps(receipt, indent=2, sort_keys=True)+"\n"
    if args.receipt:
        args.receipt.write_text(output)
    print(output, end="")


if __name__ == "__main__":
    main()
