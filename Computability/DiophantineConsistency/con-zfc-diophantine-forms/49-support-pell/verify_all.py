#!/usr/bin/env python3
"""Run the archive's finite checks; this does not decide Con(ZFC).

No network access, theorem-prover installation, or external repository is
needed. Python 3 and NumPy are sufficient. The inherited unbounded proofs
and new ordinary mathematical proofs are separate from these checks.
"""
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import platform
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise ValueError(message)


def load_module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, "Cannot load " + str(path))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def check_generated_objects():
    """Check that the supplied norm/offset JSONs are the audited builders' objects."""
    eleven = load_module("archive_eleven_builder", ROOT / "eleven/build_eleven.py")
    checked = []
    for carrier in ("full", "short"):
        for presentation in ("product", "system", "shifted_system", "sos"):
            expected = eleven.build(presentation, carrier)
            path = ROOT / "eleven/generated" / (expected["name"] + ".json")
            require(json.loads(path.read_text()) == expected,
                    "Generated eleven-variable object differs: " + path.name)
            require((path.parent / expected["coefficient_binding"]).resolve()
                    == (ROOT / "coefficients/COEFFICIENT_BINDING.json").resolve(),
                    "Eleven-variable binding is not relative to its JSON")
            checked.append(str(path.relative_to(ROOT)))
    short = load_module("archive_short_builder", ROOT / "short/build_offset44.py")
    expected = short.build(json.loads(short.SOURCE.read_text()))
    path = ROOT / "short/offset44.json"
    require(json.loads(path.read_text()) == expected, "Generated offset object differs")
    require((path.parent / expected["coefficient_binding"]["file"]).resolve()
            == (ROOT / "coefficients/COEFFICIENT_BINDING.json").resolve(),
            "Offset binding is not relative to its JSON")
    checked.append(str(path.relative_to(ROOT)))
    return checked


def check_inherited_bytes():
    """Verify the source-copy pins without interpreting their old numerical claims."""
    source_map = json.loads((ROOT / "upstream/ADDITIONAL_SOURCE_PINS.json").read_text())
    for entry in source_map["files"]:
        data = (ROOT / entry["archive_path"]).read_bytes()
        require(hashlib.sha256(data).hexdigest() == entry["sha256"], "Source SHA-256 differs")
        blob = b"blob " + str(len(data)).encode() + b"\0" + data
        require(hashlib.sha1(blob).hexdigest() == entry["git_blob_sha1"], "Source Git blob differs")
    packing = json.loads((ROOT / "SOURCES.json").read_text())
    for entry in packing["inert_upstream_sources"]:
        require(hashlib.sha256((ROOT / entry["path"]).read_bytes()).hexdigest()
                == entry["sha256"], "Packing source copy differs")
    return len(source_map["files"]) + len(packing["inert_upstream_sources"])


def main():
    import numpy
    os.environ["PYTHONDONTWRITEBYTECODE"] = "1"
    sys.dont_write_bytecode = True
    records = []
    receipt = {
        "status": "IN_PROGRESS",
        "scope": "Finite literal, symbolic, circuit and degree audits; not a consistency decision or an end-to-end formal proof.",
        "source_commit": "124c07c0b77a9e20e84676514d8b1ff78536ea3f",
        "python": platform.python_version(),
        "numpy": numpy.__version__,
        "generated_objects_compared_exactly": check_generated_objects(),
        "inherited_source_copies_hashed": check_inherited_bytes(),
        "checks": records,
    }
    commands = [
        ["audits/verify_coefficients.py", "coefficients", "--receipt", "audits/COEFFICIENT_RECONSTRUCTION.json"],
        ["verify.py"],
        ["code/audit_full_circuit.py"],
        ["eleven/verify_eleven.py"],
        ["short/audit_offset44.py"],
    ]
    logs = ROOT / "audits/logs"
    logs.mkdir(exist_ok=True)
    for optimized in (False, True):
        mode = "optimized" if optimized else "normal"
        for arguments in commands:
            command = [sys.executable] + (["-O"] if optimized else []) + arguments
            key = arguments[0].replace("/", "_").removesuffix(".py") + "_" + mode
            result = subprocess.run(command, cwd=ROOT, text=True,
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            (logs / (key + ".txt")).write_text(result.stdout)
            record = {"script": arguments[0], "mode": mode,
                      "returncode": result.returncode,
                      "log": "audits/logs/" + key + ".txt"}
            records.append(record)
            print(("PASS" if result.returncode == 0 else "FAIL"), mode, arguments[0], flush=True)
            if result.returncode != 0:
                receipt["status"] = "FAIL"
                (ROOT / "audits/ALL_CHECKS.json").write_text(json.dumps(receipt, indent=2) + "\n")
                print(result.stdout, file=sys.stderr)
                raise SystemExit(result.returncode)
    receipt["status"] = "PASS"
    (ROOT / "audits/ALL_CHECKS.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print("PASS: all ten audit runs; exact generated-object and inherited-byte comparisons.")


if __name__ == "__main__":
    main()
