#!/usr/bin/env python3
"""Require explicit rejection of malformed or damaged package variants."""
import json
from pathlib import Path
import shutil
import sys
import tempfile
sys.dont_write_bytecode = True
from integrity import IntegrityError, validate

ROOT = Path(__file__).resolve().parent

def run():
    validate(ROOT)
    outcomes = []
    cases = ["changed_content", "missing_file", "extra_file", "extra_directory",
             "file_symlink", "directory_symlink", "manifest_symlink",
             "duplicate_path", "traversal_path", "absolute_path", "backslash_path",
             "duplicate_json_key", "missing_field", "extra_field", "boolean_size",
             "bad_hash", "unsorted_paths"]
    with tempfile.TemporaryDirectory(prefix="report114-integrity-tests-") as temp:
        for case in cases:
            destination = Path(temp) / case
            shutil.copytree(ROOT, destination)
            manifest_path = destination / "manifest.json"
            data = json.loads(manifest_path.read_text())
            victim = destination / data["files"][0]["path"]
            if case == "changed_content":
                content = victim.read_bytes()
                victim.write_bytes(bytes([content[0] ^ 1]) + content[1:])
            elif case == "missing_file":
                victim.unlink()
            elif case == "extra_file":
                (destination / "unexpected.txt").write_text("extra")
            elif case == "extra_directory":
                (destination / "unexpected").mkdir()
            elif case == "file_symlink":
                victim.unlink()
                victim.symlink_to(ROOT / data["files"][0]["path"])
            elif case == "directory_symlink":
                (destination / "unexpected").symlink_to(ROOT, target_is_directory=True)
            elif case == "manifest_symlink":
                manifest_path.unlink()
                manifest_path.symlink_to(ROOT / "manifest.json")
            elif case == "duplicate_json_key":
                manifest_path.write_text('{"format":"report114-sha256-v1","format":"report114-sha256-v1","files":[]}')
            else:
                if case == "duplicate_path":
                    data["files"].append(dict(data["files"][0]))
                elif case == "traversal_path":
                    data["files"][0]["path"] = "../outside.txt"
                elif case == "absolute_path":
                    data["files"][0]["path"] = "/tmp/outside.txt"
                elif case == "backslash_path":
                    data["files"][0]["path"] = "checks\\outside.txt"
                elif case == "missing_field":
                    del data["files"][0]["sha256"]
                elif case == "extra_field":
                    data["files"][0]["optional"] = True
                elif case == "boolean_size":
                    data["files"][0]["bytes"] = True
                elif case == "bad_hash":
                    data["files"][0]["sha256"] = "g" * 64
                elif case == "unsorted_paths":
                    data["files"].reverse()
                manifest_path.write_text(json.dumps(data))
            try:
                validate(destination)
            except IntegrityError as exc:
                outcomes.append({"case": case, "status": "REJECTED", "diagnostic": str(exc)})
            else:
                raise RuntimeError("Integrity mutant accepted: " + case)
    return {"status": "PASS", "rejected": len(outcomes), "cases": outcomes}

if __name__ == "__main__":
    print(json.dumps(run(), indent=2, sort_keys=True))
