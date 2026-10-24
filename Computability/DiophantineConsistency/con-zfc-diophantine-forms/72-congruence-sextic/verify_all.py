#!/usr/bin/env python3
"""Offline finite verification of all three endpoints. Standard library only."""
import hashlib
import json
import os
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def need(condition, message):
    if not condition:
        raise ValueError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    source_manifest = json.loads((ROOT / "SOURCE_MANIFEST.json").read_text())
    for entry in source_manifest["files"]:
        raw = (ROOT / entry["local_path"]).read_bytes()
        need(hashlib.sha256(raw).hexdigest() == entry["sha256"],
             "Inherited source SHA256 mismatch: " + entry["local_path"])
        blob = hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest()
        need(blob == entry["git_blob"],
             "Inherited Git blob mismatch: " + entry["local_path"])
    binding13 = json.loads((ROOT / "positive13/ACTIVE_BINDING.json").read_text())
    binding14 = json.loads((ROOT / "positive14/ACTIVE_BINDING.json").read_text())
    need(digest(ROOT / "positive14" / binding14["polynomial_path"]) ==
         binding14["polynomial_sha256"], "Lifted polynomial binding mismatch")
    need(digest(ROOT / "positive14" / binding14["parent_polynomial_path"]) ==
         binding14["parent_polynomial_sha256"], "Lifted parent binding mismatch")
    need(binding14["derived_fixed_leaves"] == binding13["derived_fixed_leaves"],
         "Lifted fixed leaves differ from parent")
    for name, entry in binding14["ports"].items():
        parent_entry = binding13["ports"][name]
        need((ROOT / "positive14" / entry["path"]).resolve() ==
             (ROOT / "positive13" / parent_entry["path"]).resolve(),
             "Lifted coefficient refers to another file: " + name)
        for key in ["encoding", "bits", "raw_bytes", "sha256_raw", "sha256_gzip"]:
            need(entry[key] == parent_entry[key],
                 "Lifted coefficient binding differs: " + name + "/" + key)
    commands = [
        ("positive13/build13.py", "positive13/p13_degree28.json"),
        ("positive13/check13.py", None),
        ("positive13/independent/check_independent.py", None),
        ("positive13/verify_coefficients.py", None),
        ("positive14/build14.py", "positive14/p14_degree24.json"),
        ("positive14/check14.py", None),
        ("positive14/audit14_independent.py", None),
        ("integer34/build_sextic34.py", "integer34/sextic34.json"),
        ("integer34/verify_sextic34.py", None),
        ("integer34/audit_sextic34.py", None),
    ]
    runs = []
    environment = dict(os.environ, PYTHONDONTWRITEBYTECODE="1")
    for script, preserved in commands:
        previous = digest(ROOT / preserved) if preserved else None
        args = [sys.executable]
        if sys.flags.optimize:
            args.append("-O")
        args.append(str(ROOT / script))
        result = subprocess.run(args, cwd=ROOT, env=environment,
                                text=True, capture_output=True)
        if result.returncode:
            sys.stderr.write(result.stdout + result.stderr)
            raise RuntimeError("Verification failed: " + script)
        if preserved:
            need(digest(ROOT / preserved) == previous,
                 "Builder changed delivered polynomial: " + script)
        run = {"script": script, "status": "PASS"}
        if preserved:
            run["delivered_polynomial_unchanged"] = True
        runs.append(run)
        print("PASS " + script, flush=True)
    p = json.loads((ROOT / "positive13/CHECK13.json").read_text())
    s = json.loads((ROOT / "integer34/SEXTIC34_INDEPENDENT_AUDIT.json").read_text())
    lift = json.loads((ROOT / "positive14/CHECK14.json").read_text())
    need((p["unknowns"], p["exact_total_degree"], p["operations"]) ==
         (13, 28, 98), "Positive endpoint differs")
    need((s["child_variables"], s["exact_degree"], s["residuals"]) ==
         (34, 6, 19), "Integer endpoint differs")
    need((lift["unknowns"], lift["exact_total_degree"], lift["operations"]) ==
         (14, 24, 101), "Lifted endpoint differs")
    receipt = {
        "status": "PASS",
        "python_optimization": sys.flags.optimize,
        "source_commit": source_manifest["commit"],
        "inherited_files_authenticated": len(source_manifest["files"]),
        "checks": runs,
        "positive13": {"domain": "strictly positive integers", "unknowns": 13,
                       "degree": 28, "operations": 98, "residuals": 4},
        "integer34": {"domain": "all integers", "unknowns": 34,
                      "degree": 6, "residuals": 19},
        "positive14": {"domain": "strictly positive integers", "unknowns": 14,
                       "degree": 24, "operations": 101, "residuals": 5},
        "scope": "Finite exact algebra, data, coefficient regeneration and reproducibility only. "
                 "Ordinary unbounded proofs and inherited semantic calibration are separate.",
    }
    name = "VERIFICATION_OPTIMIZED.json" if sys.flags.optimize else "VERIFICATION.json"
    (ROOT / name).write_text(json.dumps(receipt, indent=2) + "\n")
    print("PASS all finite checks; " + name)


if __name__ == "__main__":
    main()
