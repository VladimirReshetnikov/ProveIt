#!/usr/bin/env python3
"""Verify both literal endpoints and optionally rebuild them without mutation."""
import argparse
import hashlib
import json
import subprocess
import sys
import tempfile
from pathlib import Path

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent
import check
import check_independent
import render

FILES = ["source.json", "source_change.json", "projected.json",
         "projection_certificate.json", "equation.json", "expanded_polynomial.json",
         "translation_certificate.json", "METRICS.json", "residuals.txt",
         "residuals.tex", "variables.tsv"]


def verify(rebuild=False):
    pins = json.loads((ROOT / "SOURCE_PINS.json").read_text())
    for item in pins["retained_original_files"]:
        path = ROOT / item["local"]
        if hashlib.sha256(path.read_bytes()).hexdigest() != item["sha256"]:
            raise ValueError("inherited source checksum: " + item["local"])
    profiles = [("symmetric_caps", 16), ("dimension259", 20)]
    results = {}
    for name, _ in profiles:
        directory = ROOT / "equations" / name
        results[name] = check.check(directory)
        results[name]["transcription"] = render.render(directory, check=True)
    results["independent_main_audit"] = check_independent.audit(ROOT)
    if rebuild:
        with tempfile.TemporaryDirectory(prefix="diophantine-direct-rebuild-") as d:
            for name, cap in profiles:
                target = Path(d) / name
                subprocess.run([sys.executable, "-B", str(ROOT / "build.py"),
                                "--mode", "selected_linear", "--orient", "2,3,4,5,6,8,9,11,12",
                                "--grouped-remainders", "--cap", str(cap), "--output", str(target)],
                               check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
                render.render(target)
                for filename in FILES:
                    if (target / filename).read_bytes() != (ROOT / "equations" / name / filename).read_bytes():
                        raise ValueError("nonidentical deterministic rebuild: " + name + "/" + filename)
                results[name]["byte_identical_rebuild_files"] = FILES
    return {"status": "PASS", "optimized_python": not __debug__,
            "inherited_files_authenticated": len(pins["retained_original_files"]),
            "results": results}


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--rebuild", action="store_true")
    ap.add_argument("--receipt", type=Path)
    args = ap.parse_args()
    result = verify(args.rebuild)
    text = json.dumps(result, sort_keys=True, indent=2) + "\n"
    if args.receipt:
        args.receipt.write_text(text)
    print(text)
