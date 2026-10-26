#!/usr/bin/env python3
"""Run the independent coefficient and certificate audits for this release."""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parent

def require(condition, message):
    if not condition:
        raise ValueError(message)

def run_json(arguments):
    command = [sys.executable, "-B"]
    if sys.flags.optimize:
        command.append("-O")
    completed = subprocess.run(command + [str(a) for a in arguments],
                               cwd=ROOT, text=True, capture_output=True)
    if completed.returncode:
        raise RuntimeError(completed.stdout + completed.stderr)
    return json.loads(completed.stdout)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--receipt", type=Path)
    args = parser.parse_args()
    comp = ROOT / "composition"
    prior = comp / "157-linear-crt"
    stages = comp / "composed"
    result = {"status": "passed", "python_optimized": bool(sys.flags.optimize),
              "repository_commit": "953fb4d82d4229f4efc5f9db4cc2bf38ae329bb4"}
    result["provenance"] = run_json([ROOT / "checks/check_provenance.py"])
    result["source157_pipeline"] = run_json([
        prior / "code/check_pipeline.py",
        prior / "inherited/factorial_free/direct/factorial_free_affine/raw_source.json",
        prior / "source"])
    result["composition"] = run_json([comp / "check_composition.py"])
    result["independent_binding"] = run_json([
        ROOT / "checks/check_composition_binding.py",
        stages / "basis235/equation.json", stages / "pooled223/equation.json",
        stages / "pooled223/pool_certificate.json"])
    a = (stages / "differences223/equation.json").read_bytes()
    b = (ROOT / "algebra/parent223.json").read_bytes()
    require(a == b, "composition-to-algebra boundary must match byte for byte")
    result["boundary_sha256"] = hashlib.sha256(a).hexdigest()
    result["algebra"] = run_json([ROOT / "algebra/audit_algebra.py"])
    result["printed_equation"] = run_json([ROOT / "checks/check_report.py"])
    final = {
        218: "95c0db6befd4ad98e6749ba18580f3dd775b1faaec36d270f8b839911754d6b1",
        216: "a91308bd0c82182ea15080763cb23cb4fa0aa45a812eabb7a6cbcd21c0b95a06",
    }
    result["final_equation_sha256"] = {}
    for n, wanted in final.items():
        value = hashlib.sha256((ROOT / "algebra" / f"equation{n}.json").read_bytes()).hexdigest()
        require(value == wanted, "frozen equation identity " + str(n))
        result["final_equation_sha256"][str(n)] = value
    result["scope"] = (
        "Exact literal polynomial, integer-map, signed-frame binding and printed-equation checks; "
        "unbounded arithmetic proof and inherited C222/ZF/ZFC logical calibration remain mathematical "
        "dependencies. No consistency assumption, zero search or new full proof-assistant build.")
    text = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.receipt:
        args.receipt.write_text(text)
    print(text, end="")

if __name__ == "__main__":
    main()
