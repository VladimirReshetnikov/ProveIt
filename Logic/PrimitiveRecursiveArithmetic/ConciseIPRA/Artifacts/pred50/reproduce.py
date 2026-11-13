"""Reproduce arithmetic checks, source metrics, and matched checker tests."""

import argparse
import ast
import hashlib
import io
import json
import platform
from pathlib import Path
import shutil
import subprocess
import sys
import tokenize

ROOT = Path(__file__).resolve().parent
SKIP = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
        tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}
EXPECTED = {
    "reference/checkers/tokens244.py": [244, 272, 608],
    "reference/checkers/ast267.py": [249, 267, 606],
    "reference/checkers/bytes478.py": [271, 305, 478],
    "code/checker/control608.py": [244, 272, 608],
    "code/checker/checker607.py": [244, 273, 607],
}


def measure(name):
    raw = (ROOT / name).read_bytes()
    tree = ast.parse(raw)
    normalized = (ast.unparse(tree) + "\n").encode()
    compile(normalized, name, "exec")
    values = [sum(t.type not in SKIP for t in tokenize.generate_tokens(
        io.StringIO(normalized.decode()).readline)),
        sum(1 for _ in ast.walk(tree)), len(normalized)]
    if values != EXPECTED[name]:
        raise ValueError((name, values, EXPECTED[name], platform.python_version()))
    return {"path": name, "metrics": values,
            "sha256": hashlib.sha256(raw).hexdigest(),
            "normalized_sha256": hashlib.sha256(normalized).hexdigest()}


def run_script(name):
    result = subprocess.run([sys.executable, "-B", str(ROOT / name)],
                            cwd=ROOT, capture_output=True, text=True, timeout=90)
    if result.returncode:
        sys.stdout.write(result.stdout)
        sys.stderr.write(result.stderr)
        raise SystemExit(result.returncode)
    return {"script": name, "status": "passed"}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--pdf", action="store_true")
    args = parser.parse_args()
    metrics = [measure(name) for name in EXPECTED]
    scripts = [run_script("code/arithmetic/pred50.py"),
               run_script("code/arithmetic/universal_sizes.py"),
               run_script("code/checker/verify.py")]
    checker = json.loads((ROOT / "code/checker/verification.json").read_text())
    report = {"python": platform.python_version(), "measurement_reference": "3.12.14",
              "status": "all checks passed", "metrics": metrics, "checks": scripts,
              "new_axiomatization_below_checker_frontier": False,
              "proof_status": "Written mathematical and operational proofs; finite diagnostics; no new proof-assistant formalization"}
    (ROOT / "evidence/reproduction.json").write_text(json.dumps(report, indent=2) + "\n")
    shutil.copyfile(ROOT / "code/checker/verification.json", ROOT / "evidence/checker_verification.json")
    if args.pdf:
        build = ROOT / ".build"
        build.mkdir(exist_ok=True)
        command = ["pdflatex", "-interaction=nonstopmode", "-halt-on-error",
                   "-output-directory=" + str(build), "ipra_pred50.tex"]
        for _ in range(2):
            result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True, timeout=90)
            if result.returncode:
                sys.stdout.write(result.stdout)
                sys.stderr.write(result.stderr)
                raise SystemExit(result.returncode)
        shutil.copyfile(build / "ipra_pred50.pdf", ROOT / "ipra_pred50.pdf")
        report["pdf"] = "compiled twice"
        (ROOT / "evidence/reproduction.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
