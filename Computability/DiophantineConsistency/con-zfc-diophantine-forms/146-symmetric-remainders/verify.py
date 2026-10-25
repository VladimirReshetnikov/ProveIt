#!/usr/bin/env python3
"""Offline mathematical and transcription verification for this research packet.

Uses Python's standard library. It does not test consistency or search for roots.
No delivered file is changed unless an explicit --receipt path is supplied.
"""
import argparse
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def require(test, message):
    if not test:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def coefficient_appendix():
    source = (ROOT / "compact/proof_sources/indexed_constants.tex").read_text()
    start = source.index(r"\textbf{The four fixed integers.}")
    end = source.index(r"\normalfont\fontsize{7.7}{8.2}\selectfont", start)
    text = source[start:end]
    text = text.replace("K={}", "K_0={}")
    text = text.replace("intermediate in K cancels", "intermediate in $K_0$ cancels")
    text = text.replace(r"\rg", r"\fixedrange").replace(r"\fl", r"\fixedfloor")
    text = text.replace("is\n{\\fontsize{7.7}{8.2}", "is\\par\n{\\fontsize{7.7}{8.2}")
    text = text.replace(r"\fontsize{7.7}{8.2}", r"\fontsize{9}{11}")
    header = ("\\begingroup\n"
              "\\newcommand{\\fixedrange}[2]{\\{#1,\\ldots,#2\\}}\n"
              "\\newcommand{\\fixedfloor}[1]{\\left\\lfloor#1\\right\\rfloor}\n")
    return header + text + "\n\\endgroup\n"


def check_text():
    main = ROOT / "direct/equations/symmetric_caps"
    require((ROOT / "report_inputs/residuals.tex").read_bytes() ==
            (main / "residuals.tex").read_bytes(), "Printed residual appendix differs")
    require((ROOT / "report_inputs/coefficients.tex").read_text() == coefficient_appendix(),
            "Printed coefficient recipe differs from the authenticated source")
    metrics = json.loads((main / "METRICS.json").read_text())
    tex = (ROOT / "report.tex").read_text()
    for macro, key in [("nvars", "variables"), ("nrows", "residuals"),
                       ("nterms", "monomials"), ("nheight", "coefficient_height")]:
        pattern = r"\\newcommand\{\\" + macro + r"\}\{(\d+)\}"
        match = re.search(pattern, tex)
        require(match and int(match.group(1)) == metrics[key], "Manuscript metric " + macro)
    for match in re.finditer(r"\\path\{([^}]+)\}", tex):
        require((ROOT / match.group(1)).is_file(), "Nonexistent manuscript file path")
    return {"residuals": metrics["residuals"],
            "equation_sha256": sha(main / "equation.json"),
            "expanded_sha256": sha(main / "expanded_polynomial.json"),
            "coefficient_recipe": "Exact extraction with fixed K renamed to K0",
            "manuscript_metrics_match": True}


def run_json(command):
    process = subprocess.run(command, cwd=ROOT, capture_output=True, text=True)
    require(process.returncode == 0,
            "Component failed: " + " ".join(command) + "\n" + process.stderr[-6000:]
            + process.stdout[-6000:])
    return json.loads(process.stdout)


def verify_manifest():
    manifest = ROOT / "MANIFEST.json"
    if not manifest.exists():
        return {"status": "not yet sealed"}
    data = json.loads(manifest.read_text())
    for item in data["files"]:
        path = ROOT / item["path"]
        require(path.is_file() and sha(path) == item["sha256"],
                "Release hash mismatch: " + item["path"])
    return {"status": "PASS", "files": len(data["files"])}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rebuild", action="store_true",
                        help="Rebuild both quartics and all three circuits in temporary locations")
    parser.add_argument("--receipt", type=Path)
    parser.add_argument("--manifest-only", action="store_true")
    args = parser.parse_args()
    result = {"manifest": verify_manifest()}
    if not args.manifest_only:
        result["manuscript"] = check_text()
        options = [sys.executable, "-B"] + (["-O"] if not __debug__ else [])
        direct = options + [str(ROOT / "direct/verify.py")]
        if args.rebuild:
            direct.append("--rebuild")
        result["direct"] = run_json(direct)
        result["compact"] = run_json(options + [str(ROOT / "compact/verify.py")])
        if args.rebuild:
            completed = subprocess.run(options + [str(ROOT / "compact/build.py"), "--check"],
                                       cwd=ROOT, capture_output=True, text=True)
            require(completed.returncode == 0,
                    "Compact reconstruction failed\n" + completed.stderr + completed.stdout)
            result["compact_byte_identical_rebuild"] = True
    result["status"] = "PASS"
    result["optimized_python"] = not __debug__
    result["scope"] = ("Exact finite source, restoration, coefficient, circuit and transcription checks. "
                       "The unbounded equivalence uses the ordinary proofs and inherited calibration.")
    text = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.receipt:
        args.receipt.parent.mkdir(parents=True, exist_ok=True)
        args.receipt.write_text(text)
    print(text, end="")


if __name__ == "__main__":
    main()
