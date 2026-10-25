#!/usr/bin/env python3
"""Verify the sealed release, cross-component bindings, and exact finite algebra."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check_manifest():
    manifest = ROOT / "MANIFEST_SHA256.json"
    require(manifest.is_file(), "The sealed release manifest is missing")
    data = json.loads(manifest.read_text())
    require(data["algorithm"] == "sha256", "Unexpected manifest algorithm")
    for name, expected in data["files"].items():
        path = ROOT / name
        require(path.resolve().is_relative_to(ROOT.resolve()), "Unsafe manifest path")
        require(path.is_file() and sha(path) == expected, "Changed or missing file: " + name)
    return len(data["files"])


def cross_bindings():
    source = ROOT / "direct_quartics/equations/integer248/equation.json"
    higher = ROOT / "higher_degree/source/equation248.json"
    require(source.read_bytes() == higher.read_bytes(), "Higher-degree source does not equal principal quartic")
    require(sha(source) == "c51ebc12534db042bd1c7bf7c59f84602f51625e2d952dffa82fa054b5d92192", "Frozen source identity")
    copies = [
        ("report/compact.tex", "compact/section.tex"),
        ("report/direct.tex", "direct_quartics/direct_section.tex"),
        ("report/elimination.tex", "higher_degree/section.tex"),
        ("report/pivots.tex", "higher_degree/pivot_appendix.tex"),
        ("report/residuals248.tex", "direct_quartics/readable/integer248/residuals.tex"),
    ]
    for a, b in copies:
        require((ROOT / a).read_bytes() == (ROOT / b).read_bytes(), "Printed section differs: " + a)
    tex = (ROOT / "report/residuals248.tex").read_text()
    ids = [int(n) for n in re.findall(r"R_\{(\d+)\} &=", tex)]
    require(ids == list(range(182)), "Printed residual list is incomplete or reordered")
    parent = (ROOT / "compact/parent/proof_sources/indexed_constants.tex").read_text()
    start = parent.index(r"\textbf{The four fixed integers.}")
    end = parent.index(r"\endgroup", start) + len(r"\endgroup")
    recipe = parent[start:end].replace("is\n{\\fontsize{7.7}{8.2}", "is\\par\n{\\fontsize{7.7}{8.2}")
    recipe = recipe.replace(r"\fontsize{7.7}{8.2}", r"\fontsize{10}{12}")
    require(recipe in (ROOT / "report/constants.tex").read_text(), "Printed fixed coefficient recipe differs")
    # Import only the document assembler, never an algebra producer.
    import build_report
    require((ROOT / "report/report_standalone.tex").read_text() == build_report.standalone_text(), "Single-file TeX edition differs")
    return {"source248_sha256": sha(source), "printed_residuals": len(ids), "printed_pivot_pairs": 913}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rebuild", action="store_true", help="Also regenerate all equation files byte for byte")
    parser.add_argument("--receipt", type=Path, help="Write a receipt outside the sealed release")
    args = parser.parse_args()
    if args.receipt:
        require(not args.receipt.resolve().is_relative_to(ROOT.resolve()), "Keep new receipts outside the sealed release")
    count = check_manifest()
    bindings = cross_bindings()
    command_prefix = [sys.executable, "-B"] + (["-O"] if sys.flags.optimize else [])
    env = dict(os.environ)
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    if sys.flags.optimize:
        env["PYTHONOPTIMIZE"] = str(sys.flags.optimize)
    results = {}
    def run(name, path, extra=()):
        print("Checking " + name + "...", flush=True)
        command = command_prefix + [str(ROOT / path)] + list(extra)
        process = subprocess.run(command, cwd=ROOT, env=env, capture_output=True, text=True)
        require(process.returncode == 0, name + " failed:\n" + process.stdout[-4000:] + process.stderr[-8000:])
        try:
            results[name] = json.loads(process.stdout)
        except json.JSONDecodeError:
            results[name] = {"status": "PASS", "stdout": process.stdout.strip()}
    with tempfile.TemporaryDirectory(prefix="conzfc-release-check-") as td:
        temporary = Path(td)
        run("compact exact algebra", "compact/verify.py")
        run("actual fixed coefficient reconstruction", "compact/parent/rebuild_coefficients.py")
        run("three direct quartics and inherited parent", "direct_quartics/verify.py", ["--rebuild"] if args.rebuild else [])
        run("eight higher-degree circuits and complete octic", "higher_degree/verify.py")
        run("complete printed pivot tables", "higher_degree/render_appendix.py", ["--check"])
        if args.rebuild:
            run("compact byte-exact rebuild", "compact/build.py", ["--check"])
            run("higher-degree byte-exact rebuild", "higher_degree/build.py", ["--check"])
            run("printed residual reconstruction", "direct_quartics/render.py", ["--output", str(temporary / "readable")])
            for profile in (248, 246, 245):
                name = "integer" + str(profile)
                expected = ROOT / "direct_quartics/readable" / name / "residuals.tex"
                actual = temporary / "readable" / name / "residuals.tex"
                require(actual.read_bytes() == expected.read_bytes(), "Readable residual rebuild: " + name)
    receipt = {"status": "PASS", "sealed_files_checked": count, "python_optimized": bool(sys.flags.optimize),
               "rebuild_requested": args.rebuild, "bindings": bindings, "checks": results,
               "scope": "Finite exact algebra and release bindings. Unbounded arithmetic and inherited refutation calibration are ordinary mathematical proofs, not decided by this program."}
    if args.receipt:
        args.receipt.write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({"status": "PASS", "sealed_files_checked": count, "checks_completed": len(results),
                      "optimized": bool(sys.flags.optimize), "rebuild": args.rebuild, **bindings}, indent=2))


if __name__ == "__main__":
    main()
