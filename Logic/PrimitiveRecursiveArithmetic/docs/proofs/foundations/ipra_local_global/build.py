#!/usr/bin/env python3
"""Rebuild the standalone Lean checks, exact examples, and PDF."""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
EVIDENCE = ROOT / "evidence"
BUILD = ROOT / "build"


def run(args: list[str], *, cwd: Path, output: Path, env=None) -> str:
    p = subprocess.run(args, cwd=cwd, env=env, text=True, stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT)
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(p.stdout)
    if p.returncode:
        print(p.stdout, file=sys.stderr)
        raise SystemExit(f"Build failed ({p.returncode}); see {output}")
    return p.stdout


def lean_build() -> None:
    lean = os.environ.get("LEAN_BIN") or shutil.which("lean")
    if not lean:
        raise SystemExit("Set LEAN_BIN to the Lean 4.32.0 executable.")
    lean = str(Path(lean).resolve())
    version = subprocess.check_output([lean, "--version"], text=True).strip()
    if "version 4.32.0," not in version:
        raise SystemExit(f"Expected Lean 4.32.0; found {version}")
    outdir = BUILD / "lean"
    outdir.mkdir(parents=True, exist_ok=True)
    env = os.environ.copy()
    env["LEAN_PATH"] = str(outdir)
    modules = ["ObjectKernel", "ObjectIteration", "ObjectExample",
               "NegativeSyntax", "ODETargets", "SplitTargets", "Audit"]
    log = [version, ""]
    for name in modules:
        output = run([lean, "-o", str(outdir / f"{name}.olean"), f"{name}.lean"],
                     cwd=ROOT / "lean", output=outdir / f"{name}.log", env=env)
        log += [f"COMPILED {name}.lean", output.rstrip()]
    (EVIDENCE / "lean_build.txt").write_text("\n".join(log) + "\n")
    audit = (outdir / "Audit.log").read_text()
    (EVIDENCE / "lean_audit.txt").write_text(audit)
    if "sorryAx" in audit or "Classical.choice" in audit:
        raise SystemExit("Unexpected audited dependency; inspect lean_audit.txt")
    (EVIDENCE / "lean_status.json").write_text(json.dumps({
        "status": "passed", "compiler": version, "modules_compiled": modules,
        "not_compiled": ["RepositoryAdapter.lean"],
        "proved_layer": ["object primitive-recursion rule",
                         "negative-translation syntax and all source axiom translations"],
        "unproved_goal_modules": ["ODETargets.lean", "SplitTargets.lean"],
        "negative_translation_remaining": ["object equality stability adapter",
                                           "formula stability",
                                           "complete derivation translator",
                                           "retained formulas and bounded selector"],
        "scope": "No completed deep application proofs are claimed."
    }, indent=2) + "\n")
    print(f"Lean: compiled {len(modules)} modules; audited proof dependencies.")


def exact_checks() -> None:
    for stem, output in [("split_branches", "split_checks"),
                         ("ode_checks", "ode_checks")]:
        run([sys.executable, str(ROOT / "code" / f"{stem}.py"),
             "--output", str(EVIDENCE / f"{output}.json")],
            cwd=ROOT, output=BUILD / f"{stem}.stdout.txt")
        data = json.loads((EVIDENCE / f"{output}.json").read_text())
        if data["status"] != "passed":
            raise SystemExit(f"{stem}: non-passing result")
        print(f"Exact arithmetic: {stem} passed.")


def paper_build() -> None:
    run(["bash", "build_pdf.sh"], cwd=ROOT, output=BUILD / "pdf_build_stdout.txt")
    log = (BUILD / "report.log").read_text()
    diagnostics = [line for line in log.splitlines()
                   if any(token in line for token in
                          ["Overfull", "Underfull", "undefined", "LaTeX Warning"])]
    (EVIDENCE / "latex_diagnostics.txt").write_text(
        "\n".join(diagnostics) + ("\n" if diagnostics else "No layout/reference warnings.\n"))
    print("PDF: built ipra_local_global.pdf; visual QA remains separate.")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("part", choices=["all", "lean", "checks", "paper"],
                        default="all", nargs="?")
    args = parser.parse_args()
    EVIDENCE.mkdir(exist_ok=True)
    BUILD.mkdir(exist_ok=True)
    if args.part in ("all", "lean"):
        lean_build()
    if args.part in ("all", "checks"):
        exact_checks()
    if args.part in ("all", "paper"):
        paper_build()


if __name__ == "__main__":
    main()
