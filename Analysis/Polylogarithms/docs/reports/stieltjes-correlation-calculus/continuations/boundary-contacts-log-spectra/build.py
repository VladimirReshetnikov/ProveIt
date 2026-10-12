#!/usr/bin/env python3
"""Flatten the modular article, check references, and compile the PDF."""
from __future__ import annotations
import argparse
import collections
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
STEM = "Boundary_Contacts_and_Logarithmic_Spectral_Integrals"


def flatten(path: Path, stack: tuple[Path, ...] = ()) -> str:
    path = path.resolve()
    if path in stack:
        raise RuntimeError(f"Cyclic input: {path}")
    if not path.is_relative_to(ROOT):
        raise RuntimeError("All inputs must be inside this package.")
    text = path.read_text(encoding="utf-8")

    def include(match: re.Match) -> str:
        child = ROOT / match.group(1)
        if not child.suffix:
            child = child.with_suffix(".tex")
        return ("\n% BEGIN " + child.relative_to(ROOT).as_posix() + "\n"
                + flatten(child, stack + (path,))
                + "\n% END " + child.relative_to(ROOT).as_posix() + "\n")

    return re.sub(r"(?m)^\s*\\input\{([^}]+)\}\s*$", include, text)


def inspect_source(text: str) -> dict:
    labels = re.findall(r"\\label\{([^}]+)\}", text)
    duplicates = [label for label, n in collections.Counter(labels).items() if n > 1]
    refs = re.findall(r"\\(?:eqref|ref)\{([^}]+)\}", text)
    bib = set(re.findall(r"\\bibitem\{([^}]+)\}", text))
    cites = []
    for match in re.finditer(r"\\cite(?:\[[^\]]*\])?\{([^}]+)\}", text):
        cites.extend(v.strip() for v in match.group(1).split(","))
    missing_refs = sorted(set(refs) - set(labels))
    missing_cites = sorted(set(cites) - bib)
    result = dict(labels=len(labels), duplicate_labels=duplicates,
                  undefined_source_references=missing_refs,
                  undefined_bibliography_keys=missing_cites,
                  bibliography_entries=len(bib))
    if duplicates or missing_refs or missing_cites:
        raise RuntimeError(json.dumps(result, indent=2))
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--no-compile", action="store_true")
    parser.add_argument("--passes", type=int, default=3)
    args = parser.parse_args()
    source = flatten(ROOT / "article.tex")
    report = inspect_source(source)
    standalone = ROOT / (STEM + ".tex")
    standalone.write_text(source, encoding="utf-8")
    report["standalone_source"] = standalone.name
    report["standalone_sha256"] = hashlib.sha256(standalone.read_bytes()).hexdigest()
    (ROOT / "data").mkdir(exist_ok=True)
    if args.no_compile:
        (ROOT / "data" / "source_structure.json").write_text(
            json.dumps(report, indent=2) + "\n", encoding="utf-8")
        print(json.dumps(report, indent=2))
        return
    if not shutil.which("pdflatex"):
        raise RuntimeError("pdflatex is required; see README.md for TeX packages.")
    build = ROOT / "build"
    build.mkdir(exist_ok=True)
    for iteration in range(args.passes):
        process = subprocess.run(
            ["pdflatex", "-interaction=nonstopmode", "-halt-on-error",
             "-file-line-error", "-output-directory", str(build), standalone.name],
            cwd=ROOT, capture_output=True, text=True)
        (build / f"pass-{iteration + 1}.txt").write_text(
            process.stdout + process.stderr, encoding="utf-8")
        if process.returncode:
            print("\n".join(process.stdout.splitlines()[-45:]), file=sys.stderr)
            raise RuntimeError(f"pdflatex pass {iteration + 1} failed")
    log = (build / (STEM + ".log")).read_text(encoding="utf-8", errors="replace")
    report["overfull_boxes"] = re.findall(r"Overfull \\[hv]box[^\n]*", log)
    report["underfull_boxes"] = re.findall(r"Underfull \\[hv]box[^\n]*", log)
    report["latex_warnings"] = re.findall(r"LaTeX Warning:[^\n]*", log)
    report["undefined_references_in_final_log"] = (
        "undefined references" in log
        or bool(re.search(r"(?:Reference|Citation) .* undefined", log)))
    if report["undefined_references_in_final_log"]:
        raise RuntimeError("Final LaTeX log still contains undefined references.")
    pdf = ROOT / (STEM + ".pdf")
    shutil.copyfile(build / pdf.name, pdf)
    report["pdf"] = pdf.name
    report["pdf_sha256"] = hashlib.sha256(pdf.read_bytes()).hexdigest()
    if shutil.which("pdfinfo"):
        info = subprocess.run(["pdfinfo", str(pdf)], capture_output=True,
                              text=True, check=True).stdout
        pages = re.search(r"(?m)^Pages:\s+(\d+)", info)
        report["pages"] = int(pages.group(1)) if pages else None
    report["status"] = "compiled; visual review recorded separately"
    (ROOT / "data" / "pdf_build_report.json").write_text(
        json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
