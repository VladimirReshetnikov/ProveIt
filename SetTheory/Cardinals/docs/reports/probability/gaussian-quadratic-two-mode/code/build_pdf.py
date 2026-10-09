"""Compile article.tex using an installed TeX distribution; no downloads."""
from __future__ import annotations
import json
import re
import shutil
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def run(command: list[str]) -> str:
    completed = subprocess.run(command, cwd=ROOT, text=True,
                               stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if completed.returncode:
        error_path = ROOT / 'results' / 'build_error.log'
        error_path.write_text(completed.stdout)
        raise RuntimeError(f'Command failed: {command!r}. Details: {error_path}')
    return completed.stdout


def main() -> None:
    (ROOT / 'results').mkdir(exist_ok=True)
    latex = shutil.which('pdflatex')
    bibtex = next((p for name in ('bibtex', 'bibtex.original', 'bibtex8')
                   if (p := shutil.which(name))), None)
    if latex is None or bibtex is None:
        raise SystemExit('Install pdfLaTeX and BibTeX from a TeX distribution first.')
    command = [latex, '-interaction=nonstopmode', '-halt-on-error', 'article.tex']
    run(command)
    run([bibtex, 'article'])
    run(command)
    output = run(command)
    log = (ROOT / 'article.log').read_text(errors='replace')
    unresolved = bool(re.search(r'(undefined references|Citation .* undefined|Reference .* undefined)', log))
    overfull = len(re.findall(r'Overfull \\[hv]box', log))
    match = re.search(r'Output written on article\.pdf \((\d+) pages', output)
    report = {'status': 'PASS' if not unresolved and not overfull else 'REVIEW',
              'pages': int(match.group(1)) if match else None,
              'unresolved_references': unresolved, 'overfull_boxes': overfull,
              'latex_engine': latex, 'bibtex_engine': bibtex,
              'pdf_bytes': (ROOT / 'article.pdf').stat().st_size,
              'note': 'Compilation checks are not mathematical verification; visual inspection is separate.'}
    (ROOT / 'results' / 'build_report.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))
    if unresolved or overfull:
        raise SystemExit('Review the TeX log before distributing the PDF.')


if __name__ == '__main__':
    main()
