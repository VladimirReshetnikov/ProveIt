"""Assemble the self-contained TeX source and compile its PDF.

Run from any directory with Python 3 and pdflatex available.
Checker measurements and tests are reproduced by tests/reproduce.py.
"""
from pathlib import Path
import json
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent


def metrics_tex():
    data = json.loads((ROOT / 'evidence/checker_metrics.json').read_text())['metrics']
    rows = []
    for name, label in [('native_checker.py', 'Native, eight rules'),
                        ('witness_checker.py', 'Witness-selected, seven rules'),
                        ('diagonal_checker.py', 'Diagonal-guard, seven rules')]:
        m = data[name]
        rows.append(f"{label} & {m['normalized_bytes']:,} & {m['tokens']:,} & "
                    f"{m['ast_nodes']:,} & {m['gzip9_bytes']:,} " + r'\\')
    return '\n'.join([r'\begin{center}\small',
                      r'\begin{tabular}{@{}lrrrr@{}}', r'\toprule',
                      r'Complete checker & Bytes & Tokens & AST nodes & gzip-9\\',
                      r'\midrule', *rows, r'\bottomrule',
                      r'\end{tabular}\end{center}'])


def inherited_tex():
    directory = ROOT / 'reference/inherited'
    names = ['inherited_choice_basis.tex', 'inherited_ordinary_bridge.tex',
             'scalar_predecessor.tex', 'equality_reflection.tex',
             'primitive_recursion.tex']
    texts = [directory.joinpath(name).read_text() for name in names]
    texts[0] = texts[0].replace(
        'The old paired introduction retains both the zero instance and an',
        'This inherited comparison starts from a paired introduction retaining both the zero instance and an')
    texts[0] = texts[0].replace(
        'The new inference interface retains one ordinary assumption',
        'The inherited Choice-DI interface retains one ordinary assumption')
    return '\n\n'.join(texts)


def main():
    template = (ROOT / 'report_template.tex').read_text()
    replacements = {
        '@@CORE@@': (ROOT / 'core_theorem.tex').read_text(),
        '@@METRICS@@': metrics_tex(),
        '@@VALIDATION@@': (ROOT / 'evidence/validation_summary.tex').read_text(),
        '@@INHERITED@@': inherited_tex(),
        '@@CHECKER@@': (ROOT / 'code/diagonal_checker.py').read_text().rstrip(),
    }
    for marker, value in replacements.items():
        template = template.replace(marker, value)
    if '@@' in template:
        raise ValueError('Unresolved report marker')
    source = ROOT / 'ipra_diagonal_guard.tex'
    source.write_text(template)
    if not shutil.which('pdflatex'):
        raise SystemExit('pdflatex is required to compile the PDF')
    for attempt in (1, 2, 3):
        result = subprocess.run(
            ['pdflatex', '-interaction=nonstopmode', '-halt-on-error', source.name],
            cwd=ROOT, capture_output=True, text=True)
        (ROOT / f'evidence/pdf_build_{attempt}.txt').write_text(result.stdout + result.stderr)
        if result.returncode:
            print(result.stdout[-6000:])
            raise SystemExit(result.returncode)
    print(ROOT / 'ipra_diagonal_guard.pdf')


if __name__ == '__main__':
    main()
