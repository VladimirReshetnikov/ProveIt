"""Assemble a standalone LaTeX source from the paper and frozen appendices."""
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def main():
    report = json.loads((ROOT / 'evidence' / 'metrics.json').read_text())
    selected = report['profiles'][-1]
    macros = '\n'.join('\\newcommand{\\' + name + '}{' + str(selected[field]) + '}'
        for name, field in [('SelectedBytes', 'normalized_bytes'),
                            ('SelectedTokens', 'significant_tokens'),
                            ('SelectedAST', 'ast_nodes')])
    rows = []
    for p in report['profiles']:
        label = p['label'].replace('Four-pattern ', 'Four-rule ').replace('Five-pattern ', 'Five-rule ')
        rows.append(label + ' & ' + ' & '.join(str(p[k]) for k in
            ('normalized_bytes', 'significant_tokens', 'ast_nodes', 'gzip9_bytes')) + r' \\')
    table = ('\\begin{center}\n\\small\n'
             '\\begin{tabular}{@{}p{0.47\\linewidth}rrrr@{}}\n\\toprule\n'
             'Complete checker & Bytes & Tokens & AST & Gzip 9\\\\\n\\midrule\n'
             + '\n'.join(rows) + '\n\\bottomrule\n\\end{tabular}\n\\end{center}')
    verification = json.loads((ROOT / 'code/packet/results/verification.json').read_text())
    validation = (f"The selected packet protocol passed {verification['standalone_process_checks']} "
        "standalone process checks, using normal Python and \\texttt{python -O}. "
        f"These include {verification['positive_certificates']} accepted certificates, "
        f"{verification['exact_packet_round_trips']} exact packet round trips, "
        f"and {verification['negative_certificates']} rejection cases. "
        f"A separate {verification['semantic_opening_checks']} generated semantic checks compared "
        "opening with an independent finite numerical interpreter. There were zero failures. "
        "Additional tree-format and ranked-format suites check the intermediate translations; "
        "their separate results are included rather than added to the selected count.")
    listing = (ROOT / 'evidence/normalized/code/packet/checker.py').read_text()
    fragments = ['inherited_choice_basis.tex', 'inherited_ordinary_bridge.tex',
                 'scalar_predecessor.tex', 'equality_reflection.tex', 'primitive_recursion.tex']
    appendix = '\n\\clearpage\n'.join((ROOT / 'reference' / name).read_text() for name in fragments)
    source = (ROOT / 'paper_main.tex').read_text()
    for marker, replacement in [('% MEASURED_MACROS', macros), ('% MEASURED_TABLE', table),
        ('% VALIDATION_SUMMARY', validation),
        ('% CHECKER_LISTING', '\\begin{lstlisting}[language=Python]\n' + listing + '\\end{lstlisting}'),
        ('% INHERITED_APPENDICES', appendix)]:
        if source.count(marker) != 1:
            raise ValueError('Missing or duplicated assembly marker: ' + marker)
        source = source.replace(marker, replacement)
    (ROOT / 'report.tex').write_text(source)
    if '--pdf' in sys.argv:
        build = ROOT / 'build'
        build.mkdir(exist_ok=True)
        command = ['pdflatex', '-interaction=nonstopmode', '-halt-on-error',
                   '-output-directory=' + str(build), 'report.tex']
        for unused in range(3):
            result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True)
            (build / 'compiler_output.txt').write_text(result.stdout + result.stderr)
            if result.returncode:
                print(result.stdout[-12000:], file=sys.stderr)
                raise SystemExit(result.returncode)
        (ROOT / 'report.pdf').write_bytes((build / 'report.pdf').read_bytes())
        print('Compiled report.pdf')


if __name__ == '__main__':
    main()
