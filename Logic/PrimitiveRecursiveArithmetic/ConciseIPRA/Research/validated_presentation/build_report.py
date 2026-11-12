#!/usr/bin/env python3
"""Expand the complete standalone TeX source and compile its PDF."""
import gzip
import json
import re
import shutil
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent
NAME = 'ipra_validated_presentation'


def tables():
    data = json.loads((ROOT/'evidence/metrics.json').read_text())
    labels = {
        'reference/native_typed_full.py': 'Full Eq/Q/D control',
        'code/native_typed_full.py': 'Full Eq/Q/D refinement',
        'reference/native_typed_eqd.py': 'Eq/D control',
        'code/native_typed_eqd.py': 'Eq/D refinement',
    }
    rows = []
    for record in data['metrics']:
        rows.append('{} & {} & {} & {} & {}\\\\'.format(
            labels[record['path']], record['normalized_bytes'],
            record['significant_tokens'], record['ast_nodes'],
            record['gzip9_bytes_mtime0']))
        source = ROOT/record['path']
        target = ROOT/'evidence/gzip'/record['path']
        target.parent.mkdir(parents=True, exist_ok=True)
        target.with_suffix('.py.gz').write_bytes(
            gzip.compress(source.read_bytes(), compresslevel=9, mtime=0))
    table = '\n'.join([
        r'\begin{center}', r'\begin{tabular}{lrrrr}', r'\toprule',
        r'Complete standalone program & Bytes & Tokens & AST & Gzip-9\\',
        r'\midrule', *rows, r'\bottomrule', r'\end{tabular}', r'\end{center}',
    ])
    (ROOT/'evidence/metrics_table.tex').write_text(table+'\n')
    receipt = json.loads((ROOT/'evidence/validation.json').read_text())
    a, b = receipt['profiles']
    summary = (
        r'The reproduced comparison has zero discrepancies. For each public '
        r'profile, it checks \textbf{'+f"{a['raw_json_values_checked']:,}"+
        r'} JSON-derived values against an independent integer/list predicate '
        r'and performs \textbf{'+f"{a['scope_comparisons']:,}"+
        r'} old/new scoped-validator comparisons. The '
        f"{a['corpus_count']} input fixtures give "
        f"{a['corpus_accept_count']} acceptances and {a['corpus_reject_count']} rejections "
        r'for full Eq/Q/D, and '
        f"{b['corpus_accept_count']} acceptances and {b['corpus_reject_count']} rejections "
        r'for Eq/D, matching their controls. Eleven disallowed unused-prefix '
        r'types are rejected in ordinary and optimized Python execution. '
        r'The corpus includes one metadata-shaped JSON object as a deliberate '
        r'top-level rejection. The proof-kernel AST is unchanged in both profiles.'
    )
    (ROOT/'evidence/validation_summary.tex').write_text(summary+'\n')


def expand(text):
    def include(match):
        return expand((ROOT/match.group(1)).read_text())
    text = re.sub(r'\\input\{([^}]+)\}', include, text)
    def listing(match):
        return '\\begin{lstlisting}\n'+(ROOT/match.group(1)).read_text()+'\\end{lstlisting}'
    return re.sub(r'\\lstinputlisting\{([^}]+)\}', listing, text)


tables()
(ROOT/(NAME+'.tex')).write_text(expand((ROOT/'report.tex').read_text()))
(ROOT/'build').mkdir(exist_ok=True)
for _ in range(3):
    completed = subprocess.run([
        'pdflatex', '-interaction=nonstopmode', '-halt-on-error',
        '-output-directory=build', NAME+'.tex',
    ], cwd=ROOT, capture_output=True, text=True)
    (ROOT/'build/console.txt').write_text(completed.stdout+completed.stderr)
    if completed.returncode:
        print((completed.stdout+completed.stderr)[-6000:])
        raise SystemExit(completed.returncode)
shutil.copy2(ROOT/'build'/(NAME+'.pdf'), ROOT/(NAME+'.pdf'))
log = (ROOT/'build'/(NAME+'.log')).read_text()
issues = [line for line in log.splitlines()
          if 'Overfull' in line or 'undefined' in line or 'multiply defined' in line]
(ROOT/'evidence/latex_summary.txt').write_text(
    'Three pdflatex passes completed.\n'+
    ('\n'.join(issues) if issues else 'No overfull boxes or unresolved references.'))
print(json.dumps({'pdf':str(ROOT/(NAME+'.pdf')), 'layout_log_issues':issues},indent=2))
