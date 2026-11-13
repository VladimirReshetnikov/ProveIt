"""Reproduce the checkers, validation records, metrics, and optional PDF."""
import argparse
import gzip
import hashlib
import json
from pathlib import Path
import platform
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def run(command, log):
    result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True)
    (ROOT / 'evidence' / log).write_text(result.stdout + result.stderr)
    if result.returncode:
        raise RuntimeError(f'{command[0]} failed; see evidence/{log}')


def verify_sources():
    manifest = json.loads((ROOT / 'evidence/source_manifest.json').read_text())
    for entry in manifest['included_files']:
        data = (ROOT / entry['local_path']).read_bytes()
        blob = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        if blob != entry['git_blob_sha1'] or hashlib.sha256(data).hexdigest() != entry['sha256']:
            raise RuntimeError('Upstream source changed: ' + entry['local_path'])


def measurements():
    readable = json.loads((ROOT / 'evidence/readable_validation.json').read_text())
    direct = json.loads((ROOT / 'comparison/evidence/verification.json').read_text())
    rows = [
        ('Pinned three-case clausal checker', direct['metrics'][0]),
        ('Same source, root case deleted', direct['metrics'][1]),
        ('New matched three-case control', readable['metrics'][1]),
        ('New two-case checker', readable['metrics'][0]),
    ]
    raw_paths = [ROOT/'comparison/code/control.py', ROOT/'comparison/code/checker.py',
                 ROOT/'code/control_three_case.py', ROOT/'code/checker.py']
    normalized = []
    table = [r'\begin{center}', r'\small', r'\begin{tabular}{@{}lrrrr@{}}',
             r'\toprule', r'Complete checker & Bytes & Tokens & AST & Gzip-9\\', r'\midrule']
    for (label, m), raw_path in zip(rows, raw_paths):
        raw = raw_path.read_bytes()
        row = dict(label=label, normalized_bytes=m['normalized_bytes'],
                   significant_tokens=m.get('significant_tokens', m.get('tokens')),
                   ast_nodes=m['ast_nodes'], gzip9_bytes=m['gzip9_bytes'],
                   raw_bytes=len(raw), raw_gzip9_bytes=len(gzip.compress(raw, compresslevel=9, mtime=0)))
        normalized.append(row)
        table.append(label + ' & ' + ' & '.join(str(row[k]) for k in
                     ('normalized_bytes','significant_tokens','ast_nodes','gzip9_bytes')) + r'\\')
    table += [r'\bottomrule', r'\end{tabular}', r'\end{center}']
    (ROOT / 'evidence/metrics_table.tex').write_text('\n'.join(table) + '\n')
    (ROOT / 'evidence/metrics.json').write_text(json.dumps(normalized, indent=2) + '\n')
    summary = r'''The direct-deletion suite passed \textbf{47 translated closed proofs},
including 32 inherited and 15 added examples; \textbf{28 rejection cases};
five obsolete certificates that require translation; and six open-context
checks. It executed \textbf{320 public CLI runs} across readable and
normalized modules, both normally and with \texttt{python -O}. It removed
61 root-evaluation nodes and checked the exact node identity at every
transformed subtree. The independently implemented readable checker passed
\textbf{32 positive and 29 rejection examples}, \textbf{122 public CLI runs}
with ordinary and optimized Python, and \textbf{1,000 deterministic
substitution comparisons}. These suites overlap; their case counts are
not presented as a count of distinct mathematical theorems.
'''
    (ROOT / 'evidence/verification_summary.tex').write_text(summary)
    (ROOT / 'evidence/environment.json').write_text(json.dumps({
        'python':sys.version,'platform':platform.platform(),
        'gzip_level':9,'gzip_mtime':0,
        'normalization':'leading module docstring removed; ast.unparse + one LF',
        'no_new_lean_compilation':True},indent=2) + '\n')
    return readable, direct


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--pdf', action='store_true', help='also compile report.tex twice with pdflatex')
    args = parser.parse_args()
    verify_sources()
    run([sys.executable, str(ROOT/'code/verify.py')], 'readable_test_run.log')
    run([sys.executable, str(ROOT/'comparison/tests/verify.py')], 'direct_test_run.log')
    readable, direct = measurements()
    if args.pdf:
        for number in (1,2):
            run(['pdflatex','-interaction=nonstopmode','-halt-on-error','report.tex'], f'latex_pass_{number}.log')
    print(json.dumps({'all_passed':True, 'readable_positive':readable['positive_examples'],
        'readable_negative':readable['negative_examples'],
        'direct_positive':direct['translated_positive'],'direct_negative':direct['negative'],
        'cli_runs':readable['public_cli_runs']+direct['public_cli_runs'],
        'substitution_comparisons':readable['substitution_comparisons'],
        'pdf_compiled':args.pdf}, indent=2))


if __name__ == '__main__':
    main()
