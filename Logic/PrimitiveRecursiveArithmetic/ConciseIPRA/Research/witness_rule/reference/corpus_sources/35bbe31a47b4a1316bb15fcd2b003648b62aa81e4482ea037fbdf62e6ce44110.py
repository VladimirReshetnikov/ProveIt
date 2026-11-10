"""Measure complete new checkers and the pinned historical source corpus.

This script parses historical Python but never executes it. The normalizer
is the same whole-module AST-unparse convention used in the draft corpus.
Gzip level 9 is informational. Run --write after intentional source edits;
the default verifies the distributed records without changing them.
"""
import argparse
import ast
import gzip
import hashlib
import json
from pathlib import Path
import platform
import zlib

from audit_corpus import metrics

ROOT = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    expected = json.loads((ROOT / 'evidence/checker_metrics.json').read_text())
    measured = []
    for entry in expected:
        raw = (ROOT / entry['file']).read_bytes()
        m = metrics(raw)
        row = dict(file=entry['file'], normalized_tokens=m['tokens'],
                   ast_nodes=m['ast'], normalized_bytes=m['bytes'],
                   raw_bytes=m['raw'], gzip9_raw=m['gzip_raw'],
                   gzip9_normalized=m['gzip_norm'],
                   sha256=hashlib.sha256(raw).hexdigest())
        measured.append(row)
        compressed = ROOT / (entry['file'] + '.gz')
        if args.write:
            compressed.write_bytes(gzip.compress(raw, compresslevel=9, mtime=0))
        elif gzip.decompress(compressed.read_bytes()) != raw:
            raise ValueError('Compressed source mismatch: ' + entry['file'])
    if not args.write and measured != expected:
        raise ValueError('Source metrics differ; the distributed counts use Python 3.12.14 and zlib 1.3.2.')

    inventory = json.loads((ROOT / 'evidence/current_corpus_metrics.json').read_text())
    if len(inventory['sources']) != 370:
        raise ValueError('Unexpected source inventory')
    for entry in inventory['sources']:
        raw = (ROOT / 'source_corpus' / (entry['sha256'] + '.py')).read_bytes()
        if hashlib.sha256(raw).hexdigest() != entry['sha256']:
            raise ValueError('Historical source hash mismatch')
        m = metrics(raw)
        if any(m[key] != entry[key] for key in m):
            raise ValueError('Historical metric mismatch: ' + entry['sha256'])

    provenance = json.loads((ROOT / 'reference/provenance.json').read_text())
    comparison = []
    for entry in provenance:
        raw = (ROOT / entry['file']).read_bytes()
        if hashlib.sha256(raw).hexdigest() != entry['sha256']:
            raise ValueError('Comparator hash mismatch: ' + entry['file'])
        if 'transformation' in entry:
            tree = ast.parse((ROOT / entry['source']).read_bytes())
            hits = [j for j, n in enumerate(tree.body)
                    if isinstance(n, ast.Try) and not n.orelse and not n.finalbody
                    and len(n.handlers) == 1 and 'REJECT' in ast.unparse(n.handlers[0])]
            if len(hits) != 1:
                raise ValueError('Expected one exact output wrapper')
            j = hits[0]
            tree.body[j:j+1] = tree.body[j].body
            if (ast.unparse(tree) + '\n').encode() != raw:
                raise ValueError('Matched-driver transformation mismatch')
        comparison.append(dict(file=entry['file'], **metrics(raw)))
    record = dict(python=platform.python_version(), zlib=zlib.ZLIB_VERSION,
                  corpus_sources=len(inventory['sources']), new=measured,
                  comparators=comparison)
    if args.write:
        (ROOT / 'evidence/checker_metrics.json').write_text(json.dumps(measured, indent=2) + '\n')
        (ROOT / 'evidence/measurement_run.json').write_text(json.dumps(record, indent=2) + '\n')
        write_table(record)
    else:
        saved = json.loads((ROOT / 'evidence/measurement_run.json').read_text())
        if record != saved:
            raise ValueError('Measurement record differs from distributed environment')
    print(json.dumps(record, indent=2))


def write_table(record):
    labels = {
        'literal_bytes.py': 'Old literal byte leader',
        'literal_ast_tokens.py': 'Old literal token/AST leader',
        'affine_matched.py': 'Old affine, matched driver',
        'arity_tokens_matched.py': 'Old arity, matched driver',
        'loop_matched.py': 'Old loop, matched driver',
    }
    rows = []
    for row in record['comparators']:
        if Path(row['file']).name in labels:
            rows.append((labels[Path(row['file']).name], row['tokens'], row['ast'], row['bytes'], row['gzip_raw']))
    for label, row in zip(('New byte profile', 'New token profile', 'New AST profile', 'New explicit-list profile'), record['new']):
        rows.append((label, row['normalized_tokens'], row['ast_nodes'], row['normalized_bytes'], row['gzip9_raw']))
    lines = [r'\begin{table}[htbp]\centering\small',
             r'\begin{tabular}{lrrrr}\toprule',
             r'Complete program & Tokens & AST & Bytes & Gzip-9\\\midrule']
    for row in rows:
        lines.append(' & '.join(map(str, row)) + r'\\')
    lines += [r'\bottomrule\end{tabular}',
              r'\caption{Whole-module counts on CPython 3.12.14. Bytes are normalized UTF-8; gzip is of the exact raw source and is informational. The new profile sources are already normalized.}',
              r'\label{tab:metrics}\end{table}']
    (ROOT / 'evidence/metrics_table.tex').write_text('\n'.join(lines) + '\n')


if __name__ == '__main__':
    main()
