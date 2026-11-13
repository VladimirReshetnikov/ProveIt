"""Remeasure complete checkers and the entire frozen comparison source corpus.

All source is counted. Only the measurement helper is imported; historical
checker programs are parsed as data and are never executed here.
"""
import argparse
import gzip
import importlib.util
import json
from pathlib import Path
import platform
import zlib

ROOT = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('source_measure', ROOT / 'reference/measure_source.py')
source_measure = importlib.util.module_from_spec(spec)
spec.loader.exec_module(source_measure)
measure = source_measure.measure


def measurements():
    corpus = json.loads((ROOT / 'evidence/corpus_metrics.json').read_text())
    mismatches = []
    keys = ['normalized_tokens', 'ast_nodes', 'normalized_bytes', 'raw_bytes',
            'gzip9_raw', 'gzip9_normalized', 'sha256']
    for old in corpus['sources']:
        new = measure((ROOT / 'reference/sources' / (old['sha256'] + '.py')).read_bytes())
        differences = {key: [old[key], new[key]] for key in keys if old[key] != new[key]}
        if differences:
            mismatches.append({'sha256': old['sha256'], 'differences': differences})
    files = [
        ('Old byte minimum', 'reference/comparators/certified_zero_bytes.py'),
        ('Old token/AST minimum', 'reference/comparators/certified_zero_joint.py'),
        ('Old other AST minimum', 'reference/comparators/affine_supply_ast.py'),
        ('Old explicit-list checker', 'reference/comparators/certified_zero_explicit.py'),
        ('New recommended checker', 'code/checker.py'),
        ('New compact checker', 'code/checker_compact.py'),
        ('Readable expansion', 'code/readable_checker.py'),
    ]
    rows = []
    for label, path in files:
        rows.append(dict(label=label, path=path, **measure((ROOT / path).read_bytes())))
    return {'python': platform.python_version(), 'zlib': zlib.ZLIB_RUNTIME_VERSION,
            'frozen_source_count': len(corpus['sources']), 'frozen_mismatches': mismatches,
            'rows': rows}


def save(result):
    (ROOT / 'evidence/checker_metrics.json').write_text(json.dumps(result, indent=2) + '\n')
    lines = [r'\begin{center}\small', r'\begin{tabular}{lrrrr}',
             r'\toprule', r'Complete program & Bytes & Tokens & AST & Gzip-9\\', r'\midrule']
    for row in result['rows']:
        if row['label'] == 'Readable expansion':
            continue
        lines.append(f"{row['label']} & {row['normalized_bytes']} & {row['normalized_tokens']} & {row['ast_nodes']} & {row['gzip9_raw']}" + r'\\')
    lines += [r'\bottomrule', r'\end{tabular}', r'\end{center}', '']
    (ROOT / 'evidence/metrics_table.tex').write_text('\n'.join(lines))
    for name in ['checker.py', 'checker_compact.py']:
        source = ROOT / 'code' / name
        source.with_suffix(source.suffix + '.gz').write_bytes(gzip.compress(source.read_bytes(), compresslevel=9, mtime=0))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true', help='Refresh evidence and gzip artifacts')
    args = parser.parse_args()
    result = measurements()
    if result['frozen_mismatches']:
        print(json.dumps(result['frozen_mismatches'], indent=2))
        raise SystemExit('Frozen measurements differ. Use the recorded CPython/zlib versions for exact reproduction.')
    if args.write:
        save(result)
    print(json.dumps({key: value for key, value in result.items() if key != 'frozen_mismatches'}, indent=2))


if __name__ == '__main__':
    main()
