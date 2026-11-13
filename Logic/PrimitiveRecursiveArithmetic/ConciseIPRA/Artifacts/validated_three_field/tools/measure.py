"""Measure complete sources without executing them (CPython 3.12.14 metric)."""
from pathlib import Path
import argparse
import ast
import csv
import hashlib
import io
import json
import sys
import tokenize

ROOT = Path(__file__).resolve().parents[1]
SKIP = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE, tokenize.NL,
        tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}
EXPECTED = {
    'code/checker_tokens306.py': (306, 362, 668),
    'code/checker_joint.py': (313, 353, 701),
    'code/checker_ast348.py': (330, 348, 681),
    'code/checker_bytes595.py': (329, 372, 595),
}

def measure(path):
    raw = path.read_bytes()
    tree = ast.parse(raw.decode('utf-8'))
    normalized = ast.unparse(tree) + '\n'
    return {
        'path': path.relative_to(ROOT).as_posix(),
        'tokens': sum(t.type not in SKIP for t in tokenize.generate_tokens(io.StringIO(normalized).readline)),
        'ast_nodes': sum(1 for _ in ast.walk(tree)),
        'normalized_bytes': len(normalized.encode('utf-8')),
        'raw_bytes': len(raw),
        'raw_sha256': hashlib.sha256(raw).hexdigest(),
        'normalized_sha256': hashlib.sha256(normalized.encode('utf-8')).hexdigest(),
    }

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    rows = [measure(p) for folder in ['code', 'controls'] for p in sorted((ROOT / folder).glob('*.py'))]
    for row in rows:
        if row['path'] in EXPECTED:
            found = tuple(row[k] for k in ('tokens', 'ast_nodes', 'normalized_bytes'))
            if found != EXPECTED[row['path']]:
                raise SystemExit(f'Metric mismatch for {row["path"]}: {found}; use CPython 3.12.14')
    receipt = {'python': sys.version, 'normalization': "ast.unparse(ast.parse(source)) + '\\n'",
               'note': 'Separate profiles; no single program attains the componentwise envelope.', 'files': rows}
    dest = ROOT / 'evidence/measurements.json'
    if args.check:
        previous = json.loads(dest.read_text())
        if previous['files'] != rows:
            raise SystemExit('Recorded source measurements differ')
    else:
        dest.write_text(json.dumps(receipt, indent=2) + '\n')
        with (ROOT / 'evidence/measurements.csv').open('w', newline='') as out:
            writer = csv.DictWriter(out, fieldnames=list(rows[0]))
            writer.writeheader()
            writer.writerows(rows)
    print(json.dumps({'status': 'PASS', 'python': sys.version.split()[0],
                      'measurements': [{k: v for k, v in r.items() if k in ('path','tokens','ast_nodes','normalized_bytes')} for r in rows]}, indent=2))

if __name__ == '__main__':
    main()
