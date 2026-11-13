#!/usr/bin/env python3
"""Remeasure the unchanged baseline sources; never execute them.

Run with CPython 3.12.14 for the exact reported AST normalization.
The numerical results are source measurements, not proofs of checker soundness.
"""
import ast
import csv
import gzip
import hashlib
import io
import json
from pathlib import Path
import platform
import sys
import tokenize
import zlib

ROOT = Path(__file__).resolve().parents[1]
IGNORED = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
           tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}


def measure(path):
    original = path.read_bytes()
    normalized = (ast.unparse(ast.parse(original.decode('utf-8'))) + '\n').encode()
    tokens = tokenize.tokenize(io.BytesIO(normalized).readline)
    return {
        'significant_tokens': sum(t.type not in IGNORED for t in tokens),
        'ast_nodes': sum(1 for _ in ast.walk(ast.parse(normalized))),
        'normalized_bytes': len(normalized),
        'gzip9_bytes': len(gzip.compress(normalized, compresslevel=9, mtime=0)),
        'original_bytes': len(original),
        'original_sha256': hashlib.sha256(original).hexdigest(),
        'normalized_sha256': hashlib.sha256(normalized).hexdigest(),
    }


def main():
    snapshot = json.loads((ROOT / 'evidence/source_snapshot.json').read_text())
    rows = []
    for entry in snapshot['controls']:
        row = {'file': entry['local_file'], 'contract': entry['contract'],
               **measure(ROOT / entry['local_file'])}
        if row['original_sha256'] != entry['original_sha256']:
            raise ValueError('Source hash changed: ' + entry['local_file'])
        rows.append(row)
    result = {
        'python': platform.python_version(), 'implementation': platform.python_implementation(),
        'zlib': zlib.ZLIB_RUNTIME_VERSION, 'commit': snapshot['commit'],
        'method': "ast.unparse(ast.parse(source)) + '\\n'; significant tokens; all AST nodes; gzip.compress(level=9,mtime=0)",
        'measurements': rows,
        'warning': 'These are different programs and input contracts. No single program attains all coordinate minima.',
    }
    if '--check' in sys.argv:
        old = json.loads((ROOT / 'evidence/measurements.json').read_text())
        if old['measurements'] != result['measurements']:
            raise AssertionError('Measurements differ; check Python and zlib versions.')
        print('All 9 source hashes and complete metric rows reproduce exactly.')
    else:
        (ROOT / 'evidence/measurements.json').write_text(json.dumps(result, indent=2) + '\n')
        with (ROOT / 'evidence/measurements.csv').open('w', newline='') as stream:
            writer = csv.DictWriter(stream, fieldnames=list(rows[0]))
            writer.writeheader()
            writer.writerows(rows)
        for row in rows:
            print(row['file'], row['significant_tokens'], row['ast_nodes'],
                  row['normalized_bytes'], row['gzip9_bytes'])


if __name__ == '__main__':
    main()
