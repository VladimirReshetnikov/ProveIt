"""Measure complete sources; compare immutable controls with their audit receipt."""
from pathlib import Path
import ast
import hashlib
import io
import json
import sys
import tokenize

ROOT = Path(__file__).resolve().parent
IGNORE = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
          tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}

def measure(path):
    data = path.read_bytes()
    tree = ast.parse(data)
    normalized = (ast.unparse(tree) + '\n').encode('utf-8')
    return {
        'path': path.relative_to(ROOT).as_posix(),
        'tokens': sum(t.type not in IGNORE for t in
                      tokenize.generate_tokens(io.StringIO(normalized.decode()).readline)),
        'ast_nodes': sum(1 for _ in ast.walk(tree)),
        'normalized_bytes': len(normalized),
        'source_sha256': hashlib.sha256(data).hexdigest(),
        'normalized_sha256': hashlib.sha256(normalized).hexdigest(),
    }

def main():
    audit = json.loads((ROOT / 'evidence/baseline_metrics.json').read_text())
    records = []
    for old in audit['selected_programs']:
        row = measure(ROOT / old['package_path'])
        for key in ('source_sha256', 'normalized_sha256', 'tokens',
                    'ast_nodes', 'normalized_bytes'):
            if row[key] != old[key]:
                raise AssertionError((row['path'], key, row[key], old[key]))
        records.append(row)
    for path in sorted((ROOT / 'code').glob('checker*.py')):
        records.append(measure(path))
    report = {'python': sys.version,
              'benchmark_python': 'CPython 3.12.14',
              'normalization': 'ast.unparse plus one LF; complete modules',
              'records': records}
    (ROOT / 'evidence/measurements.json').write_text(json.dumps(report, indent=2) + '\n')
    for row in records:
        print(f"{row['path']}: {row['tokens']} tokens, {row['ast_nodes']} AST nodes, "
              f"{row['normalized_bytes']} normalized bytes")
    return report

if __name__ == '__main__':
    main()
