"""Audit Python sources from the exact repository snapshot and incoming ZIPs.

This utility measures source, not correctness. The named complete-checker
records are classified separately in evidence/frontier_candidates.json.
"""
import ast
import csv
import gzip
import hashlib
import io
import json
from pathlib import Path
import sys
import tokenize

SKIP = {tokenize.ENCODING, tokenize.NL, tokenize.NEWLINE, tokenize.INDENT,
        tokenize.DEDENT, tokenize.ENDMARKER, tokenize.COMMENT}


class RemoveDocstrings(ast.NodeTransformer):
    def strip(self, node):
        self.generic_visit(node)
        if node.body and isinstance(node.body[0], ast.Expr):
            value = node.body[0].value
            if isinstance(value, ast.Constant) and isinstance(value.value, str):
                node.body = node.body[1:]
                if not node.body and not isinstance(node, ast.Module):
                    node.body = [ast.Pass()]
        return node

    visit_Module = strip
    visit_FunctionDef = strip
    visit_AsyncFunctionDef = strip
    visit_ClassDef = strip


def measure_bytes(raw):
    tree = ast.fix_missing_locations(RemoveDocstrings().visit(ast.parse(raw)))
    text = ast.unparse(tree) + '\n'
    data = text.encode()
    parsed = ast.parse(text)
    return {
        'sha256': hashlib.sha256(raw).hexdigest(),
        'git_blob': hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest(),
        'normalized_sha256': hashlib.sha256(data).hexdigest(),
        'tokens': sum(t.type not in SKIP for t in tokenize.generate_tokens(io.StringIO(text).readline)),
        'ast_nodes': sum(1 for _ in ast.walk(parsed)),
        'normalized_bytes': len(data),
        'gzip9_bytes': len(gzip.compress(data, compresslevel=9, mtime=0)),
        'dynamic_execution': any(isinstance(n, ast.Call) and isinstance(n.func, ast.Name)
                                 and n.func.id in {'exec', 'eval'} for n in ast.walk(parsed)),
        'accept_literal': any(isinstance(n, ast.Constant) and n.value == 'ACCEPT'
                              for n in ast.walk(parsed)),
    }


def main():
    root = Path(__file__).resolve().parent
    if len(sys.argv) != 3:
        raise SystemExit('Usage: python3 census.py PINNED_CONCISEIPRA_DIRECTORY EXTRACTED_INCOMING_DIRECTORY')
    rows, failures = [], []
    sources = [('repository', Path(sys.argv[1]) / 'Artifacts'), ('incoming', Path(sys.argv[2]))]
    cache = {}
    for label, base in sources:
        for path in sorted(base.rglob('*')):
            if not path.is_file() or not (path.name.endswith('.py') or path.name.endswith('.py.gz')):
                continue
            raw = path.read_bytes()
            if raw[:2] == b'\x1f\x8b':
                raw = gzip.decompress(raw)
            digest = hashlib.sha256(raw).hexdigest()
            try:
                if digest not in cache:
                    cache[digest] = measure_bytes(raw)
                rows.append({'path': label + '/' + path.relative_to(base).as_posix(), **cache[digest]})
            except (SyntaxError, ValueError, UnicodeError) as exc:
                failures.append({'path': str(path), 'error': str(exc)})
    destination = root / 'evidence'
    destination.mkdir(exist_ok=True)
    with (destination / 'source_census.csv').open('w', newline='') as f:
        writer = csv.DictWriter(f, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)
    summary = {
        'snapshot': '12197d86f63e9ec73b2d91399c4de2a8cb0077ee',
        'python': sys.version.split()[0],
        'paths_measured': len(rows),
        'unique_source_blobs': len(cache),
        'scope': 'Every .py and .py.gz source under Artifacts and the five extracted incoming archives; embedded extensionless historical corpora are not separately recounted.',
        'parse_failures': failures,
        'classification_warning': 'A small source is not necessarily a complete sound checker. Dynamic decompression/evaluation wrappers are excluded from the direct-source comparison.',
    }
    (destination / 'census_summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    shortlisted = [r for r in rows if r['accept_literal'] and not r['dynamic_execution']
                   and (r['tokens'] <= 243 or r['ast_nodes'] <= 264 or r['normalized_bytes'] <= 474)]
    (destination / 'frontier_candidates.json').write_text(json.dumps(shortlisted, indent=2) + '\n')
    print(json.dumps({**summary, 'shortlisted_paths': len(shortlisted)}, indent=2))


if __name__ == '__main__':
    main()
