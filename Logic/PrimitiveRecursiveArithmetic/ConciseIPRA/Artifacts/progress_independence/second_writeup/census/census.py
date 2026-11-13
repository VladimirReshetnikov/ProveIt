#!/usr/bin/env python3
"""Normalize and measure every Python source in a supplied repository subtree.

Usage: python3 census.py PATH_TO_ConciseIPRA [OUTPUT_DIRECTORY]
No source-size or path-role filter is used. Source code is never executed.
All parsed files are counted; duplicate contents retain individual path rows.
The JSON/ACCEPT flag is only a retrieval heuristic, not a soundness claim or
an assertion that the source is a standalone complete proof checker.
"""
from __future__ import annotations
import ast
import csv
import hashlib
import io
import json
from pathlib import Path
import platform
import sys
import tokenize

SKIP = {tokenize.NL, tokenize.NEWLINE, tokenize.INDENT, tokenize.DEDENT,
        tokenize.ENDMARKER, tokenize.ENCODING, tokenize.COMMENT}


def normalize(source):
    tree = ast.parse(source)
    for node in ast.walk(tree):
        if isinstance(node, (ast.Module, ast.ClassDef, ast.FunctionDef,
                             ast.AsyncFunctionDef)):
            if (node.body and isinstance(node.body[0], ast.Expr)
                    and isinstance(node.body[0].value, ast.Constant)
                    and isinstance(node.body[0].value.value, str)):
                node.body.pop(0)
                if not node.body and not isinstance(node, ast.Module):
                    node.body.append(ast.Pass())
    return ast.unparse(tree) + '\n'


def metrics(source):
    normalized = normalize(source)
    tree = ast.parse(normalized)
    return {
        'normalized_bytes': len(normalized.encode('utf-8')),
        'significant_tokens': sum(token.type not in SKIP for token in
                                 tokenize.generate_tokens(io.StringIO(normalized).readline)),
        'ast_nodes': sum(1 for _ in ast.walk(tree)),
        'normalized_sha256': hashlib.sha256(normalized.encode()).hexdigest(),
        'json_accept_heuristic': 'json' in normalized and 'ACCEPT' in normalized,
        'imports': ';'.join(sorted({node.name for node in ast.walk(tree)
                                   if isinstance(node, ast.alias)})),
    }


def main():
    if len(sys.argv) not in (2, 3):
        raise SystemExit(__doc__)
    root = Path(sys.argv[1]).resolve()
    out = Path(sys.argv[2] if len(sys.argv) == 3 else '.').resolve()
    out.mkdir(parents=True, exist_ok=True)
    cache, rows, failures = {}, [], []
    paths = sorted(root.rglob('*.py'))
    for path in paths:
        raw = path.read_bytes()
        digest = hashlib.sha256(raw).hexdigest()
        row = {'path': path.relative_to(root).as_posix(), 'raw_bytes': len(raw),
               'raw_sha256': digest}
        try:
            if digest not in cache:
                cache[digest] = metrics(raw.decode('utf-8-sig'))
            row.update(cache[digest])
            rows.append(row)
        except Exception as error:
            failures.append({**row, 'error': f'{type(error).__name__}: {error}'})
    fields = ['path', 'raw_bytes', 'normalized_bytes', 'significant_tokens',
              'ast_nodes', 'json_accept_heuristic', 'imports', 'raw_sha256',
              'normalized_sha256']
    with (out / 'all_python_metrics.csv').open('w', newline='', encoding='utf-8') as f:
        writer = csv.DictWriter(f, fieldnames=fields)
        writer.writeheader()
        writer.writerows(rows)
    # A shortlist for human review; there is intentionally no role exclusion.
    shortlist = [row for row in rows if row['json_accept_heuristic'] and (
        row['normalized_bytes'] <= 506 or row['significant_tokens'] <= 256
        or row['ast_nodes'] <= 276)]
    summary = {'python_version': platform.python_version(),
               'metric': 'Actual docstrings removed (an emptied class/function receives pass); ast.unparse plus one LF; entire module.',
               'input_root': str(root), 'python_files_seen': len(paths),
               'successfully_parsed': len(rows), 'parse_failures': failures,
               'raw_bytes_total': sum(p.stat().st_size for p in paths),
               'distinct_raw_sources': len({r['raw_sha256'] for r in rows}),
               'distinct_normalized_sources': len({r['normalized_sha256'] for r in rows}),
               'json_accept_shortlist': shortlist,
               'qualification': 'A source census, not a proof of checker soundness, completeness, or minimum possible complexity.'}
    (out / 'census_summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps({k: v for k, v in summary.items()
                      if k not in ('json_accept_shortlist', 'parse_failures')}, indent=2))
    print('Shortlist paths:', len(shortlist))
    for row in shortlist:
        print(row['significant_tokens'], row['ast_nodes'], row['normalized_bytes'], row['path'])


if __name__ == '__main__':
    main()
