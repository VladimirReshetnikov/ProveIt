"""Reproduce the delivered checker comparisons using Python's standard library.

This support program is untrusted and is never imported by a proof checker.
It verifies frozen file hashes, compares ASTs outside the stated modifications,
measures complete standalone modules, writes gzip-9 normalized sources, and
runs the packaged meaningful positive/negative fixtures in normal and -O mode.
Run from any directory: python3 /path/to/this/package/reproduce.py
"""
import ast
import csv
import gzip
import hashlib
import io
import json
import platform
import subprocess
import sys
import tokenize
import zlib
from pathlib import Path

ROOT = Path(__file__).resolve().parent
EVIDENCE = ROOT / 'evidence'
IGNORED = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.COMMENT,
           tokenize.NL, tokenize.NEWLINE, tokenize.INDENT, tokenize.DEDENT}


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def normalized(path):
    tree = ast.parse(path.read_bytes())
    return tree, (ast.unparse(tree) + '\n').encode('utf-8')


def measure(path):
    raw = path.read_bytes()
    tree, data = normalized(path)
    compressed = gzip.compress(data, compresslevel=9, mtime=0)
    rel = path.relative_to(ROOT).as_posix()
    gzip_path = 'evidence/normalized_gzip9/' + rel.replace('/', '__') + '.gz'
    (ROOT / gzip_path).write_bytes(compressed)
    return {
        'path': rel,
        'raw_bytes': len(raw),
        'normalized_bytes': len(data),
        'significant_tokens': sum(t.type not in IGNORED for t in
            tokenize.tokenize(io.BytesIO(data).readline)),
        'ast_nodes': sum(1 for _ in ast.walk(tree)),
        'gzip9_normalized_bytes': len(compressed),
        'source_sha256': sha256(raw),
        'normalized_sha256': sha256(data),
        'gzip_path': gzip_path,
    }


def ast_without(path, names):
    tree = ast.parse(path.read_bytes())
    tree.body = [n for n in tree.body if not
                 (isinstance(n, ast.FunctionDef) and n.name in names)]
    return ast.dump(tree, include_attributes=False)


def frozen_source_check():
    manifest = json.loads((EVIDENCE / 'source_map.json').read_text())
    for row in manifest['entries']:
        data = (ROOT / row['path']).read_bytes()
        if len(data) != row['bytes'] or sha256(data) != row['sha256']:
            raise ValueError('Frozen file changed: ' + row['path'])
    return len(manifest['entries'])


def structural_checks():
    native_same = ast_without(ROOT / 'reference/checkers/baseline_native.py', {'v'}) == ast_without(ROOT / 'code/checker_native.py', {'v'})
    guarded_same = ast_without(ROOT / 'reference/checkers/baseline_guarded.py', {'term', 'formula'}) == ast_without(ROOT / 'code/checker_guarded.py', {'term', 'formula'})
    old = (ROOT / 'reference/checkers/baseline_compact.py').read_text()
    needle = '([s, u] if s else [t] * 3)'
    if old.count(needle) != 1:
        raise ValueError('Unexpected compact comparator source')
    expected = old.replace(needle, '(s and [s, u] or [t] * 3)')
    compact_same = ast.dump(ast.parse(expected), include_attributes=False) == ast.dump(ast.parse((ROOT / 'code/checker_compact.py').read_text()), include_attributes=False)
    result = {
        'native_ast_identical_outside_validator': native_same,
        'guarded_ast_identical_outside_validators': guarded_same,
        'compact_ast_matches_exact_declared_expression_change': compact_same,
    }
    if not all(result.values()):
        raise ValueError('A module differs outside its declared modification')
    return result


def run_checker(relative, payload, optimized):
    args = [sys.executable]
    if optimized:
        args.append('-O')
    args.append(str(ROOT / relative))
    try:
        run = subprocess.run(args, input=payload, stdout=subprocess.PIPE,
                             stderr=subprocess.PIPE, timeout=10)
    except subprocess.TimeoutExpired:
        return {'accepted': False, 'timeout': True, 'exit_code': None}
    return {'accepted': run.returncode == 0 and run.stdout == b'ACCEPT\n',
            'timeout': False, 'exit_code': run.returncode}


def main():
    EVIDENCE.mkdir(exist_ok=True)
    (EVIDENCE / 'normalized_gzip9').mkdir(exist_ok=True)
    frozen_files = frozen_source_check()
    structural = structural_checks()
    paths = sorted((ROOT / 'code').glob('*.py')) + sorted((ROOT / 'reference/checkers').glob('*.py'))
    rows = [measure(path) for path in paths]
    settings = {
        'python': platform.python_version(),
        'implementation': platform.python_implementation(),
        'zlib_build': zlib.ZLIB_VERSION,
        'zlib_runtime': zlib.ZLIB_RUNTIME_VERSION,
        'normalization': "ast.unparse(ast.parse(complete_module)) plus one LF; no source removed",
        'gzip': 'gzip.compress(normalized, compresslevel=9, mtime=0); full wrapper; informational only',
        'metrics': rows,
    }
    (EVIDENCE / 'metrics.json').write_text(json.dumps(settings, indent=2) + '\n')
    with (EVIDENCE / 'metrics.csv').open('w', newline='') as stream:
        writer = csv.DictWriter(stream, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)
    cases = json.loads((ROOT / 'tests/cases.json').read_text())
    receipts = []
    for pair in cases['pairs']:
        for case in pair['cases']:
            payload = (ROOT / case['file']).read_bytes()
            for optimized in (False, True):
                old = run_checker(pair['baseline'], payload, optimized)
                new = run_checker(pair['candidate'], payload, optimized)
                receipts.append({
                    'profile': pair['name'], 'case': case['file'],
                    'optimized': optimized, 'expected': case['expected'],
                    'baseline': old, 'candidate': new,
                    'matched': old['accepted'] == new['accepted'] == case['expected']
                               and not old['timeout'] and not new['timeout'],
                })
    mismatches = [row for row in receipts if not row['matched']]
    result = {
        'frozen_files_verified': frozen_files,
        'structural_checks': structural,
        'distinct_fixture_files': len({row['case'] for row in receipts}),
        'profile_fixture_cases': sum(len(p['cases']) for p in cases['pairs']),
        'paired_comparisons': len(receipts),
        'process_executions': 2 * len(receipts),
        'expected_accepting_pairs': sum(row['expected'] for row in receipts),
        'expected_rejecting_pairs': sum(not row['expected'] for row in receipts),
        'timeouts': sum(row['baseline']['timeout'] + row['candidate']['timeout'] for row in receipts),
        'mismatches': mismatches,
        'receipts': receipts,
        'scope': 'Finite implementation evidence; universal preservation proofs are written, not machine-formalized.',
    }
    (EVIDENCE / 'portable_validation.json').write_text(json.dumps(result, indent=2) + '\n')
    concise = {k: v for k, v in result.items() if k != 'receipts'}
    concise['selected_metrics'] = [{k: row[k] for k in ('path', 'significant_tokens', 'ast_nodes', 'normalized_bytes', 'gzip9_normalized_bytes')}
                                  for row in rows if row['path'].startswith('code/')]
    print(json.dumps(concise, indent=2))
    if mismatches:
        raise SystemExit('Checker reproduction failed; see evidence/portable_validation.json')


if __name__ == '__main__':
    main()
