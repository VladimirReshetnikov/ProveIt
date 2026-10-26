#!/usr/bin/env python3
"""Reproduce static source checks. This does not compile or type-check Lean.

Checks pinned snapshot hashes, candidate hashes, original theorem headers,
unchanged import lines, absence of new proof holes, four sequential patches,
the combined patch, and exact complete-file source totals. Only a temporary
directory is mutated. Requires Python 3.9+ and git; no network is used.
"""
import hashlib
import json
import re
import shutil
import subprocess
import tempfile
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DECL = re.compile(r'(?m)^(?:(?:private|protected)\s+)?(?:theorem|lemma)\s+([^\s(:{]+)')


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def headers(text):
    result = defaultdict(list)
    for match in DECL.finditer(text):
        end = text.find(':=', match.start())
        if end < 0:
            raise ValueError('missing body marker for ' + match.group(1))
        result[match.group(1)].append(text[match.start():end].rstrip())
    return dict(result)


def git_apply(work, patch):
    for check in (True, False):
        argv = ['git', 'apply'] + (['--check'] if check else []) + [str(patch)]
        result = subprocess.run(argv, cwd=work, text=True, capture_output=True)
        if result.returncode:
            raise RuntimeError(' '.join(argv) + '\n' + result.stdout + result.stderr)


def main():
    if not shutil.which('git'):
        raise RuntimeError('git is required to replay the patch composition')
    evidence = json.loads((ROOT / 'evidence/composed-source-validation.json').read_text())
    totals = {'files': 0, 'before_lines': 0, 'after_lines': 0,
              'net_lines_removed': 0, 'net_bytes_removed': 0}
    header_count = 0
    for row in evidence['files']:
        old = (ROOT / 'source-snapshot' / row['path']).read_bytes()
        new = (ROOT / 'candidate-source' / row['path']).read_bytes()
        assert sha256(old) == row['source_sha256'], ('source hash', row['path'])
        assert sha256(new) == row['candidate_sha256'], ('candidate hash', row['path'])
        blob = hashlib.sha1(b'blob ' + str(len(old)).encode() + b'\0' + old).hexdigest()
        assert blob == row['source_git_blob'], ('Git blob', row['path'])
        before, after = old.decode('utf-8'), new.decode('utf-8')
        for field, actual in [('before_lines', len(before.splitlines())),
                              ('after_lines', len(after.splitlines())),
                              ('before_bytes', len(old)), ('after_bytes', len(new))]:
            assert row[field] == actual, (row['path'], field, row[field], actual)
        old_headers, new_headers = headers(before), headers(after)
        for name, items in old_headers.items():
            assert new_headers.get(name) == items, ('changed original theorem header', row['path'], name)
            header_count += len(items)
        imports = lambda s: re.findall(r'(?m)^import\s+.*$', s)
        assert imports(before) == imports(after), ('changed imports', row['path'])
        holes = lambda s: re.findall(r'\b(?:sorry|admit)\b|(?m:^axiom\s+)', s)
        assert holes(before) == holes(after), ('new proof hole or axiom text', row['path'])
        totals['files'] += 1
        totals['before_lines'] += row['before_lines']
        totals['after_lines'] += row['after_lines']
        totals['net_bytes_removed'] += row['before_bytes'] - row['after_bytes']
    totals['net_lines_removed'] = totals['before_lines'] - totals['after_lines']
    assert totals == evidence['totals'], ('totals differ', totals, evidence['totals'])
    composition = []
    with tempfile.TemporaryDirectory(prefix='proveit-source-review-') as temp:
        for mode in ('sequential', 'combined'):
            work = Path(temp) / mode
            shutil.copytree(ROOT / 'source-snapshot', work)
            patches = ([ROOT / 'patches' / r['patch'] for r in evidence['patch_checks']]
                       if mode == 'sequential' else [ROOT / 'patches/combined.patch'])
            for patch in patches:
                git_apply(work, patch)
            for row in evidence['files']:
                assert sha256((work / row['path']).read_bytes()) == row['candidate_sha256'], (mode, row['path'])
            composition.append({'mode': mode, 'patches': len(patches), 'status': 'passed'})
    print(json.dumps({'status': 'passed: static source checks only',
                      'lean_compiler_run': False, 'original_theorem_headers_unchanged': header_count,
                      'imports_unchanged': True, 'totals': totals,
                      'patch_composition': composition}, indent=2))


if __name__ == '__main__':
    main()
