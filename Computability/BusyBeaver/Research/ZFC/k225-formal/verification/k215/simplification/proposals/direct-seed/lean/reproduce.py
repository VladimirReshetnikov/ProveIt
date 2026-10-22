#!/usr/bin/env python3
"""Build the pinned, self-contained joint proof sources from scratch.

Usage: python3 reproduce.py --lean /path/to/lean-4.32.0/bin/lean --out /new/directory
No object from the delivered packet or a prior run is reused.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time

HERE = Path(__file__).resolve().parent
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}

def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

def code_without_comments(text: str) -> str:
    """Remove nested Lean comments and string literals for the hole scan."""
    out, i, depth = [], 0, 0
    while i < len(text):
        if depth:
            if text.startswith('/-', i): depth += 1; i += 2
            elif text.startswith('-/', i): depth -= 1; i += 2
            else: out.append('\n' if text[i] == '\n' else ' '); i += 1
        elif text.startswith('/-', i): depth = 1; i += 2
        elif text.startswith('--', i):
            j = text.find('\n', i); i = len(text) if j < 0 else j
        elif text[i] == '"':
            i += 1
            while i < len(text):
                if text[i] == '\\': i += 2
                elif text[i] == '"': i += 1; break
                else: i += 1
            out.append(' ')
        else: out.append(text[i]); i += 1
    if depth: raise ValueError('unterminated source comment')
    return ''.join(out)

def axiom_reports(text: str) -> dict[str, list[str]]:
    found = {}
    pattern = r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)"
    for match in re.finditer(pattern, text, re.S):
        name, raw = match.groups()
        axioms = sorted(x.strip() for x in (raw or '').split(',') if x.strip())
        if set(axioms) - ALLOWED_AXIOMS:
            raise ValueError(f'unexpected axioms for {name}: {axioms}')
        if name in found and found[name] != axioms:
            raise ValueError(f'inconsistent repeated axiom report for {name}')
        found[name] = axioms
    return found

def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--lean', required=True, type=Path)
    ap.add_argument('--out', required=True, type=Path,
                    help='must not already exist; all compiled objects are created here')
    ap.add_argument('--check-only', action='store_true', help='check inputs without running Lean')
    args = ap.parse_args()
    manifest = json.loads((HERE / 'source_bindings.json').read_text())
    src = HERE / 'src'
    files = {x['snapshot_path'] for x in manifest['modules']}
    actual = {str(p.relative_to(HERE)) for p in src.rglob('*.lean')}
    if files != actual:
        raise ValueError(f'source inventory mismatch: extra={actual-files}, missing={files-actual}')
    if list(src.rglob('*.olean')) or list(src.rglob('*.olean.private')):
        raise ValueError('source snapshot contains a compiled object')
    seen = set()
    for row in manifest['modules']:
        path = HERE / row['snapshot_path']
        if sha(path) != row['sha256']: raise ValueError(f'source hash mismatch: {path}')
        code = code_without_comments(path.read_text())
        if re.search(r'\b(sorry|admit)\b|^\s*(axiom|constant)\s', code, re.M):
            raise ValueError(f'unchecked declaration or proof hole in {path}')
        deps = [m for line in code.splitlines() if re.match(r'^\s*import\s', line)
                for m in line.strip().split()[1:]]
        if deps != row['imports']: raise ValueError(f'import list mismatch: {path}')
        if any(m not in seen and m.split('.')[0] not in {'Init', 'Std', 'Lean'} for m in deps):
            raise ValueError(f'non-topological or unbound import for {row["module"]}')
        seen.add(row['module'])
    if args.check_only:
        print(f'INPUT PASS: {len(seen)} pinned sources; no compilation performed')
        return
    lean = args.lean.resolve(strict=True)
    version = subprocess.check_output([str(lean), '--version'], text=True).strip()
    if 'version 4.32.0,' not in version or '8c9756b28d64dab099da31a4c09229a9e6a2ef35' not in version:
        raise ValueError(f'wrong Lean toolchain: {version}')
    out = args.out.resolve()
    if out.exists(): raise ValueError(f'output directory already exists: {out}')
    out.mkdir(parents=True)
    objects, logs = out / 'objects', out / 'logs'
    objects.mkdir(); logs.mkdir()
    env = dict(os.environ, LEAN_PATH=str(objects))
    result = {'lean_version': version, 'source_manifest_sha256': sha(HERE/'source_bindings.json'),
              'modules': [], 'selected_axioms': {}, 'status': 'RUNNING'}
    reports = {}
    def save(): (out/'receipt.json').write_text(json.dumps(result, indent=2)+'\n')
    save()
    try:
        for row in manifest['modules']:
            rel = Path(*row['module'].split('.'))
            target = objects / rel.with_suffix('.olean')
            target.parent.mkdir(parents=True, exist_ok=True)
            start = time.monotonic()
            run = subprocess.run([str(lean), '-o', str(target), str(rel.with_suffix('.lean'))],
                                 cwd=src, env=env, text=True, stdout=subprocess.PIPE,
                                 stderr=subprocess.STDOUT)
            log = logs/(row['module']+'.log'); log.write_text(run.stdout)
            record = {'module': row['module'], 'source_sha256': row['sha256'],
                      'log_sha256': sha(log), 'returncode': run.returncode,
                      'seconds': time.monotonic()-start}
            result['modules'].append(record)
            if run.returncode != 0 or 'sorryAx' in run.stdout:
                raise ValueError(f'kernel compilation failed: {row["module"]}; see {log}')
            found = axiom_reports(run.stdout)
            reports.update(found)
            record['olean_sha256'] = sha(target)
            record['warnings'] = run.stdout.count('warning:')
            if row['module'] in manifest['warning_free_modules'] and record['warnings']:
                raise ValueError(f'new proof/API module produced warnings: {row["module"]}')
            print(row['module'], 'PASS', flush=True)
            save()
        expected = manifest['expected_axioms']
        for name, axioms in expected.items():
            if reports.get(name) != axioms:
                raise ValueError(f'axiom report missing or changed: {name}: {reports.get(name)}')
        result['selected_axioms'] = {name: reports[name] for name in expected}
        result['status'] = 'PASS'
        save()
        print(f'PASS: {len(result["modules"])} fresh modules, {len(expected)} exact axiom reports')
    except BaseException as exc:
        result['status'] = 'FAIL'; result['failure'] = str(exc); save(); raise

if __name__ == '__main__': main()
