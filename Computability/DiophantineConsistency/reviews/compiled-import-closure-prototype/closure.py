#!/usr/bin/env python3
"""Conservative compiled-header closure survey; no source-build validation."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
READER = HERE / 'read_imports.lean'
LEAN = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
SUFFIXES = ('.olean', '.olean.private', '.olean.server', '.ir', '.ilean',
            '.olean.hash', '.olean.private.hash', '.olean.server.hash', '.ir.hash', '.ilean.hash')
NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*\Z")

def digest(path):
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(chunk)
    return h.hexdigest()

def inspect(path):
    if not os.path.lexists(path):
        return None
    if not path.is_file():
        raise RuntimeError(('broken or non-file companion', str(path)))
    before = path.stat()
    resolved = str(path.resolve(strict=True))
    value = digest(path)
    after = path.stat()
    fields = lambda s: (s.st_dev, s.st_ino, s.st_size, s.st_mtime_ns, s.st_ctime_ns)
    if fields(before) != fields(after) or str(path.resolve(strict=True)) != resolved:
        raise RuntimeError(('file changed during hashing', str(path)))
    return {'realpath': resolved, 'sha256': value}

def namespace_marker(root, top):
    directory, file = root / top, root / (top + '.olean')
    for p in (directory, file):
        if os.path.lexists(p) and not p.exists():
            raise RuntimeError(('broken namespace candidate', str(p)))
    return {'directory': str(directory.resolve()) if directory.is_dir() else None,
            'file': inspect(file)}

def resolve_module(name, roots, namespaces):
    if not NAME.fullmatch(name):
        raise RuntimeError(('unsupported module name', name))
    top = name.split('.')[0]
    if top not in namespaces:
        markers = [namespace_marker(root, top) for root in roots]
        selected = next((i for i, marker in enumerate(markers)
                         if marker['directory'] is not None or marker['file'] is not None), None)
        if selected is None:
            raise RuntimeError(('unknown namespace', top))
        namespaces[top] = {'selected': selected, 'markers': markers}
    return roots[namespaces[top]['selected']].joinpath(*name.split('.')).with_suffix('.olean')

def scan(root_olean):
    stem = str(root_olean)[:-6]
    return {stem + suffix: inspect(Path(stem + suffix)) for suffix in SUFFIXES}

def check_guard(guard):
    for p, expected in guard.items():
        if inspect(Path(p)) != expected:
            raise RuntimeError(('observed artifact changed', p))

def read_batch(paths, env):
    proc = subprocess.run([str(LEAN), '-j1', '--run', str(READER), *map(str, paths)],
                          env=env, capture_output=True, text=True, timeout=300)
    if proc.returncode != 0 or proc.stderr:
        raise RuntimeError(('Lean artifact reader failed', proc.returncode, proc.stdout, proc.stderr))
    lines = proc.stdout.splitlines()
    if len(lines) != len(paths):
        raise RuntimeError(('unexpected reader row count', len(paths), len(lines)))
    result = []
    for index, line in enumerate(lines):
        parts = line.split('\t')
        if len(parts) < 3 or parts[0] != 'OK' or parts[1] != str(index) or parts[2] not in ('true', 'false'):
            raise RuntimeError(('unexpected reader row', line))
        imports = parts[3:]
        if any(not NAME.fullmatch(name) for name in imports):
            raise RuntimeError(('unsupported imported name', imports))
        result.append({'is_module': parts[2] == 'true', 'imports': imports})
    return result

def collect(seeds, policy, *, max_modules=5000):
    roots = [Path(row['path']).resolve(strict=True) for row in policy['roots']]
    if not roots or len(set(roots)) != len(roots) or any(not p.is_dir() for p in roots):
        raise RuntimeError('missing, repeated or invalid search roots')
    roles = [row['role'] for row in policy['roots']]
    if any(not role for role in roles):
        raise RuntimeError('missing root role')
    baseline = {'reader': digest(READER), 'lean': digest(LEAN), 'driver': digest(Path(__file__))}
    env = dict(os.environ, LEAN_NUM_THREADS='1')
    for name in ('LEAN_PATH', 'LEAN_SRC_PATH', 'LEAN_SYSROOT', 'LD_LIBRARY_PATH', 'LD_PRELOAD', 'LD_AUDIT'):
        env.pop(name, None)
    namespaces, visited, guard = {}, {}, {}
    pending = list(dict.fromkeys(seeds))
    while pending:
        batch, queued = [], set()
        while pending and len(batch) < 32:
            name = pending.pop(0)
            if name in visited or name in queued:
                continue
            if len(visited) + len(batch) >= max_modules:
                raise RuntimeError(('module limit reached', max_modules))
            olean = resolve_module(name, roots, namespaces)
            companions = scan(olean)
            if companions[str(olean)] is None:
                raise RuntimeError(('selected namespace lacks object', name, str(olean)))
            for key, value in companions.items():
                if key in guard and guard[key] != value:
                    raise RuntimeError(('conflicting artifact observation', key))
                guard[key] = value
            batch.append((name, olean, companions)); queued.add(name)
        if not batch:
            continue
        paths, descriptors = [], []
        for name, olean, companions in batch:
            paths.append(olean); descriptors.append((name, 'olean'))
            ir = olean.with_suffix('.ir')
            if companions[str(ir)] is not None:
                paths.append(ir); descriptors.append((name, 'ir'))
        check_guard({str(path): guard[str(path)] for path in paths})
        results = read_batch(paths, env)
        check_guard({str(path): guard[str(path)] for path in paths})
        data = {name: {} for name, _, _ in batch}
        for (name, kind), result in zip(descriptors, results):
            data[name][kind] = result
        for name, olean, companions in batch:
            if data[name]['olean']['is_module']:
                for suffix in ('.private', '.server'):
                    if companions[str(olean) + suffix] is None:
                        raise RuntimeError(('missing module object part', name, suffix))
            deps = sorted({dep for row in data[name].values() for dep in row['imports']})
            visited[name] = {'root': namespaces[name.split('.')[0]]['selected'],
                             'role': roles[namespaces[name.split('.')[0]]['selected']],
                             'path': str(olean), 'imports': deps, 'headers': data[name]}
            pending.extend(dep for dep in deps if dep not in visited)
    check_guard(guard)
    for top, observation in namespaces.items():
        if [namespace_marker(root, top) for root in roots] != observation['markers']:
            raise RuntimeError(('namespace search changed', top))
    if baseline != {'reader': digest(READER), 'lean': digest(LEAN), 'driver': digest(Path(__file__))}:
        raise RuntimeError('reader, driver or compiler changed')
    return {'status': 'COMPILED_HEADER_SURVEY', 'seeds': seeds,
            'roots': [{'path': str(root), 'role': role} for root, role in zip(roots, roles)],
            'tool_sha256': baseline, 'modules': visited, 'artifacts': guard,
            'namespace_observations': namespaces,
            'scope': 'Conservative reachability from compiled .olean/.ir import headers under '
                     'namespace-first resolution and postchecked object/companion identities. '
                     'No source-to-object provenance, actual runtime load trace, transient '
                     'mutation exclusion or toolchain soundness is established.'}

def main():
    p = argparse.ArgumentParser()
    p.add_argument('--policy', type=Path, required=True)
    p.add_argument('--seed', action='append', required=True)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--max-modules', type=int, default=5000)
    args = p.parse_args()
    policy_hash = digest(args.policy)
    result = collect(args.seed, json.loads(args.policy.read_text()), max_modules=args.max_modules)
    if digest(args.policy) != policy_hash:
        raise RuntimeError('policy changed')
    result['policy_sha256'] = policy_hash
    with args.output.open('x') as f:
        json.dump(result, f, indent=2, sort_keys=True); f.write('\n')
    print(result['status'], len(result['modules']), digest(args.output), flush=True)

if __name__ == '__main__':
    main()
