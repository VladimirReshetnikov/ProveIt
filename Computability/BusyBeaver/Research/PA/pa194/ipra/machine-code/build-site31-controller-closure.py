#!/usr/bin/env python3
"""Rebuild the controller's machine-source imports against the physical baseline."""
from pathlib import Path
import hashlib, json, os, re, shutil, subprocess, sys

repo, manifest, out, baseline = map(Path, sys.argv[1:5])
repo = repo.resolve()
records = json.loads(manifest.read_text())
by_module = {r['module']: r for r in records}
seen, order, used_base, used_source, external = set(), [], {}, {}, set()
def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()
def object_path(root, name):
    return root.joinpath(*name.split('.')).with_suffix('.olean')
def visit(name):
    if name in seen:
        return
    seen.add(name)
    obj = object_path(out, name)
    if obj.exists():
        return
    obj = object_path(baseline, name)
    if obj.exists():
        for p in [obj, Path(str(obj)+'.private'), Path(str(obj)+'.server')]:
            if p.exists(): used_base[str(p)] = digest(p)
        return
    rec = by_module.get(name)
    if rec is None:
        if name.startswith(('PA194', 'M6.', 'Packed', 'Configuration')):
            raise SystemExit('Missing machine-specific source or baseline object: '+name)
        external.add(name)
        return
    source = Path(rec['source']).resolve()
    if not source.is_relative_to(repo) or not source.is_file():
        raise SystemExit('Source outside repository or missing: '+str(source))
    before = digest(source)
    if before != rec['sha256']:
        raise SystemExit('Source hash differs from closure manifest: '+str(source))
    used_source[str(source)] = before
    for line in source.read_text().splitlines():
        match = re.match(r'^\s*import\s+([^/-]+)', line)
        if match:
            for dep in match.group(1).split():
                visit(dep)
    order.append((name, source))
for target in ('PA194SourceControllerStep', 'PA194SourceRegisterRelation', 'PA194SourcePCBound'):
    visit(target)
for name, source in order:
    dest = out.joinpath(*name.split('.')).with_suffix('.lean')
    dest.parent.mkdir(parents=True, exist_ok=True)
    if dest.exists():
        raise SystemExit('Refusing to overwrite staged source: '+str(dest))
    shutil.copyfile(source, dest)
    obj = object_path(out, name)
    if obj.exists():
        raise SystemExit('Refusing to overwrite staged object: '+str(obj))
    print('Checking controller dependency', name, flush=True)
    proc = subprocess.run(['lake', 'env', 'env', 'LEAN_PATH='+os.environ['LEAN_PATH'], 'lean', '-M6000', '-j1', '-R', str(out), '-o', str(obj), str(dest)], cwd=repo, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    print(proc.stdout, end='', flush=True)
    if proc.returncode or 'sorryAx' in proc.stdout:
        raise SystemExit(f'Controller dependency failed: {name} (exit {proc.returncode})')
for name, before in {**used_base, **used_source}.items():
    if digest(Path(name)) != before:
        raise SystemExit('Input changed during controller build: '+name)
(out/'site31-controller-closure-receipt.json').write_text(json.dumps({'source_sha256':used_source, 'baseline_object_sha256':used_base, 'external_modules':sorted(external), 'build_order':[x[0] for x in order]}, indent=2)+'\n')
print(f'Built {len(order)} controller dependencies against the physical baseline; {len(used_base)} baseline objects hashed.', flush=True)
