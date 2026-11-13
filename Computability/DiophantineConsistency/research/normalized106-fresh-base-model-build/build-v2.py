#!/usr/bin/env python3
"""One sequential, source-snapshot diagnostic extension of the current14 base.

This records direct inputs and their companion/shadow states. It does not
authenticate all package-transitive, dynamic, or between-observation inputs.
"""
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import time
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
HERE = Path(__file__).resolve().parent
ROOT = next(p for p in HERE.parents if (p / 'lakefile.toml').is_file())
PREFLIGHT = HERE.parent / 'normalized106-current14-sixteen-source-preflight/preflight.py'
PINNED = HERE.parent / 'normalized106-current14-sixteen-source-preflight/result.json'
BASE = Path('/tmp/current14-standard-fresh-build-20261104/lib')
PKG = Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
LEAN = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
TOOL = LEAN.parent.parent / 'lib/lean'
OUT = Path('/tmp/normalized106-fresh-model-build-v2-20261105')
SUFFIXES = ('.olean', '.olean.private', '.olean.server', '.ir', '.ilean',
            '.olean.hash', '.olean.private.hash', '.olean.server.hash', '.ir.hash', '.ilean.hash')

def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def need(condition, message):
    if not condition:
        raise RuntimeError(message)

def save():
    t = OUT / 'state.tmp'
    t.write_text(json.dumps(state, indent=2, sort_keys=True) + '\n')
    t.replace(OUT / 'state.json')

def preflight(label):
    f = OUT / (label + '.json')
    e = OUT / (label + '.stderr')
    with f.open('x') as stdout, e.open('x') as stderr:
        p = subprocess.run([sys.executable, '-I', '-S', '-B', str(PREFLIGHT)],
                           cwd=ROOT, stdout=stdout, stderr=stderr, timeout=600)
    need(p.returncode == 0 and not e.read_bytes(), 'preflight failed: ' + label)
    value = json.loads(f.read_text())
    need(value == pinned, 'preflight differs from pinned receipt: ' + label)
    return sha(f)

def scan(names):
    result = {}
    for name in names:
        stem = Path(*name.split('.'))
        for root in roots:
            for suffix in SUFFIXES:
                p = root / (str(stem) + suffix)
                if os.path.lexists(p):
                    need(p.is_file(), 'broken object: ' + str(p))
                    result[str(p)] = {'realpath': str(p.resolve()), 'sha256': sha(p)}
                else:
                    result[str(p)] = None
    return result

def run(label, command, env):
    f = OUT / 'logs' / (label + '.txt')
    t = time.monotonic()
    with f.open('x') as log:
        proc = subprocess.run(command, cwd=OUT / 'src', env=env, stdout=log,
                              stderr=subprocess.STDOUT)
    return {'command': command, 'exit': proc.returncode,
            'seconds': round(time.monotonic() - t, 3), 'log': str(f),
            'log_sha256': sha(f)}

need(not OUT.exists(), 'refusing existing output')
OUT.mkdir()
(OUT / 'src').mkdir()
(OUT / 'lib').mkdir()
(OUT / 'logs').mkdir()
state = {'status': 'RUNNING', 'records': [], 'driver_sha256': sha(__file__),
         'scope': 'Source snapshot and direct dependency/companion/shadow observations; '
                  'package-transitive, dynamic, toolchain and between-observation ancestry inherited. '
                  'Timeout and Lean heap caps apply per process; no group-RSS or host-memory enforcement.'}
roots = (OUT / 'lib', PKG, TOOL)
env = dict(os.environ, LEAN_PATH=':'.join(map(str, roots[:2])), LEAN_NUM_THREADS='1')
for key in ('LEAN_SRC_PATH', 'LEAN_SYSROOT', 'LD_LIBRARY_PATH', 'LD_PRELOAD', 'LD_AUDIT'):
    env.pop(key, None)
timeout = ['/usr/bin/timeout', '--foreground', '--signal=TERM', '--kill-after=5s', '180s',
           '/usr/bin/ionice', '-c', '3', '/usr/bin/nice', '-n', '19', str(LEAN), '-M2800', '-j1',
           '-DElab.async=false']
save()
try:
    pinned = json.loads(PINNED.read_text())
    need(sha(PINNED) == 'f159489a58b1804d327a35b98ae75e64d746efe4605de0ce8a25ef3d92ca70b2', 'preflight receipt drift')
    state['preflight_before_sha256'] = preflight('preflight-before')
    # Lean resolves at the namespace root. Make one combined project tree;
    # each pre-existing file is a symlink to the authenticated base and new
    # output paths are required to be absent. No base object is written.
    base_links = {}
    for source in sorted(BASE.rglob('*')):
        target = OUT / 'lib' / source.relative_to(BASE)
        need(not source.is_symlink(), 'symlink in base tree: ' + str(source))
        if source.is_dir():
            target.mkdir(parents=True, exist_ok=True)
        else:
            need(source.is_file(), 'non-file in base tree: ' + str(source))
            target.parent.mkdir(parents=True, exist_ok=True)
            target.symlink_to(source)
            base_links[str(target)] = str(source)
    state['base_symlink_count'] = len(base_links)
    order = pinned['extension_order']
    need(len(order) == len(set(order)) == 16, 'unexpected extension')
    sources = pinned['project_sources']
    snapshot = {}
    for name in order:
        src = ROOT / sources[name]['source']
        dst = OUT / 'src' / (name.replace('.', '/') + '.lean')
        dst.parent.mkdir(parents=True, exist_ok=True)
        need(sha(src) == sources[name]['source_sha256'], 'source mismatch ' + name)
        shutil.copyfile(src, dst)
        snapshot[name] = sha(dst)
    client = OUT / 'src/FreshModel106.lean'
    shutil.copyfile(HERE / 'FreshModel106.lean', client)
    snapshot['FreshModel106'] = sha(client)
    state['snapshot'] = snapshot
    save()
    for index, name in enumerate(order + ['FreshModel106']):
        need(shutil.disk_usage(OUT).free >= 5_000_000_000, 'less than 5 GB free')
        source = OUT / 'src' / (name.replace('.', '/') + '.lean')
        expected = set(sources[name]['imports']) if name in sources else {
            'DiophantineConsistency.ModelArithmetic', 'DiophantineConsistency.ModelCarrierScaled',
            'DiophantineConsistency.ModelCarrierSyntax', 'DiophantineConsistency.HACurrentEquation2011',
            'DiophantineConsistency.IPRAExpressionNative', 'DiophantineConsistency.IPRAStandardTheory'}
        need(sha(source) == snapshot[name], 'snapshot drift ' + name)
        label = f'{index:02d}-{name.replace(".", "_")}'
        dep = run(label + '-deps', timeout + ['--deps', str(source)], env)
        need(dep['exit'] == 0, 'lean --deps failed ' + name)
        deps = {}
        for line in Path(dep['log']).read_text().splitlines():
            q = Path(line)
            need(q.is_absolute() and q.is_file() and q.suffix == '.olean', 'bad dependency ' + line)
            hits = [r for r in roots if q.is_relative_to(r)]
            need(len(hits) == 1, 'dependency outside roots ' + line)
            module = str(q.relative_to(hits[0]))[:-6].replace('/', '.')
            need(module not in deps or deps[module] == str(q), 'duplicate dependency provider ' + module)
            deps[module] = str(q)
        need(set(deps) - {'Init'} == expected - {'Init'}, 'declared dependency mismatch ' + name)
        for module, path in deps.items():
            if module in order:
                need(Path(path).is_relative_to(OUT / 'lib') and not Path(path).is_symlink(), 'extension fallback ' + module)
            elif module in sources:
                need(Path(path).is_relative_to(OUT / 'lib') and Path(path).is_symlink()
                     and Path(path).resolve().is_relative_to(BASE), 'base fallback ' + module)
        guard = scan(deps)
        obj = OUT / 'lib' / (name.replace('.', '/') + '.olean')
        obj.parent.mkdir(parents=True, exist_ok=True)
        need(not obj.exists(), 'preexisting object ' + name)
        comp = run(label + '-compile', timeout + ['--root=' + str(OUT / 'src'), str(source), '-o', str(obj)], env)
        text = Path(comp['log']).read_text()
        reports = re.findall(r"^'[^']+' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", text, re.M | re.S)
        record = {'module': name, 'source_sha256': sha(source), 'deps_run': dep, 'dependencies': deps,
                  'guard': guard, 'compile': comp, 'object_sha256': sha(obj) if obj.is_file() else None,
                  'axiom_reports': reports}
        state['records'].append(record)
        save()
        need(comp['exit'] == 0 and obj.is_file(), 'compile failed ' + name)
        need(not re.search(r'(?m)^.*(?:error:|error\([^)]*\):)|\bsorryAx\b', text), 'compile errors ' + name)
        need(sha(source) == snapshot[name] and scan(deps) == guard, 'input drift ' + name)
        if name == 'FreshModel106':
            need(len(reports) == 3, 'unexpected endpoint reports')
            for report in reports:
                need(not ({x.strip() for x in report.split(',') if x.strip()} -
                          {'propext', 'Classical.choice', 'Quot.sound'}), 'unexpected endpoint axiom')
        print('PASS', index + 1, name, flush=True)
    for name, h in snapshot.items():
        need(sha(OUT / 'src' / (name.replace('.', '/') + '.lean')) == h, 'final snapshot drift ' + name)
    for record in state['records']:
        need(scan(record['dependencies']) == record['guard'], 'final dependency drift ' + record['module'])
        need(sha(OUT / 'lib' / (record['module'].replace('.', '/') + '.olean')) == record['object_sha256'],
             'final object drift ' + record['module'])
    for target, source in base_links.items():
        p = Path(target)
        need(p.is_symlink() and str(p.resolve()) == source, 'base link drift ' + target)
    state['preflight_after_sha256'] = preflight('preflight-after')
    need(sha(__file__) == state['driver_sha256'], 'driver drift')
    state['status'] = 'PASS'
    save()
    print('PASS all 16 modules and client', flush=True)
except BaseException as e:
    state.update(status='FAILED', failure=repr(e))
    save()
    print('FAILED', repr(e), flush=True)
    raise
