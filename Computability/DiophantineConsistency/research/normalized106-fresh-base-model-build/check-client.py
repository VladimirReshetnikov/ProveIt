#!/usr/bin/env python3
"""Check the corrected client against the 16 successful attempt-02 outputs."""
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
PROVIDER = Path('/tmp/normalized106-fresh-model-build-v2-20261105')
BASE = Path('/tmp/current14-standard-fresh-build-20261104/lib')
PKG = Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
LEAN = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
PREFLIGHT = HERE.parent / 'normalized106-current14-sixteen-source-preflight/preflight.py'
PINNED = HERE.parent / 'normalized106-current14-sixteen-source-preflight/result.json'
OUT = Path('/tmp/normalized106-fresh-model-client-20261105')
SUFFIXES = ('.olean', '.olean.private', '.olean.server', '.ir', '.ilean',
            '.olean.hash', '.olean.private.hash', '.olean.server.hash', '.ir.hash', '.ilean.hash')

def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def need(condition, message):
    if not condition:
        raise RuntimeError(message)

def save():
    p = OUT / 'state.tmp'
    p.write_text(json.dumps(state, indent=2, sort_keys=True) + '\n')
    p.replace(OUT / 'state.json')

def check_guard(guard):
    for raw, expected in guard.items():
        p = Path(raw)
        if expected is None:
            need(not os.path.lexists(p), 'unexpected input ' + raw)
        else:
            need(p.is_file() and str(p.resolve()) == expected['realpath'] and
                 sha(p) == expected['sha256'], 'changed input ' + raw)

def scan(names):
    result = {}
    for name in names:
        stem = Path(*name.split('.'))
        for root in (PROVIDER / 'lib', PKG, LEAN.parent.parent / 'lib/lean'):
            for suffix in SUFFIXES:
                p = root / (str(stem) + suffix)
                if os.path.lexists(p):
                    need(p.is_file(), 'broken object ' + str(p))
                    result[str(p)] = {'realpath': str(p.resolve()), 'sha256': sha(p)}
                else:
                    result[str(p)] = None
    return result

def check_provider():
    need(sha(PROVIDER / 'state.json') == provider_sha, 'provider state drift')
    need(producer['status'] == 'FAILED' and len(producer['records']) == 17, 'unexpected producer state')
    for record in producer['records'][:16]:
        name = record['module']
        need(record['compile']['exit'] == 0, 'failed module ' + name)
        need(sha(PROVIDER / 'src' / (name.replace('.', '/') + '.lean')) == record['source_sha256'],
             'source drift ' + name)
        need(sha(PROVIDER / 'lib' / (name.replace('.', '/') + '.olean')) == record['object_sha256'],
             'object drift ' + name)
        need(sha(record['compile']['log']) == record['compile']['log_sha256'] and
             sha(record['deps_run']['log']) == record['deps_run']['log_sha256'], 'log drift ' + name)
        check_guard(record['guard'])
    need(producer['records'][16]['module'] == 'FreshModel106' and
         producer['records'][16]['compile']['exit'] != 0, 'failed client evidence')
    for p in BASE.rglob('*'):
        if p.is_file():
            q = PROVIDER / 'lib' / p.relative_to(BASE)
            need(q.is_symlink() and q.resolve() == p, 'base link mismatch ' + str(q))

def preflight(label):
    with (OUT / (label + '.json')).open('x') as o, (OUT / (label + '.stderr')).open('x') as e:
        p = subprocess.run([sys.executable, '-I', '-S', '-B', str(PREFLIGHT)],
                           cwd=ROOT, stdout=o, stderr=e, timeout=600)
    need(p.returncode == 0 and not (OUT / (label + '.stderr')).read_bytes(), 'preflight failed')
    need(json.loads((OUT / (label + '.json')).read_text()) == json.loads(PINNED.read_text()), 'preflight differs')
    return sha(OUT / (label + '.json'))

need(not OUT.exists(), 'refusing existing output')
OUT.mkdir()
state = {'status': 'RUNNING', 'driver_sha256': sha(__file__),
         'scope': 'Checks recorded direct provider and base inventories, not complete package-transitive, '
                  'dynamic or between-observation ancestry. One Lean process, -M2800 and 180-second timeout; '
                  'no group-RSS or host-memory enforcement.'}
save()
try:
    provider_sha = sha(PROVIDER / 'state.json')
    producer = json.loads((PROVIDER / 'state.json').read_text())
    need(sha(PROVIDER / 'state.json') == sha(HERE / 'attempt02/state.json'), 'not the captured producer state')
    need(sha(HERE / 'build-v2.py') == producer['driver_sha256'], 'producer driver drift')
    state['provider_sha256'] = provider_sha
    state['preflight_before_sha256'] = preflight('preflight-before')
    check_provider()
    need(shutil.disk_usage(OUT).free >= 5_000_000_000, 'less than 5 GB free')
    source = OUT / 'FreshModel106.lean'
    shutil.copyfile(HERE / 'FreshModel106.lean', source)
    state['source_sha256'] = sha(source)
    env = dict(os.environ, LEAN_PATH=str(PROVIDER / 'lib') + ':' + str(PKG), LEAN_NUM_THREADS='1')
    for key in ('LEAN_SRC_PATH', 'LEAN_SYSROOT', 'LD_LIBRARY_PATH', 'LD_PRELOAD', 'LD_AUDIT'):
        env.pop(key, None)
    prefix = ['/usr/bin/timeout', '--foreground', '--signal=TERM', '--kill-after=5s', '180s',
              '/usr/bin/ionice', '-c', '3', '/usr/bin/nice', '-n', '19', str(LEAN), '-M2800', '-j1',
              '-DElab.async=false']
    commands = [prefix + ['--deps', str(source)],
                prefix + ['--root=' + str(OUT), str(source), '-o', str(OUT / 'FreshModel106.olean')]]
    state['runs'] = []
    for i, command in enumerate(commands):
        start = time.monotonic()
        log = OUT / ('deps.txt' if i == 0 else 'compile.txt')
        with log.open('x') as f:
            p = subprocess.run(command, cwd=OUT, env=env, stdout=f, stderr=subprocess.STDOUT)
        state['runs'].append({'command': command, 'exit': p.returncode,
                              'seconds': round(time.monotonic() - start, 3),
                              'log_sha256': sha(log)})
        save()
        need(p.returncode == 0, 'Lean command failed ' + str(i))
        if i == 0:
            actual = {}
            for line in log.read_text().splitlines():
                pth = Path(line)
                need(pth.is_absolute() and pth.is_file(), 'bad dependency ' + line)
                roots = [PROVIDER / 'lib', PKG, LEAN.parent.parent / 'lib/lean']
                matches = [r for r in roots if pth.is_relative_to(r)]
                need(len(matches) == 1, 'unexpected dependency root ' + line)
                name = str(pth.relative_to(matches[0]))[:-6].replace('/', '.')
                need(name not in actual or actual[name]['path'] == line, 'duplicate provider')
                actual[name] = {'path': line, 'realpath': str(pth.resolve()), 'sha256': sha(pth)}
            need(set(actual) - {'Init'} == {'DiophantineConsistency.ModelArithmetic',
                'DiophantineConsistency.ModelCarrierScaled', 'DiophantineConsistency.ModelCarrierSyntax',
                'DiophantineConsistency.HACurrentEquation2011', 'DiophantineConsistency.IPRAExpressionNative',
                'DiophantineConsistency.IPRAStandardTheory'}, 'unexpected client imports')
            for name, rec in actual.items():
                if name.startswith('DiophantineConsistency.'):
                    pth = Path(rec['path'])
                    need(pth.is_relative_to(PROVIDER / 'lib'), 'unexpected project provider ' + name)
                    if name in {r['module'] for r in producer['records'][:16]}:
                        need(not pth.is_symlink(), 'unexpected extension symlink ' + name)
                    else:
                        need(pth.is_symlink() and pth.resolve().is_relative_to(BASE), 'unexpected base provider ' + name)
            state['dependencies'] = actual
            state['direct_guard'] = scan(actual)
            save()
    text = (OUT / 'compile.txt').read_text()
    reports = re.findall(r"^'[^']+' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", text, re.M | re.S)
    need(len(reports) == 3 and not re.search(r'(?m)^.*(?:error:|error\([^)]*\):)|\bsorryAx\b', text), 'unexpected report or error')
    for report in reports:
        need(not ({x.strip() for x in report.split(',') if x.strip()} -
                  {'propext', 'Classical.choice', 'Quot.sound'}), 'unexpected axiom')
    state['axiom_reports'] = reports
    state['object_sha256'] = sha(OUT / 'FreshModel106.olean')
    need(sha(source) == state['source_sha256'], 'client source drift')
    need(scan(state['dependencies']) == state['direct_guard'], 'client input drift')
    check_provider()
    state['preflight_after_sha256'] = preflight('preflight-after')
    need(sha(__file__) == state['driver_sha256'], 'driver drift')
    state['status'] = 'PASS'
    save()
    print('PASS fresh-model endpoint', flush=True)
except BaseException as e:
    state.update(status='FAILED', failure=repr(e))
    save()
    print('FAILED', repr(e), flush=True)
    raise
