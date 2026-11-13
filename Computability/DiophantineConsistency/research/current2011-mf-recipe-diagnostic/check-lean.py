#!/usr/bin/env python3
"""Check preliminary current2011 MF recipe identities."""
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
BUILD_PACKET = HERE.parent / 'normalized106-fresh-base-model-build'
CLIENT = Path('/tmp/normalized106-fresh-model-client-20261105')
PROVIDER = Path('/tmp/normalized106-fresh-model-build-v2-20261105')
PKG = Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
LEAN = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
PREFLIGHT = HERE.parent / 'normalized106-current14-sixteen-source-preflight/preflight.py'
PINNED = HERE.parent / 'normalized106-current14-sixteen-source-preflight/result.json'
OUT = Path('/tmp/current2011-mf-recipe-diagnostic-20261105')
ROOTS = (CLIENT, PROVIDER / 'lib', PKG, LEAN.parent.parent / 'lib/lean')
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
        for root in ROOTS:
            for suffix in SUFFIXES:
                p = root / (str(stem) + suffix)
                if os.path.lexists(p):
                    need(p.is_file(), 'broken input ' + str(p))
                    result[str(p)] = {'realpath': str(p.resolve()), 'sha256': sha(p)}
                else:
                    result[str(p)] = None
    return result

def check_provider():
    need(sha(CLIENT / 'state.json') == sha(BUILD_PACKET / 'attempt03/state.json'), 'client state changed')
    c = json.loads((CLIENT / 'state.json').read_text())
    need(c['status'] == 'PASS' and sha(CLIENT / 'FreshModel106.lean') == c['source_sha256']
         and sha(CLIENT / 'FreshModel106.olean') == c['object_sha256'], 'client object changed')
    need(sha(CLIENT / 'compile.txt') == c['runs'][1]['log_sha256'] and
         sha(CLIENT / 'deps.txt') == c['runs'][0]['log_sha256'], 'client logs changed')
    check_guard(c['direct_guard'])
    need(sha(PROVIDER / 'state.json') == c['provider_sha256'] == sha(BUILD_PACKET / 'attempt02/state.json'),
         'extension state changed')
    p = json.loads((PROVIDER / 'state.json').read_text())
    need(len(p['records']) == 17 and p['status'] == 'FAILED', 'unexpected extension state')
    for rec in p['records'][:16]:
        name = rec['module']
        need(rec['compile']['exit'] == 0 and
             sha(PROVIDER / 'src' / (name.replace('.', '/') + '.lean')) == rec['source_sha256'] and
             sha(PROVIDER / 'lib' / (name.replace('.', '/') + '.olean')) == rec['object_sha256'],
             'extension output changed ' + name)
        check_guard(rec['guard'])

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
         'scope': 'Direct, companion and point-in-time provider checks; complete package-transitive, '
                  'dynamic and between-observation ancestry inherited. Lean -M2800 and 180-second timeout; '
                  'no group-RSS or host-memory enforcement.'}
save()
try:
    state['preflight_before_sha256'] = preflight('preflight-before')
    check_provider()
    need(shutil.disk_usage(OUT).free >= 5_000_000_000, 'less than 5 GB free')
    source = OUT / 'CurrentMFRecipe.lean'
    shutil.copyfile(HERE / 'CurrentMFRecipe.lean', source)
    state['source_sha256'] = sha(source)
    env = dict(os.environ, LEAN_PATH=':'.join(map(str, ROOTS[:3])), LEAN_NUM_THREADS='1')
    for key in ('LEAN_SRC_PATH', 'LEAN_SYSROOT', 'LD_LIBRARY_PATH', 'LD_PRELOAD', 'LD_AUDIT'):
        env.pop(key, None)
    prefix = ['/usr/bin/timeout', '--foreground', '--signal=TERM', '--kill-after=5s', '180s',
              '/usr/bin/ionice', '-c', '3', '/usr/bin/nice', '-n', '19', str(LEAN), '-M2800', '-j1',
              '-DElab.async=false']
    commands = [prefix + ['--deps', str(source)],
                prefix + ['--root=' + str(OUT), str(source), '-o', str(OUT / 'CurrentMFRecipe.olean')]]
    state['runs'] = []
    for i, command in enumerate(commands):
        start = time.monotonic()
        log = OUT / ('deps.txt' if i == 0 else 'compile.txt')
        with log.open('x') as f:
            p = subprocess.run(command, cwd=OUT, env=env, stdout=f, stderr=subprocess.STDOUT)
        state['runs'].append({'command': command, 'exit': p.returncode,
                              'seconds': round(time.monotonic() - start, 3), 'log_sha256': sha(log)})
        save()
        need(p.returncode == 0, 'Lean command failed ' + str(i))
        if i == 0:
            actual = {}
            for line in log.read_text().splitlines():
                pth = Path(line)
                need(pth.is_absolute() and pth.is_file(), 'bad dependency ' + line)
                hits = [r for r in ROOTS if pth.is_relative_to(r)]
                need(len(hits) == 1 and line.endswith('.olean'), 'unexpected dependency root ' + line)
                name = str(pth.relative_to(hits[0]))[:-6].replace('/', '.')
                need(name not in actual or actual[name]['path'] == line, 'duplicate provider')
                actual[name] = {'path': line, 'realpath': str(pth.resolve()), 'sha256': sha(pth)}
            need(set(actual) - {'Init'} == {'FreshModel106'} and
                 actual['FreshModel106']['path'] == str(CLIENT / 'FreshModel106.olean'), 'unexpected imports')
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
    state['object_sha256'] = sha(OUT / 'CurrentMFRecipe.olean')
    need(sha(source) == state['source_sha256'], 'source drift')
    need(scan(state['dependencies']) == state['direct_guard'], 'direct input drift')
    check_provider()
    state['preflight_after_sha256'] = preflight('preflight-after')
    need(sha(__file__) == state['driver_sha256'], 'driver drift')
    state['status'] = 'PASS'
    save()
    print('PASS current2011 MF recipe identities', flush=True)
except BaseException as e:
    state.update(status='FAILED', failure=repr(e))
    save()
    print('FAILED', repr(e), flush=True)
    raise
