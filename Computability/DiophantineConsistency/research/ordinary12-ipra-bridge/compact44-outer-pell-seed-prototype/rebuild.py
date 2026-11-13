#!/usr/bin/env python3
"""Rebuild the three seed modules against the checked compact project overlay."""
import hashlib, json, os, shutil, subprocess, tempfile, time
from pathlib import Path

HERE = Path(__file__).resolve().parent
OBS = HERE / 'observations/rebuild-attempt01'
REPO = HERE.parents[2] / 'Lean/DiophantineConsistency'
PROVIDER = Path('/tmp/compact44-constructed-rank-author-g2doc30c')
BASE = Path('/tmp/ipra-compact-word-cell-author-01/lib')
PACKING = Path('/tmp/ipra-compact44-symbolic-unit-join/lib')
HALT = Path('/tmp/ipra-halt-dimensions-explore-02/lib')
PACKAGE = Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
LEAN = '/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean'
NAMES = ['ArithmeticOuterSeed', 'ArithmeticPellSquaredSeed', 'ArithmeticPellAuxiliarySeed']
SUFFIXES = ['.olean', '.olean.private', '.olean.server', '.ir', '.ilean',
            '.olean.hash', '.olean.private.hash', '.olean.server.hash', '.ir.hash', '.ilean.hash']

def digest(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def inventory(p):
    return {q.name: digest(q) for q in sorted(p.iterdir()) if q.is_file()}

if OBS.exists():
    raise RuntimeError('refusing to overwrite prior observations')
if shutil.disk_usage('/tmp').free < 4 * 1024**3:
    raise RuntimeError('less than 4 GiB free')
OBS.mkdir(parents=True)
project = PROVIDER / 'DiophantineConsistency'
before = inventory(project)
for name in NAMES:
    if (project / (name + '.olean')).exists():
        raise RuntimeError('expected a missing project object: ' + name)
sources = {name: digest(REPO / (name + '.lean')) for name in NAMES}
run = Path(tempfile.mkdtemp(prefix='compact44-outer-pell-rebuild-author-'))
dst = run / 'DiophantineConsistency'
dst.mkdir()
for entry in project.iterdir():
    if entry.is_file():
        (dst / entry.name).symlink_to(entry.resolve())
for name in NAMES:
    shutil.copyfile(REPO / (name + '.lean'), dst / (name + '.lean'))
env = {'PATH': '/usr/bin:/bin', 'LEAN_NUM_THREADS': '1',
       'LEAN_PATH': ':'.join(map(str, [run, BASE, PACKING, HALT, PACKAGE]))}
steps = []
for name in NAMES:
    source = dst / (name + '.lean')
    obj = dst / (name + '.olean')
    deps = subprocess.run([LEAN, '--deps', str(source)], env=env,
                          capture_output=True, text=True, timeout=120)
    (OBS / (name + '.deps')).write_text(deps.stdout)
    (OBS / (name + '.deps.stderr')).write_text(deps.stderr)
    if deps.returncode or deps.stderr:
        raise RuntimeError('dependency scan failed: ' + name)
    guards = {}
    for line in deps.stdout.splitlines():
        path = Path(line)
        if not path.is_absolute() or not path.is_file() or path.suffix != '.olean':
            raise RuntimeError('invalid dependency: ' + line)
        for suffix in SUFFIXES:
            f = Path(str(path)[:-6] + suffix)
            guards[str(f)] = digest(f) if f.is_file() else None
    cmd = [LEAN, '-M3000', '-j1', '-DElab.async=false', f'--root={run}', str(source), '-o', str(obj)]
    start = time.monotonic()
    try:
        proc = subprocess.run(cmd, env=env, capture_output=True, text=True, timeout=240)
        code, log = proc.returncode, proc.stdout + proc.stderr
    except subprocess.TimeoutExpired as exc:
        code, log = None, str(exc)
    (OBS / (name + '.log')).write_text(log)
    after = {p: digest(p) if Path(p).is_file() else None for p in guards}
    steps.append({'module': name, 'command': cmd, 'exit_code': code,
                  'seconds': round(time.monotonic()-start, 3),
                  'source_sha256': digest(source), 'object_sha256': digest(obj) if obj.is_file() else None,
                  'guards_before': guards, 'guards_unchanged': guards == after})
    (OBS / 'terminal.json').write_text(json.dumps({'run': str(run), 'steps': steps, 'sources': sources}, indent=2) + '\n')
    if code != 0 or not obj.is_file() or guards != after or any(x in log for x in ('error:', 'warning:', 'sorryAx')):
        raise SystemExit(1)
    if inventory(project) != before or any(digest(REPO / (n + '.lean')) != h for n,h in sources.items()):
        raise RuntimeError('provider or source changed')
(OBS / 'provider.json').write_text(json.dumps({'project': before, 'unchanged': inventory(project) == before}, indent=2) + '\n')
print(json.dumps({'run': str(run), 'steps': [{k:s[k] for k in ('module','exit_code','seconds','object_sha256')} for s in steps]}))
