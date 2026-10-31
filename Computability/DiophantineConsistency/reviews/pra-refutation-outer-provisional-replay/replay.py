#!/usr/bin/env python3
"""Replay the fixed-refutation outer layer over pinned mixed parent objects."""
from pathlib import Path
import hashlib, json, os, re, subprocess, tempfile, time

ROOT = Path(__file__).resolve().parents[4]
SRC = ROOT / 'Computability/DiophantineConsistency/Lean/DiophantineConsistency'
PACKET = Path(__file__).resolve().parent
PARENT = Path('/tmp/pra-refutation-outer-dev')
FOUNDATION = Path('/tmp/pra-setshift-coherent/lib/Foundation')
BASE = Path('/tmp/pra-witness-fold-refresh-6xz3_lem/state.json')
NAMES = ['PRAWitnessClosedExistential', 'PRAWitnessBoundCertificate',
         'PRAWitnessRefutationOuter', 'PRAWitnessRefutationOuterChecks',
         'PRAWitnessZFCCertificate', 'PRAWitnessZFCCertificateChecks']
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
manifest = json.loads((PACKET / 'manifest.json').read_text())
work = Path(tempfile.mkdtemp(prefix='pra-refutation-outer-'))
lib = work / 'lib'; dest = lib / 'DiophantineConsistency'
dest.mkdir(parents=True); logs = work / 'logs'; logs.mkdir()
for path in (PARENT / 'DiophantineConsistency').glob('*.olean'):
    if path.stem not in NAMES:
        (dest / path.name).symlink_to(path.resolve())
(lib / 'ZFCinPA').symlink_to((PARENT / 'ZFCinPA').resolve(), target_is_directory=True)
(lib / 'Foundation').symlink_to(FOUNDATION.resolve(), target_is_directory=True)
lean = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
base = json.loads(BASE.read_text())['LEAN_PATH']
env = dict(os.environ, LEAN_PATH=str(lib) + ':' + base, LEAN_NUM_THREADS='1')
env.pop('LEAN_SRC_PATH', None)
state = {'status': 'RUNNING', 'root': str(work), 'parent': str(PARENT),
         'manifest_sha256': sha(PACKET / 'manifest.json'), 'records': [],
         'scope': 'Pinned mixed project, ZFC and Foundation parent; transitive source ancestry inherited.'}

def save():
    p = work / 'state.tmp'; p.write_text(json.dumps(state, indent=2) + '\n'); p.replace(work / 'state.json')

def audit():
    assert sha(PACKET / 'manifest.json') == state['manifest_sha256']
    assert sha(lean) == manifest['lean_sha256']
    assert all(sha(SRC / (n + '.lean')) == h for n, h in manifest['sources'].items())
    assert all(sha(PARENT / p) == h for p, h in manifest['parent_objects'].items())
    assert all(sha(ROOT / p) == h for p, h in manifest['observed_sources'].items())

save(); print('ROOT', work, flush=True)
try:
    audit()
    for name in NAMES:
        state['module'] = name; save()
        src = SRC / (name + '.lean'); out = dest / (name + '.olean'); log = logs / (name + '.log')
        (logs / (name + '.lean')).write_bytes(src.read_bytes())
        start = time.monotonic()
        with log.open('w') as f:
            result = subprocess.run([str(lean), '-M6000', '-j1', '-DElab.async=false',
                                     str(src), '-o', str(out)], cwd=ROOT, env=env,
                                    stdout=f, stderr=subprocess.STDOUT)
        row = {'module': name, 'exit': result.returncode, 'seconds': time.monotonic()-start,
               'source_sha256': sha(src), 'object_sha256': sha(out) if out.exists() else None,
               'log_sha256': sha(log)}
        state['records'].append(row); save()
        assert result.returncode == 0 and not re.search(r'\b(?:warning|error|sorryAx)\b', log.read_text())
        assert sha(src) == manifest['sources'][name]
        if name.endswith('Checks'):
            groups = re.findall(r'depends on axioms:\s*\[([^]]*)\]', log.read_text(), re.S)
            assert groups and all(not ({x.strip() for x in g.split(',') if x.strip()} -
                                        {'propext', 'Classical.choice', 'Quot.sound'}) for g in groups)
        print('PASS', name, flush=True)
    audit(); state.update(status='PASS', module=None); save(); print('PASS', work, flush=True)
except BaseException as exc:
    state.update(status='FAILED', failure=repr(exc)); save(); raise
