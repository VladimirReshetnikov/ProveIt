"""Independent two-leaf replay, with no dependency builds or shared writes."""
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import time

ROOT = Path('/home/codex/.codex/worktrees/46be/Proofs')
REV = ROOT / 'Computability/DiophantineConsistency/reviews'
PINS = {
    'validator-source-derivation222-cache.json': '68c4efd389e168c6991282380c1aaa4c1a449c107c331fe18e3623754e1d7d6d',
    'validator-source-derivation222-replay.json': 'd688e71398add24dc4e54cdb2ba002d45524c3fbe2af324bc2d95f411f4e195c',
    'validator-source-derivation222-author.md': '5e40bdc7c7e1d4f59e9259f3e45bd31289e62e28d26ef499f6f1e1239ba2b176',
    'validator-source-derivation222-author-replay/FILES.json': '35842d9979b8911f73b51c9c9dec8dc9a5563f4665092d80df6cb406b86a7d8d',
}
OBS = []

def require(ok, msg):
    if not ok:
        raise RuntimeError(msg)

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def observe(path, expected, role):
    actual = sha(path)
    require(actual == expected, 'Changed '+role+': '+str(path))
    OBS.append({'path': str(path), 'sha256': actual, 'role': role})

def strip_comments(text):
    result, depth, i = [], 0, 0
    while i < len(text):
        if text.startswith('/-', i):
            depth += 1
            result.extend('  ')
            i += 2
        elif depth and text.startswith('-/', i):
            depth -= 1
            result.extend('  ')
            i += 2
        elif not depth and text.startswith('--', i):
            end = text.find('\n', i)
            end = len(text) if end < 0 else end
            result.extend(' '*(end-i))
            i = end
        else:
            result.append(text[i] if not depth or text[i] == '\n' else ' ')
            i += 1
    require(depth == 0, 'Unclosed comment')
    return ''.join(result)

def imports(path):
    text = strip_comments(Path(path).read_text())
    result = [] if re.search(r'^\s*prelude\s*$', text, re.M) else ['Init']
    for line in re.findall(r'^\s*(?:(?:public|private|meta)\s+)*import\s+([^\n]+)', text, re.M):
        result.extend(re.findall(r'[\w.]+', line))
    return list(dict.fromkeys(result))

for name, h in PINS.items():
    observe(REV/name, h, 'frozen author record')
data = json.loads((REV/'validator-source-derivation222-cache.json').read_text())
author = json.loads((REV/'validator-source-derivation222-replay.json').read_text())
manifest = json.loads((REV/'validator-source-derivation222-author-replay/FILES.json').read_text())
for r in manifest:
    observe(REV/'validator-source-derivation222-author-replay'/r['path'], r['sha256'], 'author bundle')
for r in data['inherited_observations']:
    observe(r['path'], r['sha256'], 'inherited authentication')

names = {r['module'] for r in data['modules']}
external_names = {r['module'] for r in data['external']}
require(len(names) == 164 and len(external_names) == 40, 'Closure counts')
require(sum(n.startswith('Foundation.') for n in names) == 117, 'Foundation count')
require(sum(len(r['objects']) for r in data['modules']) == 515, 'Artifact count')
for r in data['modules']:
    observed_imports = imports(r['source'])
    require(observed_imports == r['imports'], 'Import header: '+r['module'])
    require(set(observed_imports) <= names | external_names, 'Unlisted dependency')

def recheck():
    for name, h in PINS.items():
        observe(REV/name, h, 'author record')
    for k in ('compiler', 'manifest', 'toolchain'):
        observe(data[k], data[k+'_sha256'], k)
    for r in data['parent_receipts']:
        observe(r['path'], r['sha256'], 'parent receipt')
    for r in data['modules']:
        observe(r['source'], r['source_sha256'], 'cached source')
        for o in r['objects']:
            observe(o['path'], o['sha256'], 'cached artifact')
    for r in data['external']:
        observe(r['path'], r['sha256'], 'external boundary')

recheck()
require(shutil.disk_usage('/tmp').free >= 512*1024**2, '512MiB reserve')
out = Path(tempfile.mkdtemp(prefix='validator-source-derivation222-peer-'))
lib = out/'lib'
for r in data['modules']:
    stem = lib/r['module'].replace('.', '/')
    stem.parent.mkdir(parents=True, exist_ok=True)
    for o in r['objects']:
        path = Path(o['path'])
        suffix = path.name[len(r['module'].rsplit('.',1)[-1]):]
        Path(str(stem)+suffix).symlink_to(path)
shutil.copy2(__file__, out/'driver.py')
shutil.copy2(REV/'validator-source-derivation222-cache.json', out/'inputs.json')
env = dict(os.environ, LEAN_PATH=str(lib)+':'+data['lean_path'].split(':',1)[1], LEAN_NUM_THREADS='1')
env.pop('LEAN_SRC_PATH', None)
state = {'status': 'RUNNING', 'private': str(out), 'driver': {'path': str(out/'driver.py'), 'sha256': sha(__file__)},
         'inputs': {'path': str(out/'inputs.json'), 'sha256': sha(out/'inputs.json')},
         'scope': 'Independent fresh main/check only; authenticated cached prerequisites and explicit package boundaries reused.',
         'counts': data['counts'], 'LEAN_PATH': env['LEAN_PATH'], 'records': []}

def save():
    state['observation_count'] = len(OBS)
    (out/'state.json').write_text(json.dumps(state, indent=2)+'\n')
    (out/'observations.json').write_text(json.dumps(OBS, indent=2)+'\n')

save()
for a in author['completed']:
    n = a['module']
    require(n in ['ZFCinPA.ValidatorSourceDerivation222','ZFCinPA.ValidatorSourceDerivation222Checks'], 'Unexpected target')
    p = Path(a['source'])
    observe(p, a['source_sha256'], 'target before compile')
    code = strip_comments(p.read_text())
    require(not re.search(r'\b(sorry|native_decide|axiom)\b', code), 'Proof shortcut')
    require(set(imports(p)) <= names | external_names | {'ZFCinPA.ValidatorSourceDerivation222'}, 'Target imports')
    snapshot = out/p.name
    shutil.copy2(p, snapshot)
    target = lib/(n.replace('.', '/')+'.olean')
    require(not target.exists() and not target.is_symlink(), 'Fresh output must be absent')
    target.parent.mkdir(parents=True, exist_ok=True)
    require(shutil.disk_usage('/tmp').free >= 512*1024**2, '512MiB reserve')
    recheck()
    log, timing = out/(n+'.log'), out/(n+'.time')
    cmd = [data['compiler'], '-M6000', '-j1', '-DElab.async=false', '-o', str(target), str(p)]
    print('START '+n, flush=True)
    start = time.monotonic()
    with log.open('w') as handle:
        run = subprocess.run(['/usr/bin/time','-v','-o',str(timing)]+cmd, cwd=ROOT, env=env,
                             stdout=handle, stderr=subprocess.STDOUT)
    r = {'module': n, 'source': {'path': str(p), 'sha256': sha(p)},
         'snapshot': {'path': str(snapshot), 'sha256': sha(snapshot)}, 'command': cmd,
         'exit_code': run.returncode, 'seconds': time.monotonic()-start,
         'log': {'path': str(log), 'sha256': sha(log)},
         'timing': {'path': str(timing), 'sha256': sha(timing)}}
    state['records'].append(r)
    state['status'] = 'RUNNING' if run.returncode == 0 else 'FAIL'
    save()
    observe(p, a['source_sha256'], 'target after compile')
    recheck()
    if run.returncode:
        save()
        raise SystemExit(run.returncode)
    require(target.is_file() and not target.is_symlink(), 'Regular target output')
    reports = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log.read_text(), re.S)
    require(all(set(re.findall(r'[\w.]+',ax)) <= {'propext','Classical.choice','Quot.sound'} for _,ax in reports), 'Unexpected axiom')
    r.update(object={'path': str(target), 'sha256': sha(target)},
             author_object=a['object'], matches_author=(sha(target)==a['object']['sha256']),
             axiom_reports=reports)
    require(r['matches_author'], 'Object differs from author')
    require(not re.search(r'\b(warning|error):', log.read_text()), 'Compiler diagnostic')
    save()
    print('PASS '+n+' '+str(round(r['seconds'],3))+' seconds; '+str(len(reports))+' reports', flush=True)
require(sum(len(r['axiom_reports']) for r in state['records']) == 17, 'Axiom report count')
state['status'] = 'PASS'
state['free_bytes_after'] = shutil.disk_usage('/tmp').free
save()
Path('/tmp/validator-source-derivation222-peer-latest').write_text(str(out)+'\n')
print('FINAL '+str(out), flush=True)
