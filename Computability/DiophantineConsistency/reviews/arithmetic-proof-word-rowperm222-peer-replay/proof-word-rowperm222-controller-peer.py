from pathlib import Path
import hashlib, json, os, re, shutil, subprocess, tempfile, time

ROOT = Path('/home/codex/.codex/worktrees/46be/Proofs')
REV = ROOT / 'Computability/DiophantineConsistency/reviews'
AUTHOR = REV / 'arithmetic-proof-word-rowperm222-replay.json'
AUTHOR_SHA = '841882f09456821f479335d647e6a6dad643d00081efa4095aa69c81198f88e1'
RESERVE = 512 * 1024**2
def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def rec(p):
    return {'path': str(p), 'sha256': sha(p)}
def verify(r):
    assert sha(r['path']) == r['sha256'], r['path']
def save(p, value):
    p.write_text(json.dumps(value, indent=2) + '\n')
def imports(p):
    lines = re.findall(r'^(?:(?:public|private|meta)\s+)*import\s+([^\n]+)', Path(p).read_text(), re.M)
    return list(dict.fromkeys(['Init'] + [n for line in lines for n in line.split('--', 1)[0].split()]))

assert sha(AUTHOR) == AUTHOR_SHA
a = json.loads(AUTHOR.read_text())
assert a['status'] == 'PASS'
verify(a['inputs']); verify(a['bundle_manifest'])
i = json.loads(Path(a['inputs']['path']).read_text())
mods = i['modules']
names = {m['module'] for m in mods}
assert len(mods) == 132 and len(names) == 132
assert sum(m['module'].startswith('Foundation.') for m in mods) == 95
assert sum(len(m['objects']) for m in mods) == 417
external = sorted({n for m in mods for n in m['imports'] if n not in names})
assert len(external) == 38
pins = [*i['pins'], rec(AUTHOR), a['inputs'], a['bundle_manifest'], rec(__file__),
        rec(REV / 'arithmetic-proof-word-rowperm222-author.md')]
manifest = json.loads(Path(a['bundle_manifest']['path']).read_text())
for f in manifest['files']:
    pins.append({'path': str(Path(a['bundle_manifest']['path']).parent / f['path']), 'sha256': f['sha256']})
    pins.append({'path': f['original'], 'sha256': f['sha256']})
for m in mods:
    assert imports(m['source']) == list(dict.fromkeys(m['imports'])), m['module']
    pins.append({'path': m['source'], 'sha256': m['source_sha256']})
    pins.extend(m['objects'])
for r in a['records']:
    for key in ['source', 'snapshot', 'log', 'timing', 'object']:
        pins.append(r[key])
assert len(a['records']) == 2
targets = {r['module'] for r in a['records']}
assert not (targets & names)
for pin in pins:
    verify(pin)
assert shutil.disk_usage('/tmp').free >= RESERVE
p = Path(tempfile.mkdtemp(prefix='proof-word-rowperm222-controller-peer-'))
lib = p / 'lib'; lib.mkdir()
for m in mods:
    for o in m['objects']:
        dest = lib / Path(*m['module'].split('.')[:-1]) / Path(o['path']).name
        dest.parent.mkdir(parents=True, exist_ok=True)
        assert not dest.exists()
        dest.symlink_to(o['path'])
search = i['lean_path'].split(':')[1:]
assert all('/.lake/packages/' in x or x.endswith('/lib/lean') and '/.elan/toolchains/' in x for x in search)
env = dict(os.environ, LEAN_PATH=':'.join([str(lib), *search]), LEAN_NUM_THREADS='1')
env.pop('LEAN_SRC_PATH', None)
inputs = dict(author=rec(AUTHOR), author_inputs=a['inputs'], pins=pins, modules=mods,
              external_imports=external, lean_path=env['LEAN_PATH'], compiler=i['compiler'],
              counts=i['counts'], inherited_pin_observations=len(i['pins']))
save(p / 'inputs.json', inputs)
Path('/tmp/proof-word-rowperm222-controller-peer-location.txt').write_text(str(p))
state = dict(status='RUNNING', inputs=rec(p / 'inputs.json'), driver=rec(__file__),
             private=str(p), records=[], pin_observations=len(pins))
save(p / 'RESULT.json', state)
print(json.dumps({'status': 'PREPARED', 'private': str(p), 'pins': len(pins)}), flush=True)
for expected in a['records']:
    assert shutil.disk_usage(p).free >= RESERVE
    verify(expected['source'])
    src = Path(expected['source']['path']); name = src.stem
    snap = p / src.name; shutil.copyfile(src, snap)
    out = lib / Path(*expected['module'].split('.')).with_suffix('.olean')
    assert not out.exists() and not out.is_symlink()
    out.parent.mkdir(parents=True, exist_ok=True)
    log = p / (name + '.log'); timing = p / (name + '.time')
    cmd = [i['compiler']['path'], '-M6000', '-j1', '-DElab.async=false', '-o', str(out), str(src)]
    begin = time.monotonic()
    with log.open('w') as stream:
        code = subprocess.run(['/usr/bin/time', '-v', '-o', str(timing), *cmd], cwd=ROOT,
                              env=env, stdout=stream, stderr=subprocess.STDOUT).returncode
    r = dict(module=expected['module'], source=rec(src), snapshot=rec(snap), command=cmd,
             seconds=time.monotonic()-begin, exit_code=code, log=rec(log), timing=rec(timing))
    state['records'].append(r); save(p / 'RESULT.json', state)
    if code:
        state['status'] = 'FAILED'; save(p / 'RESULT.json', state)
        print(log.read_text()); raise SystemExit(code)
    assert sha(src) == sha(snap) and not out.is_symlink()
    r['object'] = rec(out); r['matches_author'] = sha(out) == expected['object']['sha256']
    text = log.read_text()
    assert not re.search(r'\b(?:warning|error):', text)
    reports = re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", text)
    r['axiom_reports'] = reports
    assert len(reports) == len(expected['axiom_reports'])
    for title, ax in reports:
        assert set(re.findall(r'[A-Za-z][A-Za-z.]*', ax)) <= {'propext', 'Classical.choice', 'Quot.sound'}
    save(p / 'RESULT.json', state)
    print(json.dumps(r), flush=True)
for pin in pins:
    verify(pin)
assert sum(len(r['axiom_reports']) for r in state['records']) == 6
assert all(r['matches_author'] for r in state['records'])
state['status'] = 'PASS'; state['free_bytes_final'] = shutil.disk_usage(p).free
save(p / 'RESULT.json', state)
print(json.dumps({'status': 'PASS', 'result': str(p / 'RESULT.json')}), flush=True)
