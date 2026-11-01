#!/usr/bin/env python3
"""Join hash-matched strict cores and rebuild the exact refutation bound."""
from pathlib import Path
import hashlib, json, os, re, shutil, subprocess, tempfile, time

ROOT = Path(__file__).resolve().parents[4]
PACKET = Path(__file__).resolve().parent
M = json.loads((PACKET / 'manifest.json').read_text())
A, B = (Path(M[k]) for k in ('negative_root', 'positive_root'))
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
work = Path(tempfile.mkdtemp(prefix='pra-zfc-refutation-bound-'))
src = work / 'src/DiophantineConsistency'; src.mkdir(parents=True)
lib = work / 'lib'; dest = lib / 'DiophantineConsistency'; dest.mkdir(parents=True)
logs = work / 'logs'; logs.mkdir()
for n in M['order']:
    shutil.copyfile(PACKET / 'frozen' / (n + '.lean'), src / (n + '.lean'))
for n, record in M['project_objects'].items():
    parent = A if record['provider'] == 'negative' else B
    (dest / (n + '.olean')).symlink_to((parent / 'lib/DiophantineConsistency' / (n + '.olean')).resolve())
for ns in ['Foundation', 'ZFCinPA']:
    (lib / ns).symlink_to((A / 'lib' / ns).resolve(), target_is_directory=True)
base = json.loads(Path('/tmp/pra-witness-fold-refresh-6xz3_lem/state.json').read_text())['LEAN_PATH']
base = [x for x in base.split(':') if x.startswith('/home/codex/src/Proofs/.lake/packages/')
        or x.startswith('/home/codex/.elan/toolchains/')]
env = dict(os.environ, LEAN_PATH=str(lib)+':'+':'.join(base), LEAN_NUM_THREADS='1')
env.pop('LEAN_SRC_PATH', None)
state = {'status':'RUNNING','root':str(work),'manifest_sha256':sha(PACKET/'manifest.json'),
         'records':[], 'scope':M['scope'], 'package_path':base}

def save():
    p=work/'state.tmp';p.write_text(json.dumps(state,indent=2)+'\n');p.replace(work/'state.json')

def audit():
    assert sha(PACKET/'manifest.json') == state['manifest_sha256']
    assert all(sha(Path(p)/'state.json') == h for p,h in M['parent_states'].items())
    assert all(sha(src/(n+'.lean')) == h for n,h in M['source_sha256'].items())
    assert all(sha(ROOT/p) == h for p,h in M['observed_sources'].items())
    for n, record in M['project_objects'].items():
        assert sha(dest/(n+'.olean')) == record['sha256']
    for ns, rows in M['external_objects'].items():
        for n,h in rows.items():
            assert sha(lib/ns/n) == h
    assert sha(Path(M['lean'])) == M['lean_sha256']

save(); print('ROOT',work,'parent',len(M['project_objects']),'modules',len(M['order']),flush=True)
try:
    audit()
    for n in M['order']:
        state['module']=n;save();f=src/(n+'.lean');obj=dest/(n+'.olean');log=logs/(n+'.log');t=time.monotonic()
        with log.open('w') as out:
            r=subprocess.run([M['lean'],'-M6000','-j1','-DElab.async=false','--root='+str(src.parent),
                              str(f),'-o',str(obj)],cwd=ROOT,env=env,stdout=out,stderr=subprocess.STDOUT)
        row={'module':n,'exit':r.returncode,'seconds':time.monotonic()-t,'source_sha256':sha(f),
             'object_sha256':sha(obj) if obj.exists() else None,'log_sha256':sha(log)}
        state['records'].append(row);save()
        if r.returncode or re.search(r'\b(?:warning|error|sorryAx)\b',log.read_text()):
            raise RuntimeError('compile failed: '+n+'\n'+log.read_text())
        if n.endswith('Checks'):
            groups=re.findall(r'depends on axioms:\s*\[([^]]*)\]',log.read_text(),re.S)
            if not groups or any({x.strip() for x in g.split(',') if x.strip()} -
                                 {'propext','Classical.choice','Quot.sound'} for g in groups):
                raise RuntimeError('unexpected axiom dependencies')
        print('PASS',n,flush=True)
    audit();state.update(status='PASS',module=None);save();print('PASS',work,flush=True)
except BaseException as e:
    state.update(status='FAILED',failure=repr(e));save();print('FAILED',repr(e),flush=True);raise
