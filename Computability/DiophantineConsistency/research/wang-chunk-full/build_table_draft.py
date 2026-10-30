from pathlib import Path
import hashlib, json, os, shutil, subprocess, tempfile, time

R = Path('/home/codex/.codex/worktrees/46be/Proofs')
P = Path('/tmp/adaptive-wang-table-split-src')
Q = Path('/tmp/adaptive-wang-chunk-full-src')
B = Path(os.environ.get('WANG_CHUNK_PROVIDER', '/tmp/adaptive-wang-chunk-full-042v1clo'))
C = Path('/tmp/adaptive13-assembly-recomposed-q9s50zdl')
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
bs = json.loads((B/'state.json').read_text())
cs = json.loads((C/'state.json').read_text())
g = json.loads((C/'guards.json').read_text())
providers = json.loads((C/'providers.json').read_text())
gen = json.loads((P/'generation.json').read_text())
src = P/'DiophantineConsistency/ArithmeticWangTable.lean'
assert bs['status'] == cs['status'] == 'PASS'
assert sha(C/'guards.json') == cs['guards_sha256'] == bs['base_guards_sha256']
assert sha(C/'providers.json') == cs['providers_sha256'] == bs['base_providers_sha256']
assert sha(C/'state.json') == bs['base_state_sha256']
assert sha(gen['original']) == gen['original_sha256'] == bs['original_sha256']
assert sha(src) == gen['draft_sha256']
assert len(bs['records']) == 26 and all(r['exit'] == 0 for r in bs['records'])
def auth():
    return (sha(B/'state.json') == bh and sha(C/'state.json') == ch
        and sha(C/'guards.json') == cs['guards_sha256']
        and sha(C/'providers.json') == cs['providers_sha256']
        and sha(gen['original']) == gen['original_sha256'] and sha(src) == gen['draft_sha256']
        and all(sha(p) == h for p, h in g.items())
        and all(sha(x['path']) == x['sha256'] for x in providers.values())
        and all(sha(Q/'DiophantineConsistency'/(r['name']+'.lean')) == r['source_sha256']
            and sha(B/'lib/DiophantineConsistency'/(r['name']+'.olean')) == r['object_sha256']
            and sha(B/'logs'/(r['name']+'.log')) == r['log_sha256'] for r in bs['records']))
bh, ch = sha(B/'state.json'), sha(C/'state.json')
assert auth()
w = Path(tempfile.mkdtemp(prefix='adaptive-wang-table-split-'))
lib = w/'lib'
for f in (B/'lib').rglob('*'):
    if f.is_file():
        rel = f.relative_to(B/'lib')
        if rel.parent == Path('DiophantineConsistency') and rel.name.startswith('ArithmeticWangTable.'):
            continue
        dst = lib/rel
        dst.parent.mkdir(parents=True, exist_ok=True)
        dst.symlink_to(f.resolve())
(w/'logs').mkdir()
shutil.copyfile(__file__, w/'driver.py')
shutil.copyfile(src, w/'draft-snapshot.lean')
shutil.copyfile(gen['original'], w/'original-snapshot.lean')
shutil.copyfile(P/'generation.json', w/'generation.json')
state = {'status':'RUNNING', 'private':str(w), 'chunk_provider':str(B),
    'chunk_state_sha256':bh, 'base_state_sha256':ch, 'guards_sha256':cs['guards_sha256'],
    'providers_sha256':cs['providers_sha256'], 'guard_count':len(g), 'provider_count':len(providers),
    'chunk_records':len(bs['records']), 'source_sha256':sha(src), 'original_sha256':sha(gen['original']),
    'boundary':bs['boundary'], 'scope':'Private alternative WangTable build from independently replayed finite chunk facts; no full export comparison, canonical integration, or Assembly claim.'}
def save(): (w/'state.json').write_text(json.dumps(state,indent=2)+'\n')
save(); print('PRIVATE', w, flush=True)
env = dict(os.environ, LEAN_PATH=':'.join([str(lib), *bs['boundary']]), LEAN_NUM_THREADS='1')
env.pop('LEAN_SRC_PATH', None)
o = lib/'DiophantineConsistency/ArithmeticWangTable.olean'
log = w/'logs/build.log'; tim = w/'logs/build.time'
cmd = ['/usr/bin/ionice','-c','3','/usr/bin/nice','-n','10','/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean','-M6000','-j1','-DElab.async=false','-R',str(P),'-o',str(o),str(src)]
state['command']=cmd; save(); print('START', flush=True); start=time.monotonic()
try:
    with log.open('w') as f:
        code = subprocess.run(['/usr/bin/time','-v','-o',str(tim),*cmd],cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
    state.update(exit=code, seconds=time.monotonic()-start, log_sha256=sha(log),time_sha256=sha(tim))
    if o.exists(): state['object_sha256']=sha(o)
    save(); print('DONE', code, state['seconds'], flush=True)
    if code: raise RuntimeError('Lean build failed')
    if not auth(): raise RuntimeError('Source or provider authentication failed after build')
    state['status']='PASS'; save(); print('PASS', w, flush=True)
except BaseException as e:
    state.update(status='FAILED', failure=str(e)); save(); raise
