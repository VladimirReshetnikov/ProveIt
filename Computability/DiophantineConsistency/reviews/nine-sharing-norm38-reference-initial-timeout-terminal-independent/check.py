import hashlib,json,os,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
P=Path(__file__).resolve().parent;D=P.parents[1];R=D/'research';q=R/'nine-sharing-norm38-reference-initial-check';a=q/'attempt01';out=Path('/tmp/nine-sharing-norm38-reference-initial-check-20261105');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();n='Norm38ReferenceInitial'
assert sha(a/'state.json')==sha(out/'state.json')=='399108a167bf38bc8629bdd01c08350a4d5275df46f119e4d966b7820bab90ec';s=json.loads((a/'state.json').read_text());assert s['status']=='FAILED' and s['failure']=="RuntimeError('compile failed Norm38ReferenceInitial')" and s['base_state_sha256']=='d3dc44f113f3cb6c176a67259b3d8df3c825a3ab9009f05374764ccddd7fb3ce'
assert sha(q/'run.py')==s['runner_sha256']=='e240124b3bd2fe2c811d28500f2b4e6e43d6933031b04d3bb9385a4f7201cdd5' and sha(q/'source-manifest.json')=='7555bed187202810ec868d84aedd59c48eb8f92ee3714216044e5023761ab846'
assert sha(a/'outer-terminal-author-record.json')=='c2b189962992599f229b899b2a44ea6e7cf4ef0da2a3e2cbd6ed4182888bd157';o=json.loads((a/'outer-terminal-author-record.json').read_text());assert o['outer_session_id']==64387 and o['outer_exit_code']==1 and 'not independently observed' in o['observation_kind']
assert len(s['rows'])==1;r=s['rows'][0];assert r['module']==n and r['source_sha256']=='a1af22fdf820cb3c999a3e176227e2bc418b60ee58ae0dfd5ffdfc13ca01d1f1' and 'object_sha256' not in r
cache={}
def check(path,h,real=None):
 p=Path(path);assert p.is_file()
 if real is not None:assert str(p.resolve())==real
 k=str(p.resolve())
 if k not in cache:cache[k]=sha(p)
 assert cache[k]==h
src=q/'src/DiophantineConsistency'/f'{n}.lean';check(src,r['source_sha256']);check(out/'src/DiophantineConsistency'/f'{n}.lean',r['source_sha256']);assert not (out/'lib/DiophantineConsistency'/f'{n}.olean').exists()
t=src.read_text();assert '∀ i ∈ initialNodes' in t and '(NormAssignment38.assignment ports w i)' in t and 'Fin.castLE (by decide : 14 ≤ 38)' in t
for phase in ('deps','compile'):
 z=r[phase];assert z['exit']==(0 if phase=='deps' else -15) and z['stop_reason']==(None if phase=='deps' else 'timeout') and not z['monitor_errors'] and not z['observed_descendant_pids']
 for p in (a,out):check(p/f'{n}-{phase}.txt',z['log_sha256'])
assert (a/f'{n}-compile.txt').read_bytes()==b'' and r['compile']['timeout_seconds']==120
for path,v in r['direct_guard'].items():
 if v is None:assert not os.path.lexists(path)
 else:check(path,v['sha256'],v['realpath'])
for path,v in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==v
dep=r['dependencies']['DiophantineConsistency.Norm38ReferenceBase'];assert dep['sha256']=='723434d993b01cc17c86d82fc0eba7bf9a7723913dc879405666631c15b265f5';check(dep['path'],dep['sha256'],dep['realpath'])
p=D/'reviews/nine-sharing-norm38-reference-base-terminal-independent';x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check.py')],capture_output=True,timeout=120);assert x.returncode==0 and not x.stderr and x.stdout==(p/'result.json').read_bytes(),x.stderr
print(json.dumps({'status':'PASS_TIMEOUT_EVIDENCE_ONLY','state_sha256':sha(a/'state.json'),'author_recorded_session':64387,'author_recorded_exit':1,'compile_exit':-15,'stop_reason':'timeout','elapsed_seconds':r['compile']['elapsed_seconds'],'guard_slots':len(r['direct_guard']),'overlay_links':len(s['overlay_links']),'scope':'No Lean replay; no theorem object or axiom report; final postflight not reached.'},indent=2,sort_keys=True))
