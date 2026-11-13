import hashlib,json,os,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
P=Path(__file__).resolve().parent;D=P.parents[1];R=D/'research';q=R/'nine-sharing-norm38-current-ports-abstract-retry';a=q/'attempt01';out=Path('/tmp/nine-sharing-norm38-current-ports-abstract-retry-20261105');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(a/'state.json')==sha(out/'state.json')=='c7e1f7e465cf89c0d5ca5e3231cf0ddc96bcd35fa31399d219174a119df75c09';s=json.loads((a/'state.json').read_text());assert s['status']=='FAILED' and s['failure']=="RuntimeError('compile failed Norm38CurrentPortCasts')" and s['base_state_sha256']=='0f89b8b0a53abd15b0d7c1e20f198495775628e104fabc247c24efbd2cb81ad4'
assert sha(q/'run.py')==s['runner_sha256']=='8ee39d443bc674628c351c08e57f54c5620bb5b48802219a94b5bc7c6eeb0890' and sha(q/'source-manifest.json')=='b58ac129649c50eef14df7c1a01181cd8dd248f0598a9344a5a5f4e650082cd9'
assert sha(a/'outer-terminal-author-record.json')=='4547e39ad45dbe3c6897354242ff7a93d0e3cf029c9a516fa83f19e07d2fb2dd';o=json.loads((a/'outer-terminal-author-record.json').read_text());assert o['outer_session_id']==21890 and o['outer_exit_code']==1 and 'not independently observed' in o['observation_kind']
rows=s['rows'];assert [r['module'] for r in rows]==['Norm38FinFour','Norm38CurrentPortCasts'];m=json.loads((q/'source-manifest.json').read_text())['rows'];assert len(m)==3
cache={}
def check(path,h,real=None):
 p=Path(path);assert p.is_file()
 if real is not None:assert str(p.resolve())==real
 k=str(p.resolve())
 if k not in cache:cache[k]=sha(p)
 assert cache[k]==h
for i,r in enumerate(rows):
 n=r['module'];assert r['source_sha256']==m[i]['source_sha256'];check(q/'src/DiophantineConsistency'/f'{n}.lean',r['source_sha256']);check(out/'src/DiophantineConsistency'/f'{n}.lean',r['source_sha256'])
 for phase in ('deps','compile'):
  z=r[phase];assert z['exit']==(1 if i==1 and phase=='compile' else 0) and z['stop_reason'] is None and not z['monitor_errors'] and not z['observed_descendant_pids']
  for p in (a,out):check(p/f'{n}-{phase}.txt',z['log_sha256'])
 for path,v in r['direct_guard'].items():
  if v is None:assert not os.path.lexists(path)
  else:check(path,v['sha256'],v['realpath'])
 for mod,v in r['dependencies'].items():check(v['path'],v['sha256'],v['realpath'])
 if i==0:assert r['object_sha256']=='6d5c93c760bc537fb5fcbbe4e7d12499c2fda37139c7df6a38a8409f2c614707';check(out/'lib/DiophantineConsistency'/f'{n}.olean',r['object_sha256'])
 else:assert 'object_sha256' not in r and not (out/'lib/DiophantineConsistency'/f'{n}.olean').exists()
good=(a/'Norm38FinFour-compile.txt').read_text();assert 'Norm38FinFour.eq_all\' depends on axioms: [propext, Classical.choice, Quot.sound]' in good and 'warning:' not in good
bad=(a/'Norm38CurrentPortCasts-compile.txt').read_text();assert ':15:8: error: (kernel) excessive memory consumption detected' in bad and 'DiophantineConsistency.Norm38CurrentPorts.port_casts]' in bad
assert not (a/'Norm38CurrentPortSpecialization-compile.txt').exists()
for path,v in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==v
assert rows[1]['dependencies']['DiophantineConsistency.Norm38FinFour']['sha256']==rows[0]['object_sha256']
parent=json.loads((R/'nine-sharing-norm38-current-ports-split-draft/attempt01/state.json').read_text())
assert parent['status']=='FAILED'
assert rows[0]['dependencies']['DiophantineConsistency.Norm38CurrentPortBase']['sha256']==parent['rows'][0]['object_sha256']
for i in range(4):assert rows[1]['dependencies'][f'DiophantineConsistency.Norm38CurrentPort{i}']['sha256']==parent['rows'][i+1]['object_sha256']
p=D/'reviews/nine-sharing-norm38-current-ports-split-terminal-independent';x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check.py')],capture_output=True,timeout=120);assert x.returncode==0 and not x.stderr and x.stdout==(p/'result.json').read_bytes(),x.stderr
print(json.dumps({'status':'PASS_PARTIAL_FAILURE_EVIDENCE_ONLY','state_sha256':sha(a/'state.json'),'author_recorded_session':21890,'author_recorded_exit':1,'generic_object_sha256':rows[0]['object_sha256'],'failed_compile_exit':1,'guard_slots':sum(len(r['direct_guard']) for r in rows),'overlay_links':len(s['overlay_links']),'scope':'No Lean replay; failed universal axiom report contains failed declaration; final specialization unrun.'},indent=2,sort_keys=True))
