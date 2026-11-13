import hashlib,json,os,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
P=Path(__file__).resolve().parent;D=P.parents[1];R=D/'research';q=R/'nine-sharing-norm38-reference-gates-batched-check';a=q/'attempt01';out=Path('/tmp/nine-sharing-norm38-reference-gates-batched-check-20261105');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(a/'state.json')==sha(out/'state.json')=='87e43d4d8be3fec16e9fb8fd0b2d28927dc3795d92c2e727491ab15f1a0c9835';s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and s['base_state_sha256']=='d3dc44f113f3cb6c176a67259b3d8df3c825a3ab9009f05374764ccddd7fb3ce'
assert sha(q/'run.py')==s['runner_sha256']=='da96ae87bd9d90819aba563e84e757c090af9d3e4b99acc01e8f2c80d078b589' and sha(q/'source-manifest.json')=='f1bcea19ffbb926edaa3cff8e455ff0e0b63b9698f6ab3b28ae7ddbe9fc6ee20'
assert sha(a/'outer-terminal-author-record.json')=='4a92c894fa6dc3d73606a912dba4536aa6fe72a9d1d5b9491dabb37269d4a92f';o=json.loads((a/'outer-terminal-author-record.json').read_text());assert o['outer_session_id']==25860 and o['outer_exit_code']==0 and 'not independently observed' in o['observation_kind']
rows=s['rows'];names=[f'Norm38ReferenceGateGroup{i:02}' for i in range(12)]+['Norm38ReferenceGatesAll'];assert [r['module'] for r in rows]==names;m=json.loads((q/'source-manifest.json').read_text())['rows'];assert len(m)==13
cache={}
def check(path,h,real=None):
 p=Path(path);assert p.is_file()
 if real is not None:assert str(p.resolve())==real
 k=str(p.resolve())
 if k not in cache:cache[k]=sha(p)
 assert cache[k]==h
for i,r in enumerate(rows):
 n=r['module'];assert r['source_sha256']==m[i]['source_sha256'];check(q/'src/DiophantineConsistency'/f'{n}.lean',r['source_sha256']);check(out/'src/DiophantineConsistency'/f'{n}.lean',r['source_sha256']);check(out/'lib/DiophantineConsistency'/f'{n}.olean',r['object_sha256'])
 for phase in ('deps','compile'):
  z=r[phase];assert z['exit']==0 and z['stop_reason'] is None and not z['monitor_errors'] and not z['observed_descendant_pids']
  for p in (a,out):check(p/f'{n}-{phase}.txt',z['log_sha256'])
 for path,v in r['direct_guard'].items():
  if v is None:assert not os.path.lexists(path)
  else:check(path,v['sha256'],v['realpath'])
 for mod,v in r['dependencies'].items():check(v['path'],v['sha256'],v['realpath'])
 if i<12:assert r['dependencies']['DiophantineConsistency.Norm38ReferenceBase']['sha256']=='723434d993b01cc17c86d82fc0eba7bf9a7723913dc879405666631c15b265f5'
for i in range(12):assert rows[-1]['dependencies']['DiophantineConsistency.'+names[i]]['sha256']==rows[i]['object_sha256']
assert rows[-1]['object_sha256']=='a2ed1f5582804d525fab3ec9bd5fa3346fcfad3036fcdedce8e4654ed4dce7dd'
log=(a/'Norm38ReferenceGatesAll-compile.txt').read_text();assert "reference_gate_equations_batched' depends on axioms: [propext, Quot.sound]" in log and log.count('warning:')==2 and 'error:' not in log
for path,v in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==v
p=D/'reviews/nine-sharing-norm38-reference-base-terminal-independent';x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check.py')],capture_output=True,timeout=120);assert x.returncode==0 and not x.stderr and x.stdout==(p/'result.json').read_bytes(),x.stderr
print(json.dumps({'status':'PASS_TERMINAL_EVIDENCE_ONLY','state_sha256':sha(a/'state.json'),'assembly_object_sha256':rows[-1]['object_sha256'],'author_recorded_session':25860,'author_recorded_exit':0,'stages':len(rows),'guard_slots':sum(len(r['direct_guard']) for r in rows),'overlay_links':len(s['overlay_links']),'axioms':['propext','Quot.sound'],'warnings':2,'scope':'Generic reference gate equations only; no terminal-agreement model bridge or endpoint; no Lean replay.'},indent=2,sort_keys=True))
