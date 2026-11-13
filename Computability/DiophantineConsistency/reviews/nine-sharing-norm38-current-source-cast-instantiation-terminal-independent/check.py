import hashlib,json,os,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
P=Path(__file__).resolve().parent;D=P.parents[1];R=D/'research';q=R/'nine-sharing-norm38-current-source-cast-instantiation';a=q/'attempt01';out=Path('/tmp/nine-sharing-norm38-current-source-cast-instantiation-20261106');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(a/'state.json')==sha(out/'state.json')=='ce4c75e2c8f603965d6bfc6f8038a0299a54163b22d78b01afc48c38a70fda27';s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and s['base_state_sha256']=='f0a9160c385c1f7163c46e8ebfd967a380e122b56190b2a92ec9d13c248454e8'
assert sha(q/'run.py')==s['runner_sha256']=='2369327030d8b551c84a896ff8afb1e4725040ed220c2d880b6b7f925a2759cf' and sha(q/'source-manifest.json')=='8065a6e99a475def42b31e03044d77d67b64a97243686dc1b8bbbce1ef68ec6a' and sha(q/'provider_survey.py')=='a8b88dcbd9a1ea69d8679a459f6941ada18e6b845c216330413f2f78c760e85c'
assert sha(a/'outer-observation.json')=='31fa0fad553067176746e8f6965dadb154f09010a308e6fb2f2159719cadb980';o=json.loads((a/'outer-observation.json').read_text());assert o['session_id']==50683 and o['numeric_exit']==0 and 'not an independent transcript' in o['observation_source']
assert sha(a/'survey-before.json')==sha(a/'survey-after.json')=='66800bc782a8c7b28693372efcc470858286f640b3c3eb441e6488d52e6a0564';survey=json.loads((a/'survey-before.json').read_text());assert survey['status']=='PASS_POINT_PRODUCER_SURVEY'
rows=s['rows'];names=['Norm38SourceFourCasts','Norm38CurrentSourceFourCasts'];objects=['a6d54fb349a8e0c2a25a7b1a379e5029dda893325a6229b83f9340e2fc2ef10e','d0419dac500817ece12c1d6d4d4a90ab78afb45fe62447a2d2311a9b1d980a43'];assert [r['module'] for r in rows]==names;m=json.loads((q/'source-manifest.json').read_text())['rows'];assert len(m)==2
cache={}
def check(path,h,real=None):
 p=Path(path);assert p.is_file()
 if real is not None:assert str(p.resolve())==real
 k=str(p.resolve())
 if k not in cache:cache[k]=sha(p)
 assert cache[k]==h
for i,r in enumerate(rows):
 n=r['module'];assert r['source_sha256']==m[i]['source_sha256'] and r['object_sha256']==objects[i];check(q/'src/DiophantineConsistency'/f'{n}.lean',r['source_sha256']);check(out/'src/DiophantineConsistency'/f'{n}.lean',r['source_sha256']);check(out/'lib/DiophantineConsistency'/f'{n}.olean',r['object_sha256'])
 for phase in ('deps','compile'):
  z=r[phase];assert z['exit']==0 and z['stop_reason'] is None and not z['monitor_errors'] and not z['observed_descendant_pids']
  for p in (a,out):check(p/f'{n}-{phase}.txt',z['log_sha256'])
 for path,v in r['direct_guard'].items():
  if v is None:assert not os.path.lexists(path)
  else:check(path,v['sha256'],v['realpath'])
 for mod,v in r['dependencies'].items():
  check(v['path'],v['sha256'],v['realpath']);assert r['direct_guard'][v['path']]['sha256']==v['sha256'] and r['direct_guard'][v['path']]['realpath']==v['realpath']
  if mod in survey['selected']:assert v['sha256']==survey['selected'][mod]['sha256'] and v['realpath']==survey['selected'][mod]['realpath']
 log=(a/f'{n}-compile.txt').read_text();assert "source_zero_implies_seed_zero' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]" in log and 'warning:' not in log and 'error:' not in log
assert rows[1]['dependencies']['DiophantineConsistency.Norm38SourceFourCasts']['sha256']==objects[0]
t=(q/'src/DiophantineConsistency/Norm38CurrentSourceFourCasts.lean').read_text();assert 'Norm38CurrentFourCastInstantiation.currentNaturalPorts (V := V)' in t and 'Norm38CurrentPorts.port0 Norm38CurrentPorts.port1 Norm38CurrentPorts.port2 Norm38CurrentPorts.port3 hs' in t and 'InternalZero (ObjectCurrentEquation2011.expressionAt CurrentWindowCarry2011.ports)' in t and 'InternalZero (SharingSeed38.seed CurrentWindowCarry2011.ports)' in t
for path,v in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==v
x=subprocess.run([sys.executable,'-I','-S','-B',str(q/'provider_survey.py')],capture_output=True,text=True,timeout=120);z=json.loads(x.stdout);assert x.returncode==0 and not x.stderr and z['status']=='PASS_POINT_PRODUCER_SURVEY' and z['selected']==survey['selected'] and z['links']==survey['links']
print(json.dumps({'status':'PASS_TERMINAL_EVIDENCE_ONLY','state_sha256':sha(a/'state.json'),'generic_object_sha256':objects[0],'current_object_sha256':objects[1],'author_recorded_session':50683,'author_recorded_exit':0,'guard_slots':sum(len(r['direct_guard']) for r in rows),'overlay_links':len(s['overlay_links']),'axioms':['propext','Classical.choice','Quot.sound'],'warnings':0,'scope':'Fixed-current symbolic source zero implies seed zero without explicit cast hypotheses; Jones composition and endpoint still needed; no Lean replay.'},indent=2,sort_keys=True))
