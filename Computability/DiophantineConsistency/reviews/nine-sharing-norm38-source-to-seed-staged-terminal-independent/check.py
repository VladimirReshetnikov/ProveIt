import hashlib,json,os,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
P=Path(__file__).resolve().parent;D=P.parents[1];R=D/'research';q=R/'nine-sharing-norm38-source-to-seed-staged';a=q/'attempt01';out=Path('/tmp/nine-sharing-norm38-source-to-seed-staged-20261105');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(a/'state.json')==sha(out/'state.json')=='94bb5144f566046c47841eb77a35b57b752e8f46d0fccd4cf75f4b44fcc7aeae';s=json.loads((a/'state.json').read_text());assert s['status']=='FAILED' and s['failure']=="RuntimeError('compile failed Norm38CarrierUnitNorms')" and s['base_state_sha256']=='f0a9160c385c1f7163c46e8ebfd967a380e122b56190b2a92ec9d13c248454e8'
assert sha(q/'run.py')==s['runner_sha256']=='6b5ee8ddba7c09914ca18cf9450ebafd53cdda77d7f90d58cb7618a169187869' and sha(q/'source-manifest.json')=='616e70064e4ad2959b2d9bb45d0baf635f5765b20f1a1a327a2edaf925e60e4c' and sha(q/'provider_survey.py')=='631812fa3f28d07fafa704f43e152f9b78dd3b1faa6eb8cd0baddc0faa08b783'
assert sha(a/'outer-observation.json')=='d9b7c01999f922c73c7dc4120de0317c450732fe5fe9c24ef8753a349b51972b';o=json.loads((a/'outer-observation.json').read_text());assert o['session_id']==31838 and o['numeric_exit']==1 and 'not an independent transcript' in o['observation_source']
rows=s['rows'];assert [r['module'] for r in rows]==['Norm38SourceCarrierZero','Norm38CarrierUnitNorms'];m=json.loads((q/'source-manifest.json').read_text())['rows'];assert len(m)==3
assert sha(a/'survey-before.json')=='f69de9b5a9dcc2d6bf93d5ac8e4e6a06353d5645ba8f86c5aeda71a6084697a8';survey=json.loads((a/'survey-before.json').read_text());assert survey['status']=='PASS_POINT_PRODUCER_SURVEY' and len(survey['links'])==1138 and len(survey['selected'])==8
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
  z=r[phase];assert z['exit']==(-15 if i==1 and phase=='compile' else 0) and z['stop_reason']==('timeout' if i==1 and phase=='compile' else None) and not z['monitor_errors'] and not z['observed_descendant_pids']
  for p in (a,out):check(p/f'{n}-{phase}.txt',z['log_sha256'])
 for path,v in r['direct_guard'].items():
  if v is None:assert not os.path.lexists(path)
  else:check(path,v['sha256'],v['realpath'])
 for mod,v in r['dependencies'].items():
  check(v['path'],v['sha256'],v['realpath']);assert r['direct_guard'][v['path']]['sha256']==v['sha256'] and r['direct_guard'][v['path']]['realpath']==v['realpath']
  if mod in survey['selected']:assert v['sha256']==survey['selected'][mod]['sha256'] and v['realpath']==survey['selected'][mod]['realpath']
 if i==0:assert r['object_sha256']=='1fac54d1bce8d18a18d3865a922aeefdde19833c091293003c8186673c69283c';check(out/'lib/DiophantineConsistency'/f'{n}.olean',r['object_sha256'])
 else:assert 'object_sha256' not in r and not (out/'lib/DiophantineConsistency'/f'{n}.olean').exists()
good=(a/'Norm38SourceCarrierZero-compile.txt').read_text();assert "source_zero_carrier' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]" in good and 'warning:' not in good
assert (a/'Norm38CarrierUnitNorms-compile.txt').read_bytes()==b'' and rows[1]['compile']['timeout_seconds']==120 and not (a/'Norm38SourceToSeed-compile.txt').exists()
for path,v in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==v
x=subprocess.run([sys.executable,'-I','-S','-B',str(q/'provider_survey.py')],capture_output=True,text=True,timeout=120);z=json.loads(x.stdout);assert x.returncode==0 and not x.stderr and z['status']=='PASS_POINT_PRODUCER_SURVEY' and z['selected']==survey['selected'] and z['links']==survey['links']
print(json.dumps({'status':'PASS_PARTIAL_TIMEOUT_EVIDENCE_ONLY','state_sha256':sha(a/'state.json'),'stage1_object_sha256':rows[0]['object_sha256'],'author_recorded_session':31838,'author_recorded_exit':1,'guard_slots':sum(len(r['direct_guard']) for r in rows),'overlay_links':len(s['overlay_links']),'scope':'Source-zero-to-carrier stage passed; model norm extraction timed out and composition unrun; no Lean replay.'},indent=2,sort_keys=True))
