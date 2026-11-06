import hashlib,json,os,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
P=Path(__file__).resolve().parent;D=P.parents[1];R=D/'research';q=R/'nine-sharing-norm38-forward-source-check';a=q/'attempt01';out=Path('/tmp/nine-sharing-norm38-forward-source-check-20261105');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(a/'state.json')==sha(out/'state.json')=='cab44da16e5312c579738b4367e8d62b701654aff502e529a3bfd0f30744c58c';s=json.loads((a/'state.json').read_text());assert s['status']=='FAILED' and s['failure']=="RuntimeError('compile failed Norm38SourceToSeed')" and s['base_state_sha256']=='f0a9160c385c1f7163c46e8ebfd967a380e122b56190b2a92ec9d13c248454e8'
assert sha(q/'run.py')==s['runner_sha256']=='3a1194b5cbb8378f3a7e13829df9b89ed0ab5a4138c29998f0fa8cc31199b35a' and sha(q/'source-manifest.json')=='bec8903d2b084d38ba31648de663267d2e12b1f471c64a9601e694011119ee55' and sha(q/'provider_survey.py')=='c939eae7448754104ca9f9d8d978b08845374381a879bf830327e33922e486a6'
assert sha(a/'outer-terminal-author-record.json')=='ca06255512d154356199ebc2bf8f00216875f053aea7f55a8cb262d99b0d703d';o=json.loads((a/'outer-terminal-author-record.json').read_text());assert o['outer_session_id']==15055 and o['outer_exit_code']==1 and 'not independently observed' in o['observation_kind']
rows=s['rows'];assert [r['module'] for r in rows]==['Norm38ForwardFiveNorms','Norm38SourceToSeed'];m=json.loads((q/'source-manifest.json').read_text())['rows'];assert len(m)==2
assert sha(a/'survey-before.json')=='38da20ddb5a217a84f615dd0eeed5a074edead53a25f7717550e65be76b6b558';survey=json.loads((a/'survey-before.json').read_text());assert survey['status']=='PASS_POINT_PRODUCER_SURVEY' and len(survey['links'])==1137 and len(survey['selected'])==7
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
  if mod!='Init' and mod in survey['selected']:assert v['sha256']==survey['selected'][mod]['sha256'] and v['realpath']==survey['selected'][mod]['realpath']
 if i==0:assert r['object_sha256']=='e612241ec264e407e02ff13e50a9d8859909f13e461a0282165fa31bbcfc9baa';check(out/'lib/DiophantineConsistency'/f'{n}.olean',r['object_sha256'])
 else:assert 'object_sha256' not in r and not (out/'lib/DiophantineConsistency'/f'{n}.olean').exists()
good=(a/'Norm38ForwardFiveNorms-compile.txt').read_text();assert "forward_fiveNorms' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]" in good and 'warning:' not in good
assert (a/'Norm38SourceToSeed-compile.txt').read_bytes()==b'' and rows[1]['compile']['timeout_seconds']==120
local=rows[1]['dependencies']['DiophantineConsistency.Norm38ForwardFiveNorms'];assert local['sha256']==rows[0]['object_sha256'] and Path(local['path']).resolve()==(out/'lib/DiophantineConsistency/Norm38ForwardFiveNorms.olean').resolve()
for path,v in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==v
x=subprocess.run([sys.executable,'-I','-S','-B',str(q/'provider_survey.py')],capture_output=True,text=True,timeout=120);z=json.loads(x.stdout);assert x.returncode==0 and not x.stderr and z['status']=='PASS_POINT_PRODUCER_SURVEY' and z['selected']==survey['selected'] and z['links']==survey['links']
print(json.dumps({'status':'PASS_PARTIAL_TIMEOUT_EVIDENCE_ONLY','state_sha256':sha(a/'state.json'),'stage1_object_sha256':rows[0]['object_sha256'],'author_recorded_session':15055,'author_recorded_exit':1,'guard_slots':sum(len(r['direct_guard']) for r in rows),'overlay_links':len(s['overlay_links']),'scope':'Forward five-norm theorem compiled; source-to-seed timed out and whole-run postflight unrun; no Lean replay.'},indent=2,sort_keys=True))
