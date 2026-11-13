import hashlib,json,os,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];p=D/'research/nine-sharing-sign33-absdiff-square-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-absdiff-square-check-20261106');n='Sign33AbsDiffSquare';sha=lambda x:hashlib.sha256(Path(x).read_bytes()).hexdigest()
assert sha(a/'state.json')==sha(out/'state.json')=='0adb930ca2a8ae278945357cbdedb3636c93014b57cdcd85ddfe24edcece0fff';s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1
assert sha(p/'run.py')==s['runner_sha256']=='046d5ce155df2e3d6f0d3a942d5f8ba6acd12255ded5802c65195d96f59e8e9d';assert sha(a/'outer-observation.json')=='61e9124535df0fef0fccf0d1e791ba3851afcdd58d00ffd37c7e8e68538b462a';o=json.loads((a/'outer-observation.json').read_text());assert o['session_id']==57651 and o['numeric_exit']==0 and 'not an independent transcript' in o['observation_source']
r=s['rows'][0];assert r['module']==n and r['source_sha256']=='6dda96f620b4df528aab6b913732f86f68516ad04db0727a7aa84a806be5c0bf' and r['object_sha256']=='f990f1d2f77896b6d52dab63e31e69a0af763c894c5a16d44dc7bb046bce3e65'
src=p/'src/DiophantineConsistency'/f'{n}.lean';assert sha(src)==sha(out/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256'] and sha(out/'lib/DiophantineConsistency'/f'{n}.olean')==r['object_sha256'];t=src.read_text()
for x in ['theorem absdiff_sq (x y : V)','ι (absdiff x y) * ι (absdiff x y) = (ι x-ι y)*(ι x-ι y)']:assert x in t
for phase in ('deps','compile'):
 z=r[phase];assert z['exit']==0 and z['stop_reason'] is None and not z['monitor_errors'] and not z['observed_descendant_pids'];assert sha(a/f'{n}-{phase}.txt')==sha(out/f'{n}-{phase}.txt')==z['log_sha256']
log=(a/f'{n}-compile.txt').read_text();assert sha(a/f'{n}-compile.txt')=='75dea33e8bdb472d12a33556d50e8ac03578546d44501912360648f407bb5c2d';assert log.count('warning:')==0 and 'error:' not in log and 'sorryAx' not in log and "'DiophantineConsistency.Sign33AbsDiffSquare.absdiff_sq' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
cache={}
def check(path,h,rp):
 q=Path(path);assert q.is_file() and str(q.resolve())==rp
 if rp not in cache:cache[rp]=sha(q)
 assert cache[rp]==h
for k,v in r['direct_guard'].items():
 if v is None:assert not os.path.lexists(k)
 else:check(k,v['sha256'],v['realpath'])
for k,v in s['overlay_links'].items():assert Path(k).is_symlink() and str(Path(k).resolve())==v
assert len(r['direct_guard'])==150 and len(s['overlay_links'])==1162
assert sha(a/'survey-before.json')==sha(a/'survey-after.json')==sha(out/'survey-before.json')==sha(out/'survey-after.json')=='5eb58efb621946fc9bff718bceb2708e8f0e6b85c23db11c96bb3724a1038677';survey=json.loads((a/'survey-before.json').read_text());assert survey['status']=='PASS_POINT_PRODUCER_SURVEY'
for k in ('DiophantineConsistency.ArithmeticPellHalfIndex','DiophantineConsistency.ModelDifferenceRing'):
 dep=r['dependencies'][k];sel=survey['selected'][k];check(dep['path'],sel['sha256'],sel['realpath']);assert dep['sha256']==sel['sha256'] and dep['realpath']==sel['realpath'] and r['direct_guard'][dep['path']]==sel
v=subprocess.run([sys.executable,'-I','-S','-B',str(p/'provider_survey.py')],capture_output=True,timeout=60);assert v.returncode==0 and not v.stderr and hashlib.sha256(v.stdout).hexdigest()=='5eb58efb621946fc9bff718bceb2708e8f0e6b85c23db11c96bb3724a1038677'
print(json.dumps({'status':'PASS_TERMINAL_EVIDENCE_ONLY','object_sha256':r['object_sha256'],'author_session':57651,'author_exit':0,'axioms':['propext','Classical.choice','Quot.sound'],'lint_warnings':0,'guard_slots':150,'overlay_links':1162,'scope':'Arbitrary natural-model absdiff-square identity only; no sign33 zero bridge or endpoint, no Lean replay.'},indent=2,sort_keys=True))
