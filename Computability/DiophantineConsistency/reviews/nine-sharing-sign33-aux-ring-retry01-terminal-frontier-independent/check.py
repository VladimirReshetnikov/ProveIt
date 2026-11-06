import hashlib,json,os,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];p=D/'research/nine-sharing-sign33-aux-ring-retry01';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-aux-ring-retry01-20261106');n='Sign33AuxRing';sha=lambda x:hashlib.sha256(Path(x).read_bytes()).hexdigest()
assert sha(a/'state.json')==sha(out/'state.json')=='cf7ac3aa5c46fd4dc3eb6cd3da2b5009aea19a104fc710b098244b53155b40de';s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1
assert sha(p/'run.py')==s['runner_sha256']=='3b12db4c61cbcb87aec11f6350e8f3dd504f30e2e4d50810794b6c0eb86f3431';assert sha(a/'outer-observation.json')=='9f90509edd128a0b898d8c408d3406e297bbd6f2b64b00cd2e43254352145332';o=json.loads((a/'outer-observation.json').read_text());assert o['session_id']==48441 and o['numeric_exit']==0 and 'not an independent transcript' in o['observation_source']
r=s['rows'][0];assert r['module']==n and r['source_sha256']=='fd4e20bc73bf0ea3fce0efd8bcd85fe0f34930306ca0eca81c6e743355f0da5d' and r['object_sha256']=='c811fe71c42029cf613637374432ae92f636dad314d2b3b756690831aa5af621'
src=p/'src/DiophantineConsistency'/f'{n}.lean';assert sha(src)==sha(out/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256'] and sha(out/'lib/DiophantineConsistency'/f'{n}.olean')==r['object_sha256'];t=src.read_text()
for x in ['(hS : 0<S) (hy : 0<y)','(haux : S*S*(absdiff x z)*(absdiff x z)+y*y=1+S*S*y*y)','(ι x-ι z)*(ι x-ι z)-ι y*ι y ≤ 0']:assert x in t
for phase in ('deps','compile'):
 z=r[phase];assert z['exit']==0 and z['stop_reason'] is None and not z['monitor_errors'] and not z['observed_descendant_pids'];assert sha(a/f'{n}-{phase}.txt')==sha(out/f'{n}-{phase}.txt')==z['log_sha256']
log=(a/f'{n}-compile.txt').read_text();assert sha(a/f'{n}-compile.txt')=='c816a9cbe4d9e1bebcc05c00f26b6acfbd55e34e933493d21e10430d9a978e0a';assert log.count('warning:')==0 and 'error:' not in log and 'sorryAx' not in log and "'DiophantineConsistency.Sign33AuxRing.aux_difference_of_norm' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
cache={}
def check(path,h,rp):
 q=Path(path);assert q.is_file() and str(q.resolve())==rp
 if rp not in cache:cache[rp]=sha(q)
 assert cache[rp]==h
for k,v in r['direct_guard'].items():
 if v is None:assert not os.path.lexists(k)
 else:check(k,v['sha256'],v['realpath'])
for k,v in s['overlay_links'].items():assert Path(k).is_symlink() and str(Path(k).resolve())==v
assert len(r['direct_guard'])==150 and len(s['overlay_links'])==1166
assert sha(a/'survey-before.json')==sha(a/'survey-after.json')==sha(out/'survey-before.json')==sha(out/'survey-after.json')=='839c8edadeeb8e589e5b0159865398ae62ec2954563bb62adfdc7f363077cc2e';survey=json.loads((a/'survey-before.json').read_text());assert survey['status']=='PASS_POINT_PRODUCER_SURVEY'
for k in ('DiophantineConsistency.Sign33AbsDiffSquare','Sign33OrderedRing'):
 dep=r['dependencies'][k];sel=survey['selected'][k];check(dep['path'],sel['sha256'],sel['realpath']);assert dep['sha256']==sel['sha256'] and dep['realpath']==sel['realpath'] and r['direct_guard'][dep['path']]==sel
v=subprocess.run([sys.executable,'-I','-S','-B',str(p/'provider_survey.py')],capture_output=True,timeout=60);assert v.returncode==0 and not v.stderr and hashlib.sha256(v.stdout).hexdigest()=='839c8edadeeb8e589e5b0159865398ae62ec2954563bb62adfdc7f363077cc2e'
print(json.dumps({'status':'PASS_TERMINAL_EVIDENCE_ONLY','object_sha256':r['object_sha256'],'author_session':48441,'author_exit':0,'axioms':['propext','Classical.choice','Quot.sound'],'lint_warnings':0,'guard_slots':150,'overlay_links':1166,'scope':'Conditional auxiliary norm sign only; no sign33 zero bridge or endpoint, no Lean replay.'},indent=2,sort_keys=True))
