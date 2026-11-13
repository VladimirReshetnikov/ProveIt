import hashlib,json,os,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];p=D/'research/nine-sharing-sign33-five-witnesses-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-five-witnesses-check-20261106');n='Sign33FiveWitnesses';sha=lambda x:hashlib.sha256(Path(x).read_bytes()).hexdigest()
assert sha(a/'state.json')==sha(out/'state.json')=='933c9733daeaa2c705fbb1a5b1c3c95c4ab37d078a9c9b3bfc839d39b469253e';s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1
assert sha(p/'run.py')==s['runner_sha256']=='f786a9f8d979f3820d849fb8de0901084a9bffe7911f132766b70baa4007e5f0';assert sha(a/'outer-observation.json')=='1dd149b27242dbecda3a7046ed3a2917bdfe650e388d290ffc4afdb8869fc7ca';o=json.loads((a/'outer-observation.json').read_text());assert o['session_id']==61841 and o['numeric_exit']==0 and 'not an independent transcript' in o['observation_source']
r=s['rows'][0];assert r['module']==n and r['source_sha256']=='dbecb8b85c1e3f54446b50eb8e2b68e6dc5f389d49493d14ffe84962f20da893' and r['object_sha256']=='5e1543945a01464d97340fa1dedf90529ca37f16d1821a9186a613410ff9cee0'
src=p/'src/DiophantineConsistency'/f'{n}.lean';assert sha(src)==sha(out/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256'] and sha(out/'lib/DiophantineConsistency'/f'{n}.olean')==r['object_sha256'];t=src.read_text()
for x in ['(hq : 1≤q) (hN : 1≤N) (hgap : 0<q-F-alpha) (hr : r+2<E)','(hc : 0<c) (hT : 0<T) (hf : 0<f) (hi : 0<i) (hhalf : 2*r<c)','(hstrict : f*f=1+delta a*(i*c*c)*(i*c*c))','(hS : 0<S) (hy : 0<y)','S*S*(absdiff x z)*(absdiff x z)+y*y=1+S*S*y*y','∃ gap tau inner v negative : V','ι negative = ι y*ι y-(ι x-ι z)*(ι x-ι z)']:assert x in t
for phase in ('deps','compile'):
 z=r[phase];assert z['exit']==0 and z['stop_reason'] is None and not z['monitor_errors'] and not z['observed_descendant_pids'];assert sha(a/f'{n}-{phase}.txt')==sha(out/f'{n}-{phase}.txt')==z['log_sha256']
log=(a/f'{n}-compile.txt').read_text();assert sha(a/f'{n}-compile.txt')=='66bd1812289e9dd111547bf3b89c3d61db1c17c96cdf3c524aa81371949cb706';assert log.count('warning:')==0 and 'error:' not in log and 'sorryAx' not in log and "'DiophantineConsistency.Sign33FiveWitnesses.five_witnesses_of_windows_and_norms' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]" in log
cache={}
def check(path,h,rp):
 q=Path(path);assert q.is_file() and str(q.resolve())==rp
 if rp not in cache:cache[rp]=sha(q)
 assert cache[rp]==h
for k,v in r['direct_guard'].items():
 if v is None:assert not os.path.lexists(k)
 else:check(k,v['sha256'],v['realpath'])
for k,v in s['overlay_links'].items():assert Path(k).is_symlink() and str(Path(k).resolve())==v
assert len(r['direct_guard'])==200 and len(s['overlay_links'])==1169
assert sha(a/'survey-before.json')==sha(a/'survey-after.json')==sha(out/'survey-before.json')==sha(out/'survey-after.json')=='951cbb884e3e815e7132cbfb7397d20f9ed5b50de73b9e294ca4ebbce4a5a0b0';survey=json.loads((a/'survey-before.json').read_text());assert survey['status']=='PASS_POINT_PRODUCER_SURVEY'
for k in ('DiophantineConsistency.Sign33GapTauRing','DiophantineConsistency.Sign33InnerVRing','DiophantineConsistency.Sign33AuxRing'):
 dep=r['dependencies'][k];sel=survey['selected'][k];check(dep['path'],sel['sha256'],sel['realpath']);assert dep['sha256']==sel['sha256'] and dep['realpath']==sel['realpath'] and r['direct_guard'][dep['path']]==sel
v=subprocess.run([sys.executable,'-I','-S','-B',str(p/'provider_survey.py')],capture_output=True,timeout=60);assert v.returncode==0 and not v.stderr and hashlib.sha256(v.stdout).hexdigest()=='951cbb884e3e815e7132cbfb7397d20f9ed5b50de73b9e294ca4ebbce4a5a0b0'
print(json.dumps({'status':'PASS_TERMINAL_EVIDENCE_ONLY','object_sha256':r['object_sha256'],'author_session':61841,'author_exit':0,'axioms':['propext','Classical.choice','Quot.sound'],'lint_warnings':0,'guard_slots':200,'overlay_links':1169,'scope':'Conditional five natural representatives only; no concrete 33-variable seed bridge or endpoint, no Lean replay.'},indent=2,sort_keys=True))
