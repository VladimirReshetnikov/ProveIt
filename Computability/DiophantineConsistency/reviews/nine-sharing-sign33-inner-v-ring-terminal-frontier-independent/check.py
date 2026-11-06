import hashlib,json,os,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];p=D/'research/nine-sharing-sign33-inner-v-ring-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-inner-v-ring-check-20261106');n='Sign33InnerVRing';sha=lambda x:hashlib.sha256(Path(x).read_bytes()).hexdigest()
assert sha(a/'state.json')==sha(out/'state.json')=='2c4ed1f6ee2dd1588d0c1b1d2a4121f0f07e1a38bac2fe53b317d73153b43c2a';s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1
assert sha(p/'run.py')==s['runner_sha256']=='290b69728ebb925d9c1ad6bb2bc0e13ea721c99f387a65f7121f8d9f7dc445fb';assert sha(a/'outer-observation.json')=='ec081713425dc5353ef1cce97f8e297a08da1529eb2ee792a0a06bb1942130dd';o=json.loads((a/'outer-observation.json').read_text());assert o['session_id']==56073 and o['numeric_exit']==0 and 'not an independent transcript' in o['observation_source']
r=s['rows'][0];assert r['module']==n and r['source_sha256']=='d433ca992bad31b325c5e38693dea26fc7731875b4a130132c1c52d451e6f9a9' and r['object_sha256']=='bb4c20461196accbd1e3e3914f9ab6637f2142f5366150e29caf3b037d3371da'
src=p/'src/DiophantineConsistency'/f'{n}.lean';assert sha(src)==sha(out/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256'] and sha(out/'lib/DiophantineConsistency'/f'{n}.olean')==r['object_sha256'];t=src.read_text()
for x in ['(hc : 0<c) (hT : 0<T) (hf : 0<f) (hi : 0<i)','(hhalf : 2*r<c)','(hstrict : f*f=1+delta a*(i*c*c)*(i*c*c))','0 ≤ ι c*ι T-ι r ∧ 0 ≤ ι f*ι f*(ι c*ι T-ι r)-ι c']:assert x in t
for phase in ('deps','compile'):
 z=r[phase];assert z['exit']==0 and z['stop_reason'] is None and not z['monitor_errors'] and not z['observed_descendant_pids'];assert sha(a/f'{n}-{phase}.txt')==sha(out/f'{n}-{phase}.txt')==z['log_sha256']
log=(a/f'{n}-compile.txt').read_text();assert sha(a/f'{n}-compile.txt')=='f0df670715ddf08d3cad96e98e6fc55064710069dad53301be1738a2d89dcfd7';assert log.count('warning:')==0 and 'error:' not in log and 'sorryAx' not in log and "'DiophantineConsistency.Sign33InnerVRing.inner_v_of_window_and_strong' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]" in log
cache={}
def check(path,h,rp):
 q=Path(path);assert q.is_file() and str(q.resolve())==rp
 if rp not in cache:cache[rp]=sha(q)
 assert cache[rp]==h
for k,v in r['direct_guard'].items():
 if v is None:assert not os.path.lexists(k)
 else:check(k,v['sha256'],v['realpath'])
for k,v in s['overlay_links'].items():assert Path(k).is_symlink() and str(Path(k).resolve())==v
assert len(r['direct_guard'])==150 and len(s['overlay_links'])==1165
assert sha(a/'survey-before.json')==sha(a/'survey-after.json')==sha(out/'survey-before.json')==sha(out/'survey-after.json')=='d9f974099b02b4f95706040bef7499ec35c7f8757bf7629c811b2b547259ff7f';survey=json.loads((a/'survey-before.json').read_text());assert survey['status']=='PASS_POINT_PRODUCER_SURVEY'
for k in ('DiophantineConsistency.Sign33StrongF','Sign33OrderedRing'):
 dep=r['dependencies'][k];sel=survey['selected'][k];check(dep['path'],sel['sha256'],sel['realpath']);assert dep['sha256']==sel['sha256'] and dep['realpath']==sel['realpath'] and r['direct_guard'][dep['path']]==sel
v=subprocess.run([sys.executable,'-I','-S','-B',str(p/'provider_survey.py')],capture_output=True,timeout=60);assert v.returncode==0 and not v.stderr and hashlib.sha256(v.stdout).hexdigest()=='d9f974099b02b4f95706040bef7499ec35c7f8757bf7629c811b2b547259ff7f'
print(json.dumps({'status':'PASS_TERMINAL_EVIDENCE_ONLY','object_sha256':r['object_sha256'],'author_session':56073,'author_exit':0,'axioms':['propext','Classical.choice','Quot.sound'],'lint_warnings':0,'guard_slots':150,'overlay_links':1165,'scope':'Conditional inner/V ring signs only; no sign33 zero bridge or endpoint, no Lean replay.'},indent=2,sort_keys=True))
