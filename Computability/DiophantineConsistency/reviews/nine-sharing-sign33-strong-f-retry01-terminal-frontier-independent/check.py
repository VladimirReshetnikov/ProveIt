import hashlib,json,os,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];p=D/'research/nine-sharing-sign33-strong-f-retry01';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-strong-f-retry01-20261106');n='Sign33StrongF';sha=lambda x:hashlib.sha256(Path(x).read_bytes()).hexdigest()
assert sha(a/'state.json')==sha(out/'state.json')=='2c513f2262b81f9b0e7d0da8b704dab73da0820a7a339ef9158a3eddc3b06a2c';s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1
assert sha(p/'run.py')==s['runner_sha256']=='dc29a2628ab57d87bde74ab5663f72ef5f86e57b9cb70d58c260f03a2f3f9d22';assert sha(a/'outer-observation.json')=='b2b998ae4c7698266ecf37ee75e23aca2658d2c56267712ebb8daad9a2466c54';o=json.loads((a/'outer-observation.json').read_text());assert o['session_id']==26365 and o['numeric_exit']==0 and 'not an independent transcript' in o['observation_source']
r=s['rows'][0];assert r['module']==n and r['source_sha256']=='df4419d685971b45d91f3f5ccc6f5f3b841bcf2beeb225a74117cfe46d8bbf1e' and r['object_sha256']=='1f314f12d503005ba4d28d4660a0a95bbde87a2751ef77afb2c64d73569c4f6a'
src=p/'src/DiophantineConsistency'/f'{n}.lean';assert sha(src)==sha(out/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256'] and sha(out/'lib/DiophantineConsistency'/f'{n}.olean')==r['object_sha256'];t=src.read_text()
for x in ['(hc : 0<c)','(hf : 0<f)','(hi : 0<i)','(hstrict : f*f=1+delta a*(i*c*c)*(i*c*c)) : 2≤f','simpa only [one_add_one_eq_two]']:assert x in t
for phase in ('deps','compile'):
 z=r[phase];assert z['exit']==0 and z['stop_reason'] is None and not z['monitor_errors'] and not z['observed_descendant_pids'];assert sha(a/f'{n}-{phase}.txt')==sha(out/f'{n}-{phase}.txt')==z['log_sha256']
log=(a/f'{n}-compile.txt').read_text();assert sha(a/f'{n}-compile.txt')=='ca15f29d039d3d01b6f803caddf317da09f16f84766e2bc0b04a1d5f64ab998c';assert log.count('warning:')==1 and 'error:' not in log and 'sorryAx' not in log and "'DiophantineConsistency.Sign33StrongF.strong_norm_f_ge_two' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
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
assert sha(a/'survey-before.json')==sha(a/'survey-after.json')==sha(out/'survey-before.json')==sha(out/'survey-after.json')=='5e0a12ddb5419503ab2fc2418ee59db3d0185da0a11c2454870c3f17b34fc5f7';survey=json.loads((a/'survey-before.json').read_text());assert survey['status']=='PASS_POINT_PRODUCER_SURVEY'
for name in ('ArithmeticPellFirstIndex','ModelDifferenceRing'):
 k='DiophantineConsistency.'+name;dep=r['dependencies'][k];sel=survey['selected'][k];check(dep['path'],sel['sha256'],sel['realpath']);assert dep['sha256']==sel['sha256'] and dep['realpath']==sel['realpath'] and r['direct_guard'][dep['path']]==sel
v=subprocess.run([sys.executable,'-I','-S','-B',str(p/'provider_survey.py')],capture_output=True,timeout=60);assert v.returncode==0 and not v.stderr and hashlib.sha256(v.stdout).hexdigest()=='5e0a12ddb5419503ab2fc2418ee59db3d0185da0a11c2454870c3f17b34fc5f7'
print(json.dumps({'status':'PASS_TERMINAL_EVIDENCE_ONLY','object_sha256':r['object_sha256'],'author_session':26365,'author_exit':0,'axioms':['propext','Classical.choice','Quot.sound'],'lint_warnings':1,'guard_slots':150,'overlay_links':1162,'scope':'Conditional strong norm lower bound only; no sign33 zero bridge or endpoint, no Lean replay.'},indent=2,sort_keys=True))
