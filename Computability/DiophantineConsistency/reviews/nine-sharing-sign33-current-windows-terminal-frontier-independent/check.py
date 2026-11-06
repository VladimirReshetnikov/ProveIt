import hashlib,json,os,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];p=D/'research/nine-sharing-sign33-current-windows-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-current-windows-check-20261106');n='Sign33CurrentWindows';sha=lambda x:hashlib.sha256(Path(x).read_bytes()).hexdigest()
assert sha(a/'state.json')==sha(out/'state.json')=='ed0ee11bdf097d8d844da870cd9c2191f861d7e7f5e23bdf53114648f1bf64db';s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1
assert sha(p/'run.py')==s['runner_sha256']=='2306604b919e07a84eb7367dc0219f64a322f32c4b4ed8ad2fbb56fd5f4ff084';assert sha(a/'outer-observation.json')=='8ffee81f6b6c421d5b1099b344140fce00e6effba874bf558c54b80d1f23cf9c';o=json.loads((a/'outer-observation.json').read_text());assert o['session_id']==43875 and o['numeric_exit']==0 and 'not an independent transcript' in o['observation_source']
r=s['rows'][0];assert r['module']==n and r['source_sha256']=='ac17e913b7abcd7a398221ff9e93fc4b6648eece6ba27f6737a600eaaa4d9ed3' and r['object_sha256']=='a2fd0bcecb4cea0625245a5d4bd2949848fe5b39a2f6932f6de095283894e521'
src=p/'src/DiophantineConsistency'/f'{n}.lean';assert sha(src)==sha(out/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256'] and sha(out/'lib/DiophantineConsistency'/f'{n}.olean')==r['object_sha256'];t=src.read_text()
for x in ['ObjectCurrentEquation2011.InternalZero ObjectCurrentEquation2011.naturalExpression v','let w : Fin 14 → V := fun j => v j+1','CurrentMasks2011.highPort+CurrentMasks2011.beta : ℕ','0<q-w 1-w 2 ∧ r+2<E ∧ 2*r<c','ArithmeticCarrierSoundness2011.current_natural_equations v hz']:assert x in t
for phase in ('deps','compile'):
 z=r[phase];assert z['exit']==0 and z['stop_reason'] is None and not z['monitor_errors'] and not z['observed_descendant_pids'];assert sha(a/f'{n}-{phase}.txt')==sha(out/f'{n}-{phase}.txt')==z['log_sha256']
log=(a/f'{n}-compile.txt').read_text();assert sha(a/f'{n}-compile.txt')=='481b7e6fabd532c3bb397bf766b6847abf742f2707b25b8e02955638fa5af464';assert log.count('warning:')==0 and 'error:' not in log and 'sorryAx' not in log and "'DiophantineConsistency.Sign33CurrentWindows.windows_of_current_zero' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]" in log
cache={}
def check(path,h,rp):
 q=Path(path);assert q.is_file() and str(q.resolve())==rp
 if rp not in cache:cache[rp]=sha(q)
 assert cache[rp]==h
for k,v in r['direct_guard'].items():
 if v is None:assert not os.path.lexists(k)
 else:check(k,v['sha256'],v['realpath'])
for k,v in s['overlay_links'].items():assert Path(k).is_symlink() and str(Path(k).resolve())==v
assert len(r['direct_guard'])==150 and len(s['overlay_links'])==1164
assert sha(a/'survey-before.json')==sha(a/'survey-after.json')==sha(out/'survey-before.json')==sha(out/'survey-after.json')=='07fe7fdd5131921c5edca868a6696d3990f37d09ae0c15a3ea43886f6217610d';survey=json.loads((a/'survey-before.json').read_text());assert survey['status']=='PASS_POINT_PRODUCER_SURVEY'
for k in ('DiophantineConsistency.Sign33Windows','DiophantineConsistency.ArithmeticCarrierSoundness2011'):
 dep=r['dependencies'][k];sel=survey['selected'][k];check(dep['path'],sel['sha256'],sel['realpath']);assert dep['sha256']==sel['sha256'] and dep['realpath']==sel['realpath'] and r['direct_guard'][dep['path']]==sel
v=subprocess.run([sys.executable,'-I','-S','-B',str(p/'provider_survey.py')],capture_output=True,timeout=60);assert v.returncode==0 and not v.stderr and hashlib.sha256(v.stdout).hexdigest()=='07fe7fdd5131921c5edca868a6696d3990f37d09ae0c15a3ea43886f6217610d'
print(json.dumps({'status':'PASS_TERMINAL_EVIDENCE_ONLY','object_sha256':r['object_sha256'],'author_session':43875,'author_exit':0,'axioms':['propext','Classical.choice','Quot.sound'],'lint_warnings':0,'guard_slots':150,'overlay_links':1164,'scope':'Current source-zero natural windows only; no sign33 zero bridge or endpoint, no Lean replay.'},indent=2,sort_keys=True))
