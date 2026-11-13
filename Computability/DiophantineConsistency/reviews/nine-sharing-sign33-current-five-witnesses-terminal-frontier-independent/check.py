import hashlib,json,os,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];p=D/'research/nine-sharing-sign33-current-five-witnesses-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-current-five-witnesses-check-20261106');n='Sign33CurrentFiveWitnesses';sha=lambda x:hashlib.sha256(Path(x).read_bytes()).hexdigest()
assert sha(a/'state.json')==sha(out/'state.json')=='8d3ff4f3074da6a298a525d6963959ca7addf67795fb298cc040c238dca4eadf';s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1
assert sha(p/'run.py')==s['runner_sha256']=='d7cdbbaa814a3e93ab4ecf97ff36f14b0e4e78d764b1f9737bbc9f09bcb8e147';assert sha(a/'outer-observation.json')=='1a30380636a80965bfa379a2ef9a2eac2439d34605b1909fb1ede4d53b952782';o=json.loads((a/'outer-observation.json').read_text());assert o['session_id']==90586 and o['numeric_exit']==0 and 'not an independent transcript' in o['observation_source']
r=s['rows'][0];assert r['module']==n and r['source_sha256']=='e9ee97d30688a955ad586263f446f4b03e8ce3989377397706cc692f6b0ab5ba' and r['object_sha256']=='ab27659865533dcc9a8548478c7ba4286192ef265401f82e8dc732cee0b7d28a'
src=p/'src/DiophantineConsistency'/f'{n}.lean';assert sha(src)==sha(out/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256'] and sha(out/'lib/DiophantineConsistency'/f'{n}.olean')==r['object_sha256'];t=src.read_text()
for x in ['ObjectCurrentEquation2011.InternalZero ObjectCurrentEquation2011.naturalExpression v','let w : Fin 14 → V := fun j => v j+1','CurrentMasks2011.highPort+CurrentMasks2011.beta : ℕ','let S := delta a*w 5*c*c','let x := w 4*w 4*c*w 6','let z := w 4*w 4*r+c','∃ gap tau inner val negative : V','ι negative = ι (w 12)*ι (w 12)-(ι x-ι z)*(ι x-ι z)']:assert x in t
for phase in ('deps','compile'):
 z=r[phase];assert z['exit']==0 and z['stop_reason'] is None and not z['monitor_errors'] and not z['observed_descendant_pids'];assert sha(a/f'{n}-{phase}.txt')==sha(out/f'{n}-{phase}.txt')==z['log_sha256']
log=(a/f'{n}-compile.txt').read_text();assert sha(a/f'{n}-compile.txt')=='86c7daef3dd91070aa3d73c1e0f69817b3f474546152134646ad9effef3cc431';assert log.count('warning:')==0 and 'error:' not in log and 'sorryAx' not in log and "'DiophantineConsistency.Sign33CurrentFiveWitnesses.five_witnesses_of_current_zero' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]" in log
cache={}
def check(path,h,rp):
 q=Path(path);assert q.is_file() and str(q.resolve())==rp
 if rp not in cache:cache[rp]=sha(q)
 assert cache[rp]==h
for k,v in r['direct_guard'].items():
 if v is None:assert not os.path.lexists(k)
 else:check(k,v['sha256'],v['realpath'])
for k,v in s['overlay_links'].items():assert Path(k).is_symlink() and str(Path(k).resolve())==v
assert len(r['direct_guard'])==200 and len(s['overlay_links'])==1171
assert sha(a/'survey-before.json')==sha(a/'survey-after.json')==sha(out/'survey-before.json')==sha(out/'survey-after.json')=='e6e7b306e3ab6460f28362a335d4173f83197c176ba75f44d13bd0223a1846d5';survey=json.loads((a/'survey-before.json').read_text());assert survey['status']=='PASS_POINT_PRODUCER_SURVEY'
for k in ('DiophantineConsistency.Sign33CurrentWindows','DiophantineConsistency.Sign33FiveWitnesses','DiophantineConsistency.ArithmeticCarrierSoundness2011'):
 dep=r['dependencies'][k];sel=survey['selected'][k];check(dep['path'],sel['sha256'],sel['realpath']);assert dep['sha256']==sel['sha256'] and dep['realpath']==sel['realpath'] and r['direct_guard'][dep['path']]==sel
v=subprocess.run([sys.executable,'-I','-S','-B',str(p/'provider_survey.py')],capture_output=True,timeout=60);assert v.returncode==0 and not v.stderr and hashlib.sha256(v.stdout).hexdigest()=='e6e7b306e3ab6460f28362a335d4173f83197c176ba75f44d13bd0223a1846d5'
print(json.dumps({'status':'PASS_TERMINAL_EVIDENCE_ONLY','object_sha256':r['object_sha256'],'author_session':90586,'author_exit':0,'axioms':['propext','Classical.choice','Quot.sound'],'lint_warnings':0,'guard_slots':200,'overlay_links':1171,'scope':'Current source zero to five natural representatives only; no concrete 33-variable seed bridge or endpoint, no Lean replay.'},indent=2,sort_keys=True))
