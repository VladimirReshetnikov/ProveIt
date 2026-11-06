import hashlib,json,os,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];p=D/'research/nine-sharing-sign33-current-core-cuts-retry01';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-current-core-cuts-retry01-20261106');n='Sign33CurrentCoreCuts';sha=lambda x:hashlib.sha256(Path(x).read_bytes()).hexdigest()
assert sha(a/'state.json')==sha(out/'state.json')=='7df5e65c8c86be59c6af3f79b2ea99caf493907ea28a4c711efd1d83c679d8e9';s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1
assert sha(p/'run.py')==s['runner_sha256']=='b41adebec2fd5506253f2d0c7e4efdb0c4808ddbbb85d23d5b270ec5e82fd086';assert sha(a/'outer-observation.json')=='7179552c4b2b5d50dec1f7a96b1b259f1feec08869f046ce967fb450d7986742';o=json.loads((a/'outer-observation.json').read_text());assert o['session_id']==64526 and o['numeric_exit']==0 and 'not an independent transcript' in o['observation_source']
r=s['rows'][0];assert r['module']==n and r['source_sha256']=='a84564331e016e1a7b2b2086521daed5376978ef2a561b0aec108fdcd6d0d446' and r['object_sha256']=='1f9a7c639979896a0fbdcc8213a6410c83062953c500a9f9beebd1fa1e75812b'
src=p/'src/DiophantineConsistency'/f'{n}.lean';assert sha(src)==sha(out/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256'] and sha(out/'lib/DiophantineConsistency'/f'{n}.olean')==r['object_sha256'];t=src.read_text()
for x in ['ObjectCurrentEquation2011.InternalZero ObjectCurrentEquation2011.naturalExpression v','let w : Fin 14 → V := fun j => v j+1','Carrier65.core (ModelThirteenCarrier.ringPorts (V := V))','∃ gap tau inner val negative : V','ι tau = d.tau','ι inner = d.c*ι (w 6)-d.rank','ι val = d.V','ι negative = d.y*d.y-d.V*d.V']:assert x in t
for phase in ('deps','compile'):
 z=r[phase];assert z['exit']==0 and z['stop_reason'] is None and not z['monitor_errors'] and not z['observed_descendant_pids'];assert sha(a/f'{n}-{phase}.txt')==sha(out/f'{n}-{phase}.txt')==z['log_sha256']
log=(a/f'{n}-compile.txt').read_text();assert sha(a/f'{n}-compile.txt')=='ccc8c2357bc5e4a03ec3a76670de8a99e34a35af692dcd92f2788b358c0dd1d6';assert log.count('warning:')==0 and 'error:' not in log and 'sorryAx' not in log and "'DiophantineConsistency.Sign33CurrentCoreCuts.five_core_representatives_of_current_zero' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]" in log
cache={}
def check(path,h,rp):
 q=Path(path);assert q.is_file() and str(q.resolve())==rp
 if rp not in cache:cache[rp]=sha(q)
 assert cache[rp]==h
for k,v in r['direct_guard'].items():
 if v is None:assert not os.path.lexists(k)
 else:check(k,v['sha256'],v['realpath'])
for k,v in s['overlay_links'].items():assert Path(k).is_symlink() and str(Path(k).resolve())==v
assert len(r['direct_guard'])==200 and len(s['overlay_links'])==1172
assert sha(a/'survey-before.json')==sha(a/'survey-after.json')==sha(out/'survey-before.json')==sha(out/'survey-after.json')=='3c14a08aab4c2d6316b0647a9d5952881fccfe5732c3fdde01a26b1f64bd165e';survey=json.loads((a/'survey-before.json').read_text());assert survey['status']=='PASS_POINT_PRODUCER_SURVEY'
for k in ('DiophantineConsistency.Sign33CurrentFiveWitnesses','DiophantineConsistency.Sign33CurrentWindows','DiophantineConsistency.ModelThirteenCoreInvariants'):
 dep=r['dependencies'][k];sel=survey['selected'][k];check(dep['path'],sel['sha256'],sel['realpath']);assert dep['sha256']==sel['sha256'] and dep['realpath']==sel['realpath'] and r['direct_guard'][dep['path']]==sel
v=subprocess.run([sys.executable,'-I','-S','-B',str(p/'provider_survey.py')],capture_output=True,timeout=60);assert v.returncode==0 and not v.stderr and hashlib.sha256(v.stdout).hexdigest()=='3c14a08aab4c2d6316b0647a9d5952881fccfe5732c3fdde01a26b1f64bd165e'
print(json.dumps({'status':'PASS_TERMINAL_EVIDENCE_ONLY','object_sha256':r['object_sha256'],'author_session':64526,'author_exit':0,'axioms':['propext','Classical.choice','Quot.sound'],'lint_warnings':0,'guard_slots':200,'overlay_links':1172,'scope':'Source-zero to five Carrier65 core representatives only; no concrete 33-variable seed bridge or endpoint, no Lean replay.'},indent=2,sort_keys=True))
