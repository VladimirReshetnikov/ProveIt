#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-seed-current-source-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-seed-current-source-check-20261106');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'state.json':'4f03aa9a1581b620688ef516dfe3c5156253dc6cf47be04f1dc348775093f265','Sign33SeedSource-compile.txt':'ed69664f7b9506cc0556331522435617f705964e7571b9a57bf4d32fdf9d8317','Sign33CurrentSeedSource-compile.txt':'48bc2200174632932b9ea98fd0a0c30e6dc353ce535531045f1c7efc7b79940a','outer-observation.json':'2af3d955e845f5b86edc476372eb7e5274d99a0f28264e1d6a6b5f6d363a6427'}.items():assert sha(a/n)==h
o=json.loads((a/'outer-observation.json').read_text());assert (o['session_id'],o['numeric_exit'])==(3154,1);s=json.loads((a/'state.json').read_text());assert s['status']=='FAILED' and len(s['rows'])==2 and len(s['overlay_links'])==1217
objects=['d1575bc682b709f677efb2a33b562886e87d8b96f384f23a73f55d8b7933fa77',None];names=['Sign33SeedSource','Sign33CurrentSeedSource'];pins=['52d26b985ccebc8d055d3ce250cc6885b8346607e4bc0ac96c92eaa48ee050ef','77b0624fb62992bbeb9c8d1ad219e225ba33c7dc90b7f072bb33bc118debca6b']
for i,(r,n,h,pin) in enumerate(zip(s['rows'],names,objects,pins)):
 assert r['module']==n and r['source_sha256']==pin and sha(p/'src/DiophantineConsistency'/f'{n}.lean')==pin
 for phase in ('deps','compile'):
  x=r[phase];assert x['exit']==(0 if phase=='deps' or i==0 else -6) and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert sha(a/f'{n}-{phase}.txt')==x['log_sha256']
 assert r.get('object_sha256')==h
 if h:assert sha(out/'lib/DiophantineConsistency'/f'{n}.olean')==h
 else:assert not (out/'lib/DiophantineConsistency'/f'{n}.olean').exists()
 assert len(r['direct_guard'])==(150 if i==0 else 300)
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
log=(a/'Sign33SeedSource-compile.txt').read_text();assert re.search(r"'DiophantineConsistency\.Sign33SeedSource\.seed_implies_source' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log) and 'warning:' not in log and 'sorryAx' not in log
failed=(a/'Sign33CurrentSeedSource-compile.txt').read_text();assert "lean::memory_exception" in failed and "'interpreter'" in failed
expected=[{'Sign33AllCutsSource':'9518aba7d4f0ba9a988284315ace952cbfc8bf6f09865aef1f46ca29d46a5c05','Sign33ResidualIff':'33eb8b457ea09983d4591856171a37bd8e625dd4cf2d712dbcd621290b5fe204'},{'Sign33SeedSource':objects[0],'Norm38CurrentPort0':'0d5bc92d8592aa838671b36237f28b8bcca9bbdfceaf22877f99613d8ea55c43','Norm38CurrentPort1':'6429224b975688f1407395a7285c68fc716dd253a4bb11d2bdd175773ec30d86','Norm38CurrentPort2':'864dcedb4ccedd7af39f7704b999570b908a7f25b58519c75b0956e45f6a1eb2','Norm38CurrentPort3':'507e816bc8faf4b38f2e17a06dd15e67e9f1307e769b19cb776db17274eff57c'}]
for r,e in zip(s['rows'],expected):
 for mod,h in e.items():
  dep=r['dependencies']['DiophantineConsistency.'+mod];assert dep['sha256']==h and r['direct_guard'][dep['path']]=={'sha256':h,'realpath':dep['realpath']}
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
assert not (a/'survey-after.json').exists()
print(json.dumps({'status':'PASS_FAILURE_AUDIT','author_recorded_outer_session':3154,'generic_stage':'PASS','current_stage':'Lean -6 interpreter memory exception','guard_slots':450,'overlay_links':1217,'scope':'generic conditional theorem only; no current specialization; no Lean replay'},indent=2,sort_keys=True))
