from pathlib import Path
from hashlib import sha256
import json,subprocess,sys
h=Path('research/trace75-bfs-occupied-prototype');obs=h/'observations/attempt01';outer=h/'observations/outer-attempt01'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
p=obs/'result.json';assert sha(p)=='ec5cb21bb0c36527ad05a4474d0b9a1cff598a504a6a2a2d4a754471b041d633';j=json.loads(p.read_text());assert j['status']=='PASS'
p=outer/'terminal.json';assert sha(p)=='fe59f80dd0339adf513b65d763402c5977ec67afd2f4e4ce269f7e219c96baf1';o=json.loads(p.read_text());assert o['exit']==0 and o['child_result_sha256']==sha(obs/'result.json') and o['inputs_before']==o['inputs_after'];assert sha(h/'run.py')==o['inputs_before'][str((h/'run.py').resolve())]==j['runner_sha256']=='856acbd45cd41f4e30007b13f5016e469f37d5e464eb7b96f391a0221cddcd3a' and o['wrapper_sha256_before']==o['wrapper_sha256_after']==sha(h/'run-outer.py')=='186bd5548f3e42831545eaad2892c8f9591f6e25ff334bb5ef7821740a8e2657'
for p,v in o['inputs_before'].items():assert sha(p)==v
for p,v in j['inputs'].items():assert sha(p)==v
for s in ['stdout','stderr']:assert sha(outer/s)==o[s+'_sha256']
assert not (outer/'stderr').read_text()
root=Path(j['output_root']);source=root/'Trace75BFSOccupied.lean';object=root/'Trace75BFSOccupied.olean';assert sha(source)==sha(obs/'source.txt')==sha(h/'Trace75BFSOccupied.lean')=='a82d245ff3c009d1afbb8807c10bfbd1e30167d930d34313238edf8079da47a3';assert sha(object)==j['object_sha256']=='ea99101894f3575e4846087cc0b798843c6ecea62ca1164bd320c2ebd7c23ad8' and not object.is_symlink()
assert {str(p.relative_to(root)) for p in root.rglob('*') if p.is_file() or p.is_symlink()}=={source.name,object.name}
st=j['stage'];hd=j['header'];assert st['status']=='PASS' and st['exit']==0 and st['reason'] is None and hd['status']=='PASS' and hd['exit']==0 and hd['reason'] is None
for tag,r in [('',st),('header.',hd)]:
 for s in ['stdout','stderr']:assert sha(obs/(tag+s))==r[s+'_sha256']
 assert not (obs/(tag+'stderr')).read_text()
assert (obs/'stdout').read_text()=="'Trace75BFSOccupied.graph_occupied' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
lines=(obs/'header.stdout').read_text().splitlines();assert lines[0]=='BEGIN '+str(object) and lines[-1]=='END';imps=[x[7:] for x in lines[1:-1] if x.startswith('IMPORT ')];assert len(imps)==len(lines)-2 and imps==j['header_imports'] and [x for x in imps if x!='Init']==['Trace75BFSCleanCarry','Trace75BFSSupport','Trace75FixedSlots','DirectBFSSelectedOrigin','DirectBFSForeignBands','DiophantineConsistency.SelectedBandWord','DiophantineConsistency.HighMaskLocal']
assert st['env']==j['env'] and hd['env']=={'PATH':'/usr/bin:/bin'}
p=subprocess.run([sys.executable,'-I','-S','-B','reviews/trace75-bfs-occupied-runner-independent/check.py'],capture_output=True,text=True);assert p.returncode==0,p.stderr
print(p.stdout.strip());print('PASS: actual outer and Lean/header exits 0, exact seven imported modules, source/object/report hashes and current union/provider subtrees rechecked; no independent Lean replay.')
