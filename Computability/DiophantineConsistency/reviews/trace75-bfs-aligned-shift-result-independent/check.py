from pathlib import Path
from hashlib import sha256
import json,subprocess,sys
h=Path('research/trace75-bfs-aligned-shift-prototype');obs=h/'observations/attempt01';outer=h/'observations/outer-attempt01'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
p=obs/'result.json';assert sha(p)=='76788e416a7ed045716de97e103d2346cdee29f306acfcbb49447e5a834d33da';j=json.loads(p.read_text());assert j['status']=='PASS'
p=outer/'terminal.json';assert sha(p)=='953c46e5cafe93266535b854948af27535999bdac7510c614f655561d7fa3f9f';o=json.loads(p.read_text());assert o['exit']==0 and o['child_result_sha256']==sha(obs/'result.json') and o['inputs_before']==o['inputs_after'];assert sha(h/'run.py')==o['inputs_before'][str((h/'run.py').resolve())]==j['runner_sha256']=='a70f0187f405c0e74fdab628140be37a151eec8bad54e9a0bc4e5356698aca6d' and o['wrapper_sha256_before']==o['wrapper_sha256_after']==sha(h/'run-outer.py')=='ab203382c74e333ee652a572d1a9d32744ed099ccda94667dc43d679c1eac528'
for p,v in o['inputs_before'].items():assert sha(p)==v
for p,v in j['inputs'].items():assert sha(p)==v
for s in ['stdout','stderr']:assert sha(outer/s)==o[s+'_sha256']
assert not (outer/'stderr').read_text()
root=Path(j['output_root']);source=root/'Trace75BFSAlignedShift.lean';object=root/'Trace75BFSAlignedShift.olean';assert sha(source)==sha(obs/'source.txt')==sha(h/'Trace75BFSAlignedShift.lean')=='c98252d1ecb692a8346539c1a043228535e43fd120f0409175a157628ff83453';assert sha(object)==j['object_sha256']=='e031954c734ca8bbecf74a134acb9bfe2bdeeccebe2550f1a79e85dda76deb64' and not object.is_symlink()
assert {str(p.relative_to(root)) for p in root.rglob('*') if p.is_file() or p.is_symlink()}=={source.name,object.name}
st=j['stage'];hd=j['header'];assert st['status']=='PASS' and st['exit']==0 and st['reason'] is None and hd['status']=='PASS' and hd['exit']==0 and hd['reason'] is None
for tag,r in [('',st),('header.',hd)]:
 for s in ['stdout','stderr']:assert sha(obs/(tag+s))==r[s+'_sha256']
 assert not (obs/(tag+'stderr')).read_text()
assert (obs/'stdout').read_text()=="'Trace75BFSAlignedShift.graph_aligned_shift' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
lines=(obs/'header.stdout').read_text().splitlines();assert lines[0]=='BEGIN '+str(object) and lines[-1]=='END';imps=[x[7:] for x in lines[1:-1] if x.startswith('IMPORT ')];assert len(imps)==len(lines)-2 and imps==j['header_imports'] and [x for x in imps if x!='Init']==['Trace75BFSSimpleParity','Trace75BFSSupport','Trace75BFSOccupied','DirectBFSCarryRoom','DiophantineConsistency.FractionalAnchorConflict','DiophantineConsistency.OccupiedNamedSlots']
assert st['env']==j['env'] and hd['env']=={'PATH':'/usr/bin:/bin'}
p=subprocess.run([sys.executable,'-I','-S','-B','reviews/trace75-bfs-aligned-shift-runner-independent/check.py'],capture_output=True,text=True);assert p.returncode==0,p.stderr
print(p.stdout.strip());print('PASS: actual outer and Lean/header exits 0, exact six imported modules, source/object/report hashes and current union/provider subtrees rechecked; no independent Lean replay.')
