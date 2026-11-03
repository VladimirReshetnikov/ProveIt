from pathlib import Path
from hashlib import sha256
import json,subprocess,sys
h=Path('research/trace75-bfs-cell-shift-prototype');obs=h/'observations/attempt01';outer=h/'observations/outer-attempt01'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
p=obs/'result.json';assert sha(p)=='57660aa69e2ecde3b0e10c20f0edb01681f7774d04c80a1c1d7b06e081f7caa3';j=json.loads(p.read_text());assert j['status']=='PASS'
p=outer/'terminal.json';assert sha(p)=='48bca5b09f8b1b8759bf2258bb5e21220d567b954d1220ca9644a09165f85944';o=json.loads(p.read_text());assert o['exit']==0 and o['child_result_sha256']==sha(obs/'result.json') and o['inputs_before']==o['inputs_after'];assert sha(h/'run.py')==o['inputs_before'][str((h/'run.py').resolve())]==j['runner_sha256']=='019aed0d7e29601dfd3728dbe329fb26f0030a006b0fa0620d1e2017aaa17095' and o['wrapper_sha256_before']==o['wrapper_sha256_after']==sha(h/'run-outer.py')=='1eb3737eef6560eaa0885d0137120b25818a4ee50f35ffc1df2a34252510c7a9'
for p,v in o['inputs_before'].items():assert sha(p)==v
for p,v in j['inputs'].items():assert sha(p)==v
for s in ['stdout','stderr']:assert sha(outer/s)==o[s+'_sha256']
assert not (outer/'stderr').read_text()
root=Path(j['output_root']);source=root/'Trace75BFSCellShift.lean';object=root/'Trace75BFSCellShift.olean';assert sha(source)==sha(obs/'source.txt')==sha(h/'Trace75BFSCellShift.lean')=='b71baea359fe136c823fed0d7b462a159f5245a7eb5e2e242766edca64af5f83';assert sha(object)==j['object_sha256']=='757b5a9f37ede9d67c75b97714f68d2c5c2c48c48cdd8845145ccadb82e047b8' and not object.is_symlink()
assert {str(p.relative_to(root)) for p in root.rglob('*') if p.is_file() or p.is_symlink()}=={source.name,object.name}
st=j['stage'];hd=j['header'];assert st['status']=='PASS' and st['exit']==0 and st['reason'] is None and hd['status']=='PASS' and hd['exit']==0 and hd['reason'] is None
for tag,r in [('',st),('header.',hd)]:
 for s in ['stdout','stderr']:assert sha(obs/(tag+s))==r[s+'_sha256']
 assert not (obs/(tag+'stderr')).read_text()
assert (obs/'stdout').read_text()=="'Trace75BFSCellShift.graph_cell_shift' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
lines=(obs/'header.stdout').read_text().splitlines();assert lines[0]=='BEGIN '+str(object) and lines[-1]=='END';imps=[x[7:] for x in lines[1:-1] if x.startswith('IMPORT ')];assert len(imps)==len(lines)-2 and imps==j['header_imports'] and [x for x in imps if x!='Init']==['Trace75BFSAlignedShift','Trace75BFSSupport','Trace75FixedDigits','DiophantineConsistency.AlignedAnchorModel','DiophantineConsistency.SymbolicKBandDraft','Trace75BFSSimpleParity','Trace75BFSOccupied','DirectBFSCarryRoom','DiophantineConsistency.FractionalAnchorConflict','DiophantineConsistency.OccupiedNamedSlots']
assert st['env']==j['env'] and hd['env']=={'PATH':'/usr/bin:/bin'}
p=subprocess.run([sys.executable,'-I','-S','-B','reviews/trace75-bfs-cell-shift-runner-independent/check.py'],capture_output=True,text=True);assert p.returncode==0,p.stderr
print(p.stdout.strip());print('PASS: actual outer and Lean/header exits 0, exact ten imported modules, source/object/report hashes and current union/provider subtrees rechecked; no independent Lean replay.')
