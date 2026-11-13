from pathlib import Path
from hashlib import sha256
import json,subprocess,sys
h=Path('research/trace75-bfs-field-markers-prototype');obs=h/'observations/attempt01';outer=h/'observations/outer-attempt01'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
p=obs/'result.json';assert sha(p)=='30bc3205b4bd21130e871e518c9360e04cb3db4918cc17b2bcfdb1dc8ed0f18b';j=json.loads(p.read_text());assert j['status']=='PASS'
p=outer/'terminal.json';assert sha(p)=='b876e772806063052002332cf1c2572e0c2896da60d44e36a7e32539dedc4695';o=json.loads(p.read_text());assert o['exit']==0 and o['child_result_sha256']==sha(obs/'result.json') and o['inputs_before']==o['inputs_after'];assert sha(h/'run.py')==o['inputs_before'][str((h/'run.py').resolve())]==j['runner_sha256']=='963a9d01db7c84c876529a42fd38c5ae6c0bd5526b19a513ccee8b11cdbd20c1' and o['wrapper_sha256_before']==o['wrapper_sha256_after']==sha(h/'run-outer.py')=='998537aa1506b74d08f130d4bf8d324858d120ee1da3e9fd53f6b242339fa44e'
for p,v in o['inputs_before'].items():assert sha(p)==v
for p,v in j['inputs'].items():assert sha(p)==v
for s in ['stdout','stderr']:assert sha(outer/s)==o[s+'_sha256']
assert not (outer/'stderr').read_text()
root=Path(j['output_root']);source=root/'Trace75BFSFieldMarkers.lean';object=root/'Trace75BFSFieldMarkers.olean';assert sha(source)==sha(obs/'source.txt')==sha(h/'Trace75BFSFieldMarkers.lean')=='3c52b846ca5faffcd8cd97e69bd796277da73b40b0f8b1f5ae6cf5e3d91ff5ba';assert sha(object)==j['object_sha256']=='70c92a5033178fa7b102ef545bc9ba24b3e9addd2ca161930108ec10641a1ea4' and not object.is_symlink()
assert {str(p.relative_to(root)) for p in root.rglob('*') if p.is_file() or p.is_symlink()}=={source.name,object.name}
st=j['stage'];hd=j['header'];assert st['status']=='PASS' and st['exit']==0 and st['reason'] is None and hd['status']=='PASS' and hd['exit']==0 and hd['reason'] is None
for tag,r in [('',st),('header.',hd)]:
 for s in ['stdout','stderr']:assert sha(obs/(tag+s))==r[s+'_sha256']
 assert not (obs/(tag+'stderr')).read_text()
assert (obs/'stdout').read_text()=="'Trace75BFSFieldMarkers.graph_field_markers' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
lines=(obs/'header.stdout').read_text().splitlines();assert lines[0]=='BEGIN '+str(object) and lines[-1]=='END';imps=[x[7:] for x in lines[1:-1] if x.startswith('IMPORT ')];assert len(imps)==len(lines)-2 and imps==j['header_imports'] and [x for x in imps if x!='Init']==['Trace75BFSUniformReset','Trace75BFSSupport','Trace75FixedSlots','DirectBFSFieldParity','DirectBFSMarkerParity','DiophantineConsistency.FieldWindowParity','DiophantineConsistency.WholeBlockTemporal']
assert st['env']==j['env'] and hd['env']=={'PATH':'/usr/bin:/bin'}
p=subprocess.run([sys.executable,'-I','-S','-B','reviews/trace75-bfs-field-markers-runner-independent/check.py'],capture_output=True,text=True);assert p.returncode==0,p.stderr
print(p.stdout.strip());print('PASS: actual outer and Lean/header exits 0, exact seven imported modules, source/object/report hashes and current union/provider subtrees rechecked; no independent Lean replay.')
