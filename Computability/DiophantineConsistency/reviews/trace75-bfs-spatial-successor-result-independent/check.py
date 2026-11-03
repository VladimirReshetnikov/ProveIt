from pathlib import Path
from hashlib import sha256
import json,subprocess,sys
h=Path('research/trace75-bfs-spatial-successor-prototype');obs=h/'observations/attempt01';outer=h/'observations/outer-attempt01'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
p=obs/'result.json';assert sha(p)=='24c98a5979883eaa56cbf7992de814fd3eb6b33dd7b8daa156bf08af870ddd7b';j=json.loads(p.read_text());assert j['status']=='PASS'
p=outer/'terminal.json';assert sha(p)=='eaa49e8dbfb20e32fa5b56b39a361dd7622f33ba5772e69cbf16640488221f28';o=json.loads(p.read_text());assert o['exit']==0 and o['child_result_sha256']==sha(obs/'result.json') and o['inputs_before']==o['inputs_after'];assert sha(h/'run.py')==o['inputs_before'][str((h/'run.py').resolve())]==j['runner_sha256']=='a57a4d39b56d5ee9fc60de66305da5a8ba319d6893a376fa2ee18fd4946a0b5f' and o['wrapper_sha256_before']==o['wrapper_sha256_after']==sha(h/'run-outer.py')=='237166caa1f01c19b583ebbc4eb5ae46033eadb79bad405694a5edea184f0c96'
for p,v in o['inputs_before'].items():assert sha(p)==v
for p,v in j['inputs'].items():assert sha(p)==v
for s in ['stdout','stderr']:assert sha(outer/s)==o[s+'_sha256']
assert not (outer/'stderr').read_text()
root=Path(j['output_root']);source=root/'Trace75BFSSpatialSuccessor.lean';object=root/'Trace75BFSSpatialSuccessor.olean';assert sha(source)==sha(obs/'source.txt')==sha(h/'Trace75BFSSpatialSuccessor.lean')=='d3b6373004b16f7c4c1517e8f2f4289760ce9df2c841b028acb072c98ffb000b';assert sha(object)==j['object_sha256']=='d028374852aed078f8c1a54c660787999bfbca195fac66278a73ed293f7e28af' and not object.is_symlink()
assert {str(p.relative_to(root)) for p in root.rglob('*') if p.is_file() or p.is_symlink()}=={source.name,object.name}
st=j['stage'];hd=j['header'];assert st['status']=='PASS' and st['exit']==0 and st['reason'] is None and hd['status']=='PASS' and hd['exit']==0 and hd['reason'] is None
for tag,r in [('',st),('header.',hd)]:
 for s in ['stdout','stderr']:assert sha(obs/(tag+s))==r[s+'_sha256']
 assert not (obs/(tag+'stderr')).read_text()
assert (obs/'stdout').read_text()=="'Trace75BFSSpatialSuccessor.graph_spatial_successor' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
lines=(obs/'header.stdout').read_text().splitlines();assert lines[0]=='BEGIN '+str(object) and lines[-1]=='END';imps=[x[7:] for x in lines[1:-1] if x.startswith('IMPORT ')];assert len(imps)==len(lines)-2 and imps==j['header_imports'] and [x for x in imps if x!='Init']==['Trace75BFSUniformDecoder','Trace75BFSSupport','Trace75BFSFieldMarkers','DirectBFSBlockOrbit','DiophantineConsistency.BlockCyclicIndex']
assert st['env']==j['env'] and hd['env']=={'PATH':'/usr/bin:/bin'}
p=subprocess.run([sys.executable,'-I','-S','-B','reviews/trace75-bfs-spatial-successor-runner-independent/check.py'],capture_output=True,text=True);assert p.returncode==0,p.stderr
print(p.stdout.strip());print('PASS: actual outer and Lean/header exits 0, exact five imported modules, source/object/report hashes and current union/provider subtrees rechecked; no independent Lean replay.')
