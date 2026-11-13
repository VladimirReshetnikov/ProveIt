from pathlib import Path
from hashlib import sha256
import json,subprocess,sys
h=Path('research/trace75-bfs-uniform-reset-prototype');obs=h/'observations/attempt01';outer=h/'observations/outer-attempt01'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
p=obs/'result.json';assert sha(p)=='252268f327d68dd2ff352a2229a54d053bc6fd324a0f2bf483f2e19a8861ac9f';j=json.loads(p.read_text());assert j['status']=='PASS'
p=outer/'terminal.json';assert sha(p)=='a4da339bb4e2527533e23a91b4624c1b51fc28b050592305a1704dfcc424ea07';o=json.loads(p.read_text());assert o['exit']==0 and o['child_result_sha256']==sha(obs/'result.json') and o['inputs_before']==o['inputs_after'];assert sha(h/'run.py')==o['inputs_before'][str((h/'run.py').resolve())]==j['runner_sha256']=='a0fcdb3355c1a9c46205c7db2691268aa95734aaff490e96c231ce111dac8c88' and o['wrapper_sha256_before']==o['wrapper_sha256_after']==sha(h/'run-outer.py')=='1e718c5b9953590aa5a5053496caafb48c2de28e8a2cda8cdd0d17b87fb33a3e'
for p,v in o['inputs_before'].items():assert sha(p)==v
for p,v in j['inputs'].items():assert sha(p)==v
for s in ['stdout','stderr']:assert sha(outer/s)==o[s+'_sha256']
assert not (outer/'stderr').read_text()
root=Path(j['output_root']);source=root/'Trace75BFSUniformReset.lean';object=root/'Trace75BFSUniformReset.olean';assert sha(source)==sha(obs/'source.txt')==sha(h/'Trace75BFSUniformReset.lean')=='99d0a2dc08e267ed1e6cb25038fef47c6476024bb6a2b62107e0b1c263849e55';assert sha(object)==j['object_sha256']=='1c99b1ac2130c05c832de7041c7bed41562daf056faeaaa5220e5cc92eeeb335' and not object.is_symlink()
assert {str(p.relative_to(root)) for p in root.rglob('*') if p.is_file() or p.is_symlink()}=={source.name,object.name}
st=j['stage'];hd=j['header'];assert st['status']=='PASS' and st['exit']==0 and st['reason'] is None and hd['status']=='PASS' and hd['exit']==0 and hd['reason'] is None
for tag,r in [('',st),('header.',hd)]:
 for s in ['stdout','stderr']:assert sha(obs/(tag+s))==r[s+'_sha256']
 assert not (obs/(tag+'stderr')).read_text()
assert (obs/'stdout').read_text()=="'Trace75BFSUniformReset.graph_uniform_reset' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
lines=(obs/'header.stdout').read_text().splitlines();assert lines[0]=='BEGIN '+str(object) and lines[-1]=='END';imps=[x[7:] for x in lines[1:-1] if x.startswith('IMPORT ')];assert len(imps)==len(lines)-2 and imps==j['header_imports'] and [x for x in imps if x!='Init']==['Trace75BFSCellShift','Trace75BFSSupport','DiophantineConsistency.WholeBlockTemporal']
assert st['env']==j['env'] and hd['env']=={'PATH':'/usr/bin:/bin'}
p=subprocess.run([sys.executable,'-I','-S','-B','reviews/trace75-bfs-uniform-reset-runner-independent/check.py'],capture_output=True,text=True);assert p.returncode==0,p.stderr
print(p.stdout.strip());print('PASS: actual outer and Lean/header exits 0, exact three imported modules, source/object/report hashes and current union/provider subtrees rechecked; no independent Lean replay.')
