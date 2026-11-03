from pathlib import Path
from hashlib import sha256
import json,subprocess,sys
h=Path('research/trace75-bfs-uniform-decoder-prototype');obs=h/'observations/attempt01';outer=h/'observations/outer-attempt01'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
p=obs/'result.json';assert sha(p)=='459c9d8576ce39bd96bdbfa4da34640d2e0705ce0ea03f46768695c8b4196c54';j=json.loads(p.read_text());assert j['status']=='PASS'
p=outer/'terminal.json';assert sha(p)=='6e1ddc62d434c95e160648607e2e66133561fefabcb7fb365a5fd1fb57d7c25e';o=json.loads(p.read_text());assert o['exit']==0 and o['child_result_sha256']==sha(obs/'result.json') and o['inputs_before']==o['inputs_after'];assert sha(h/'run.py')==o['inputs_before'][str((h/'run.py').resolve())]==j['runner_sha256']=='57a11f6730d5c6953e50c5e43f385187589f4c96abeb97e0b7836b33c757e6d1' and o['wrapper_sha256_before']==o['wrapper_sha256_after']==sha(h/'run-outer.py')=='3db2cecaafc8930cb2a7171e09fcea5f6bb0bc168f590e58c3ce780dee89b5e9'
for p,v in o['inputs_before'].items():assert sha(p)==v
for p,v in j['inputs'].items():assert sha(p)==v
for s in ['stdout','stderr']:assert sha(outer/s)==o[s+'_sha256']
assert not (outer/'stderr').read_text()
root=Path(j['output_root']);source=root/'Trace75BFSUniformDecoder.lean';object=root/'Trace75BFSUniformDecoder.olean';assert sha(source)==sha(obs/'source.txt')==sha(h/'Trace75BFSUniformDecoder.lean')=='ff8f6fb090a3140972795471be57fe5438abf6058ce49119d0d179cf95b73b06';assert sha(object)==j['object_sha256']=='f2ca7b64f92f89f3f95b8d381c4d7f509d137a490f819bb84b0f37906cd6603f' and not object.is_symlink()
assert {str(p.relative_to(root)) for p in root.rglob('*') if p.is_file() or p.is_symlink()}=={source.name,object.name}
st=j['stage'];hd=j['header'];assert st['status']=='PASS' and st['exit']==0 and st['reason'] is None and hd['status']=='PASS' and hd['exit']==0 and hd['reason'] is None
for tag,r in [('',st),('header.',hd)]:
 for s in ['stdout','stderr']:assert sha(obs/(tag+s))==r[s+'_sha256']
 assert not (obs/(tag+'stderr')).read_text()
assert (obs/'stdout').read_text()=="'Trace75BFSUniformDecoder.graph_uniform_decoder' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
lines=(obs/'header.stdout').read_text().splitlines();assert lines[0]=='BEGIN '+str(object) and lines[-1]=='END';imps=[x[7:] for x in lines[1:-1] if x.startswith('IMPORT ')];assert len(imps)==len(lines)-2 and imps==j['header_imports'] and [x for x in imps if x!='Init']==['Trace75BFSUniformReset','Trace75BFSSupport','Trace75FixedSlots','DirectBFSUniformDecoder','DiophantineConsistency.UniformPhaseSupport']
assert st['env']==j['env'] and hd['env']=={'PATH':'/usr/bin:/bin'}
p=subprocess.run([sys.executable,'-I','-S','-B','reviews/trace75-bfs-uniform-decoder-runner-independent/check.py'],capture_output=True,text=True);assert p.returncode==0,p.stderr
print(p.stdout.strip());print('PASS: actual outer and Lean/header exits 0, exact five imported modules, source/object/report hashes and current union/provider subtrees rechecked; no independent Lean replay.')
