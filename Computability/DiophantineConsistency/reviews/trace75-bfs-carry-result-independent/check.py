from pathlib import Path
from hashlib import sha256
import json,subprocess,sys
h=Path('research/trace75-bfs-carry-prototype');obs=h/'observations/attempt01';outer=h/'observations/outer-attempt01'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
p=obs/'result.json';assert sha(p)=='7704d80833c17b04cf345e269213121f4bbf41537b62262921f7177f21dd4bc7';j=json.loads(p.read_text());assert j['status']=='PASS'
p=outer/'terminal.json';assert sha(p)=='c12da16e2196705490b6b5c54bf1c626eb8bda5446772018974d2e88a7c84631';o=json.loads(p.read_text());assert o['exit']==0 and o['child_result_sha256']==sha(obs/'result.json') and o['inputs_before']==o['inputs_after'];assert sha(h/'run.py')==o['inputs_before'][str((h/'run.py').resolve())]==j['runner_sha256']=='b5f0efe4dd1f853e54a5822e77b585269910b0554511ad94c4aba170f5a7fff0' and o['wrapper_sha256_before']==o['wrapper_sha256_after']==sha(h/'run-outer.py')=='a4368d56f8ede996441664f04d925dbb3d2d19c55c4b9435bc3d5b9052f741f4'
for p,v in o['inputs_before'].items():assert sha(p)==v
for p,v in j['inputs'].items():assert sha(p)==v
for s in ['stdout','stderr']:assert sha(outer/s)==o[s+'_sha256']
assert not (outer/'stderr').read_text()
root=Path(j['output_root']);source=root/'Trace75BFSCarry.lean';object=root/'Trace75BFSCarry.olean';assert sha(source)==sha(obs/'source.txt')==sha(h/'Trace75BFSCarry.lean')=='84b55b0b1e206c5a9e7d16292581651bbe69cbed51b4f50f8a2faf6563bf1499';assert sha(object)==j['object_sha256']=='d4dc1034131198fd5965e9a23585f81c1182c39ba8b217fb550036acb7b9545e' and not object.is_symlink()
assert {str(p.relative_to(root)) for p in root.rglob('*') if p.is_file() or p.is_symlink()}=={source.name,object.name}
st=j['stage'];hd=j['header'];assert st['status']=='PASS' and st['exit']==0 and st['reason'] is None and hd['status']=='PASS' and hd['exit']==0 and hd['reason'] is None
for tag,r in [('',st),('header.',hd)]:
 for s in ['stdout','stderr']:assert sha(obs/(tag+s))==r[s+'_sha256']
 assert not (obs/(tag+'stderr')).read_text()
assert (obs/'stdout').read_text()=="'Trace75BFSCarry.graph_indexed_carry' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
lines=(obs/'header.stdout').read_text().splitlines();assert lines[0]=='BEGIN '+str(object) and lines[-1]=='END';imps=[x[7:] for x in lines[1:-1] if x.startswith('IMPORT ')];assert len(imps)==len(lines)-2 and imps==j['header_imports'] and [x for x in imps if x!='Init']==['Trace75FixedCongruence','DirectBFSBandCarry','DiophantineConsistency.ActualTemporalBand']
assert st['env']==j['env'] and hd['env']=={'PATH':'/usr/bin:/bin'}
p=subprocess.run([sys.executable,'-I','-S','-B','reviews/trace75-bfs-carry-runner-independent/check.py'],capture_output=True,text=True);assert p.returncode==0,p.stderr
print(p.stdout.strip());print('PASS: actual outer and Lean/header exits 0, exact three imported modules, source/object/report hashes and current union/provider subtrees rechecked; no independent Lean replay.')
