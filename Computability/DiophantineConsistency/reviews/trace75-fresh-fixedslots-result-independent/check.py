from pathlib import Path
from hashlib import sha256
import json,subprocess,sys
h=Path('research/trace75-fresh-fixedslots-prototype');obs=h/'observations/attempt01';outer=h/'observations/outer-attempt01'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
p=obs/'result.json';assert sha(p)=='7f1df5657b7a5a82e1136b9d2e19e067c57312c1bbc6ae23dc21e6946ce06873';j=json.loads(p.read_text());assert j['status']=='PASS'
p=outer/'terminal.json';assert sha(p)=='4c78ac9fab5a3c8d5da0bbb191932180e0426deef1b9c818c66302990412b2d1';o=json.loads(p.read_text());assert o['exit']==0 and o['child_result_sha256']==sha(obs/'result.json') and o['inputs_before']==o['inputs_after'];assert sha(h/'run.py')==o['inputs_before'][str((h/'run.py').resolve())]==j['runner_sha256']=='4cbaec5b82fa6c36ed281abcf19c11234c60c3ba7187ac49f21df3997ad4ee63' and o['wrapper_sha256_before']==o['wrapper_sha256_after']==sha(h/'run-outer.py')=='cee3a171ae74820716225751cd3d116c8c50727116371698e4321f6ddbf4c504'
for p,v in o['inputs_before'].items():assert sha(p)==v
for p,v in j['inputs'].items():assert sha(p)==v
for s in ['stdout','stderr']:assert sha(outer/s)==o[s+'_sha256']
assert not (outer/'stderr').read_text()
root=Path(j['output_root']);source=root/'Trace75FixedSlots.lean';object=root/'Trace75FixedSlots.olean';assert sha(source)==sha(obs/'source.txt')==sha(h/'Trace75FixedSlots.lean')=='e33b9f4ef0132bc2fc0f1adabad939d892b22a446ec1679934f3c34d0902b7d6';assert sha(object)==j['object_sha256']=='63c29a06e1efa989917b77548c8362622a038fe0531373a7f86993343f80cda1' and not object.is_symlink()
assert {str(p.relative_to(root)) for p in root.rglob('*') if p.is_file() or p.is_symlink()}=={source.name,object.name}
st=j['stage'];hd=j['header'];assert st['status']=='PASS' and st['exit']==0 and st['reason'] is None and hd['status']=='PASS' and hd['exit']==0 and hd['reason'] is None
for tag,r in [('',st),('header.',hd)]:
 for s in ['stdout','stderr']:assert sha(obs/(tag+s))==r[s+'_sha256']
 assert not (obs/(tag+'stderr')).read_text()
assert (obs/'stdout').read_text()=="'Trace75FixedSlots.increment_digits' depends on axioms: [propext, Classical.choice, Quot.sound]\n'Trace75FixedSlots.graph_fixed_slots' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
lines=(obs/'header.stdout').read_text().splitlines();assert lines[0]=='BEGIN '+str(object) and lines[-1]=='END';imps=[x[7:] for x in lines[1:-1] if x.startswith('IMPORT ')];assert len(imps)==len(lines)-2 and imps==j['header_imports'] and [x for x in imps if x!='Init']==['Trace75FixedDigits','DiophantineConsistency.CompactMixedIncrement']
assert st['env']==j['env'] and hd['env']=={'PATH':'/usr/bin:/bin'}
p=subprocess.run([sys.executable,'-I','-S','-B','reviews/trace75-fresh-fixedslots-runner-independent/check.py'],capture_output=True,text=True);assert p.returncode==0,p.stderr
print(p.stdout.strip());print('PASS: actual outer and Lean/header exits 0, exact two imported modules, source/object/report hashes and current union/provider subtrees rechecked; no independent Lean replay.')
prior=Path('/tmp/trace75-fixedslots-o2wc0z82/Trace75FixedSlots.olean');assert sha(prior)==sha(object);print('PASS: fresh output byte-identical to earlier checked object; provenance remains distinct.')
