from pathlib import Path
from hashlib import sha256
import json,subprocess,sys
h=Path('research/trace75-bfs-support-prototype');obs=h/'observations/attempt01';outer=h/'observations/outer-attempt01'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
p=obs/'result.json';assert sha(p)=='656ef70f8acfe147effa3b3339b5f6a210c924ab5defe5caa10097faf3fcfeaa';j=json.loads(p.read_text());assert j['status']=='PASS'
p=outer/'terminal.json';assert sha(p)=='db3489eec9ed11e229931ed331b970fdcecb9d2b83e9259f9928e71c5ab45b51';o=json.loads(p.read_text());assert o['exit']==0 and o['child_result_sha256']==sha(obs/'result.json') and o['inputs_before']==o['inputs_after'];assert sha(h/'run-v2.py')==o['inputs_before'][str((h/'run-v2.py').resolve())]==j['runner_sha256']=='d4cd167d6acbe89a57edbef3a3cd605f076d569eda83ec39c334fd8d95eef060' and o['wrapper_sha256_before']==o['wrapper_sha256_after']==sha(h/'run-outer-v2.py')=='ab098a8a9930728d294a3c0158362360e7112a4e2ab18db59488538816f499f5'
for p,v in o['inputs_before'].items():assert sha(p)==v
for p,v in j['inputs'].items():assert sha(p)==v
for s in ['stdout','stderr']:assert sha(outer/s)==o[s+'_sha256']
assert not (outer/'stderr').read_text()
root=Path(j['output_root']);source=root/'Trace75BFSSupport.lean';object=root/'Trace75BFSSupport.olean';assert sha(source)==sha(obs/'source.txt')==sha(h/'Trace75BFSSupport.lean')=='06187545b591ad3f6e19bd8f5f9101c6c291bed639e1e10b629584960604ee6b';assert sha(object)==j['object_sha256']=='0795d51ca82af5844510d53a0690ef3940d023f0c78450c38026a8386a255121' and not object.is_symlink()
assert {str(p.relative_to(root)) for p in root.rglob('*') if p.is_file() or p.is_symlink()}=={source.name,object.name}
st=j['stage'];hd=j['header'];assert st['status']=='PASS' and st['exit']==0 and st['reason'] is None and hd['status']=='PASS' and hd['exit']==0 and hd['reason'] is None
for tag,r in [('',st),('header.',hd)]:
 for s in ['stdout','stderr']:assert sha(obs/(tag+s))==r[s+'_sha256']
 assert not (obs/(tag+'stderr')).read_text()
assert (obs/'stdout').read_text()=="'Trace75BFSSupport.graph_support_carry' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
lines=(obs/'header.stdout').read_text().splitlines();assert lines[0]=='BEGIN '+str(object) and lines[-1]=='END';imps=[x[7:] for x in lines[1:-1] if x.startswith('IMPORT ')];assert len(imps)==len(lines)-2 and imps==j['header_imports'] and [x for x in imps if x!='Init']==['Trace75BFSCarry','Trace75FixedSlots','DiophantineConsistency.CleanModelSupport']
assert st['env']==j['env'] and hd['env']=={'PATH':'/usr/bin:/bin'}
p=subprocess.run([sys.executable,'-I','-S','-B','reviews/trace75-bfs-support-runner-v2-independent/check.py'],capture_output=True,text=True);assert p.returncode==0,p.stderr
print(p.stdout.strip());print('PASS: actual outer and Lean/header exits 0, exact three imported modules, source/object/report hashes and current union/provider subtrees rechecked; no independent Lean replay.')
