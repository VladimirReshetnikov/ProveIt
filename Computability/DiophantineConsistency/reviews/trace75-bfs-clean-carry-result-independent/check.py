from pathlib import Path
from hashlib import sha256
import json,subprocess,sys
h=Path('research/trace75-bfs-clean-carry-prototype');obs=h/'observations/attempt01';outer=h/'observations/outer-attempt01'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
p=obs/'result.json';assert sha(p)=='c370158e10e44877025fdc28c0abf5040143a300cf7db8a8bbcc7c366e16b92a';j=json.loads(p.read_text());assert j['status']=='PASS'
p=outer/'terminal.json';assert sha(p)=='ca17662a11a3aa67b5815590157fe88cf03072c0abd974f4aa274523e83420ea';o=json.loads(p.read_text());assert o['exit']==0 and o['child_result_sha256']==sha(obs/'result.json') and o['inputs_before']==o['inputs_after'];assert sha(h/'run.py')==o['inputs_before'][str((h/'run.py').resolve())]==j['runner_sha256']=='7d59697b02829a87488a8b25f5a08a30d658ae3d8a16ed183c63ea11e588481f' and o['wrapper_sha256_before']==o['wrapper_sha256_after']==sha(h/'run-outer.py')=='3cf6609f5e2278d2686d24cb393e828a6be3d97ca366ddfdc55b368ef1b07f57'
for p,v in o['inputs_before'].items():assert sha(p)==v
for p,v in j['inputs'].items():assert sha(p)==v
for s in ['stdout','stderr']:assert sha(outer/s)==o[s+'_sha256']
assert not (outer/'stderr').read_text()
root=Path(j['output_root']);source=root/'Trace75BFSCleanCarry.lean';object=root/'Trace75BFSCleanCarry.olean';assert sha(source)==sha(obs/'source.txt')==sha(h/'Trace75BFSCleanCarry.lean')=='83673606ed323d304cb97b95f4ad25f120dec09a286f020242d3ce226c6156e8';assert sha(object)==j['object_sha256']=='95408ca90bbf60fd8162eb69dc98f651aae45ca9450492b534aa978c0b0d0c2d' and not object.is_symlink()
assert {str(p.relative_to(root)) for p in root.rglob('*') if p.is_file() or p.is_symlink()}=={source.name,object.name}
st=j['stage'];hd=j['header'];assert st['status']=='PASS' and st['exit']==0 and st['reason'] is None and hd['status']=='PASS' and hd['exit']==0 and hd['reason'] is None
for tag,r in [('',st),('header.',hd)]:
 for s in ['stdout','stderr']:assert sha(obs/(tag+s))==r[s+'_sha256']
 assert not (obs/(tag+'stderr')).read_text()
assert (obs/'stdout').read_text()=="'Trace75BFSCleanCarry.graph_clean_carry' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
lines=(obs/'header.stdout').read_text().splitlines();assert lines[0]=='BEGIN '+str(object) and lines[-1]=='END';imps=[x[7:] for x in lines[1:-1] if x.startswith('IMPORT ')];assert len(imps)==len(lines)-2 and imps==j['header_imports'] and [x for x in imps if x!='Init']==['Trace75BFSSupport','DiophantineConsistency.CleanSafeSource','DiophantineConsistency.CyclicAnyPhase','DiophantineConsistency.TemporalSafeCyclic','DiophantineConsistency.TemporalCarryExact']
assert st['env']==j['env'] and hd['env']=={'PATH':'/usr/bin:/bin'}
p=subprocess.run([sys.executable,'-I','-S','-B','reviews/trace75-bfs-clean-carry-runner-independent/check.py'],capture_output=True,text=True);assert p.returncode==0,p.stderr
print(p.stdout.strip());print('PASS: actual outer and Lean/header exits 0, exact five imported modules, source/object/report hashes and current union/provider subtrees rechecked; no independent Lean replay.')
