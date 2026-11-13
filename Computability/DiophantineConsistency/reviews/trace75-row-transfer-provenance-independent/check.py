from pathlib import Path
import json,hashlib,ast
D=Path(__file__).resolve().parents[2];R=D/'research';h=R/'trace75-row-transfer-provenance';o=h/'observations/attempt01'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def load(p):return json.loads(Path(p).read_text())
assert sha(h/'check.py')=='18e490eb0114a3dc76f0e61c7faf7d8cc6b126334a06df87713053628ab51dad' and sha(o/'terminal.json')=='474a0a08bb64c65e614f9a4499834208e35807d0f78a34da97fc7b9eb26b254d' and sha(o/'stdout')=='2a862662bc49fb532e0f880cc013600125f59bd7294a5d6c52650bae3cb468b5';t=load(o/'terminal.json');assert t['exit']==0 and t['checker_sha256_before']==t['checker_sha256_after']==sha(h/'check.py') and t['stdout_sha256']==sha(o/'stdout') and t['stderr_sha256']==sha(o/'stderr')
tree=ast.parse((h/'check.py').read_text());a=next(x for x in tree.body if isinstance(x,ast.Assign) and any(isinstance(y,ast.Name) and y.id=='inputs' for y in x.targets));pins=ast.literal_eval(a.value);assert len(pins)==8
for p,d in pins.items():assert sha(R/p)==d
keys=list(pins);f=load(R/keys[0]);inventory=load(R/keys[1]);r=load(R/keys[2]);obs=load(o/'stdout');n='DirectBFSRowTransfer';assert n in inventory['direct_outside_project'] and r['exit']==0 and r['pins']['source']==r['after']['source']==pins[keys[3]] and r['pins']['runner']==r['after']['runner']==pins[keys[7]] and r['stdout_sha256']==pins[keys[5]] and r['stderr_sha256']==pins[keys[6]]
src=Path(r['command'][5]);out=Path(r['command'][7]);sel=f['selected_project'][n]['.olean'];assert sha(src)==pins[keys[3]] and str(out.resolve(strict=True))==sel['resolved'] and sha(out)==r['object_sha256']==sel['sha256'];assert r['direct_imports']==r['direct_imports_after'];expected={'DirectBFSConjugacyLift','DirectBFSSymbolicKernel','DiophantineConsistency.Compact943Data'};assert {x['module'] for x in r['direct_imports']}==set(f['serialized_headers'][n]) - {'Init'}==expected
same=[];different=[]
for e in r['direct_imports']:
 p=Path(e['path']);target=f['selected_project'][e['module']]['.olean'];assert sha(p)==e['sha256']==target['sha256']==sha(target['resolved']);(same if str(p.resolve())==target['resolved'] else different).append(e['module']);x=next(z for z in obs['direct_imports'] if z['module']==e['module']);assert x['recorded_and_selected_sha256']==e['sha256'] and x['current_recorded_realpath']==str(p.resolve()) and x['selected_realpath']==target['resolved'] and x['same_realpath']==(str(p.resolve())==target['resolved'])
assert set(same)=={'DirectBFSConjugacyLift','DirectBFSSymbolicKernel','DiophantineConsistency.Compact943Data'} and not different;print('PASS source/runner/log/output records and three direct before/after comparisons; all 3 same current realpath')
