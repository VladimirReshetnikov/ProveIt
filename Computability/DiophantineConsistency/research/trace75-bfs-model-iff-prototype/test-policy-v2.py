#!/usr/bin/env python3
from pathlib import Path
from hashlib import sha256
import ast,json
h=Path(__file__).resolve().parent
runner=h/'run-v2.py'
pin='b2a4546f408db202e6295043fb9c67bf04493cd99768c57f85584607af81a2ef'
assert sha256(runner.read_bytes()).hexdigest()==pin
module=ast.parse(runner.read_text())
nodes=[n for n in module.body if isinstance(n,ast.FunctionDef) and n.name=='report_ok']
assert len(nodes)==1
ns={};exec(compile(ast.Module(body=nodes,type_ignores=[]),str(runner),'exec'),ns)
check=ns['report_ok']
good="'Trace75BFSModelIff.positive_model_iff' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
cases={'exact':(good,'',True),'missing':('','',False),'duplicate':(good+good,'',False),'wrong_name':(good.replace('Trace75BFSModelIff','DirectBFS80ModelIff'),'',False),'extra_axiom':(good.replace('Quot.sound]','Quot.sound, bad]'),'',False),'missing_axiom':(good.replace(', Quot.sound',''),'',False),'warning':(good+'warning(lean.foo): x\n','',False),'error':(good+'error(lean.foo): x\n','',False),'sorry':(good.replace('Quot.sound','sorryAx'),'',False),'stderr':(good,'x',False),'extra_newline':(good+'\n','',False)}
checks={name:check(out,err)==expected for name,(out,err,expected) in cases.items()}
assert all(checks.values())
obs=h/'observations'/'policy-attempt02';obs.mkdir(parents=True,exist_ok=False)
result={'runner_sha256':pin,'test_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),'checks':checks}
(obs/'result.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps(result,sort_keys=True))
