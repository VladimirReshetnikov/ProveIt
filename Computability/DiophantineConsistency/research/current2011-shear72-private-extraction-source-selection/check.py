from pathlib import Path
from hashlib import sha256
import json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/current2011-shear72-private-extraction-source-selection')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
workspace=Path('Lean/DiophantineConsistency/ArithmeticCarrier94Extraction.lean').read_text();private=Path('research/current2011-ordinary94-six-module-build/attempt05-failed/modified-source.lean').read_text()
a='simp only [hx,ht,hA,zero_add,add_zero,mul_zero,zero_mul,mul_one,one_mul,'
b='simp only [hx,ht,hA,zero_add,add_zero,mul_zero,mul_one,'
assert workspace.count(a)==1 and workspace.replace(a,b,1)==private
assert re.findall(r'^import\s+(\S+)',workspace,re.M)==re.findall(r'^import\s+(\S+)',private,re.M)
base=json.loads(Path('research/current2011-shear72-magnitude-modelarithmetic-selection/selection.json').read_text());changed=json.loads((D/'selection.json').read_text())
p=Path('research/current2011-ordinary94-six-module-build/attempt05-failed/modified-source.lean');base['frontier']['DiophantineConsistency.ArithmeticCarrier94Extraction']={'kind':'historical-private-source-frontier','path':str(p),'sha256':sha256(p.read_bytes()).hexdigest()}
assert changed==base
record=json.loads(Path('research/current2011-ordinary94-six-module-build/attempt05/result.json').read_text()); assert record['exit']==0
assert 'ArithmeticCarrier94Extraction.lean' in ' '.join(record['command'])
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),'selection_sha256':sha256((D/'selection.json').read_bytes()).hexdigest(),'workspace_sha256':sha256(workspace.encode()).hexdigest(),'private_sha256':sha256(private.encode()).hexdigest(),'single_simp_list_delta':True,'single_frontier_entry_delta':True,'recorded_producer_exit':record['exit'],'source_object_provider_authenticated':False,'lean_executed':False},sort_keys=True,indent=2))
