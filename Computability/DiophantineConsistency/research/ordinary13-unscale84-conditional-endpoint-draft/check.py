from pathlib import Path
from hashlib import sha256
import json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-unscale84-conditional-endpoint-draft')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
s=(D/'Unscale84Endpoint.lean.src').read_text()
for token in ['def expression84','def expression87','(h87 : PositiveModelBridge (expression87 K))','(compact_positive_zero_iff (V:=V) K).trans (h87 V)','theorem native84','theorem standard84','theorem reference84','∼mappedNativeRefutation embedding']:
 assert token in s,token
assert s.count('(h87 : PositiveModelBridge (expression87 K))')==4
print(json.dumps({'exact_87_positive_bridge_explicit':True,'compact_tuple_preserved':True,'lean_executed':False,'proof_axiom_reports':False,'physical_file_binding':False},sort_keys=True,indent=2))
