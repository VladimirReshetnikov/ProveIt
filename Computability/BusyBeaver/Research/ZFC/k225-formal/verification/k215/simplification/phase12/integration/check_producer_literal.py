"""Own literal-data reconstruction; never import or execute a delivered producer."""
from pathlib import Path
import ast,hashlib,json
R=Path.cwd();P=Path('/tmp/k215-phase12-import-proposal');D=R/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC';producer=R/'Computability/BusyBeaver/Research/ZFC/k225-formal/generate_l2k222.py'
assert hashlib.sha256(producer.read_bytes()).hexdigest()=='c720d5bf58d4c9119bfb6a6d206451e18c7287caf0518c8a666b38cc0b2e74f6'
tree=ast.parse(producer.read_text());tables={}
for n in tree.body:
 if isinstance(n,ast.Assign):
  for target in n.targets:
   if isinstance(target,ast.Name) and target.id in {'SUBS','LOOP136','OLD_136','NEW_136'}:tables[target.id]=ast.literal_eval(n.value)
rows=[]
for src,dst in [('L2Lib254','L2Lib222'),('L2Macros254','L2Macros222'),('L2Control254','L2Control222')]:
 t=(D/(src+'.lean')).read_text()
 for old,new in tables['SUBS']:t=t.replace(old,new)
 if src=='L2Control254':
  assert t.count(tables['OLD_136'])==1;t=t.replace(tables['OLD_136'],tables['NEW_136']);anchor='/-! ## Fetch, MP and NIP -/';assert t.count(anchor)==1;t=t.replace(anchor,tables['LOOP136']+anchor)
 head=f"/- Forked by Research/ZFC/k225-formal/generate_l2k222.py from {src}.lean for dag222 (Elliot Glazer's Dag230 with the 222's AX node). -/\n"
 actual=(head+t).encode();target=D/(dst+'.lean');assert actual==target.read_bytes(),dst
 rows.append({'module':dst,'bytes':len(actual),'sha256':hashlib.sha256(actual).hexdigest()})
record={'status':'PASS_EXACT_THREE_MODULE_LITERAL_REPRODUCTION','producer_sha256':hashlib.sha256(producer.read_bytes()).hexdigest(),'modules':rows,'producer_executed':False,'supplied_execution':False,'scope':'AST literal tables read as data; own finite string transformations independently compare all three maintained outputs.'};(P/'producer-literal-check.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record,indent=2))
