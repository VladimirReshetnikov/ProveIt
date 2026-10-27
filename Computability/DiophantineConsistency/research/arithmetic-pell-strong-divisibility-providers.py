from pathlib import Path
import hashlib,json
D=Path('/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency')
P=D/'research/arithmetic-pell-strong-divisibility-cache-plan.json'
O=D/'research/arithmetic-pell-strong-divisibility-providers.json'
def record(path):
 p=Path(path);d=p.read_bytes();return dict(path=str(p),sha256=hashlib.sha256(d).hexdigest(),bytes=len(d))
def require(ok,msg):
 if not ok:raise RuntimeError(msg)
def relative(module,obj):return str(Path(*module.split('.')[:-1])/Path(obj['path']).name)
require(not O.exists(),'new mapping')
pp=record(P);require(pp['sha256']=='6540842617bdadcad5f9d28b42447ff6b3ed9b3ad28d225b323a808997bd4015','plan')
p=json.loads(P.read_text());virtual={};records=[]
for module in p['modules']:
 for obj in module['objects']:
  key=relative(module['module'],obj);require(key not in virtual,'overlay collision');virtual[key]=obj
for module in p['modules']+p['external']:
 for expected in module.get('objects',module.get('artifacts')):
  rel=relative(module['module'],expected)
  if rel in virtual:actual=record(virtual[rel]['path']);kind='prospective private link; no overlay created'
  else:
   first=next((Path(root)/rel for root in p['boundary_search'] if (Path(root)/rel).is_file()),None)
   require(first is not None,'boundary missing');actual=record(first);kind='actual explicit boundary first provider'
  require(actual['sha256']==expected['sha256'] and actual['bytes']==expected['bytes'],'provider '+rel)
  records.append(dict(module=module['module'],relative=rel,kind=kind,expected=expected,actual=actual))
require(len(records)==496 and len(virtual)==382,'complete providers')
O.write_text(json.dumps(dict(status='READ_ONLY_PROVIDER_MAPPING_NO_OVERLAY_OR_COMPILER',plan=pp,
 audit=record(__file__),custom_planned_links=382,actual_boundary_first_artifacts=114,
 total=496,records=records),indent=2)+'\n')
print(json.dumps(record(O),indent=2))
