from pathlib import Path
import ast,json,hashlib,re
R=Path('/home/codex/.codex/worktrees/ec20/Proofs');P=R/'Computability/BusyBeaver/Research/ZFC/k218-continuation-search/marker-relay/return-122';checks=[]
def ck(name,value):
 assert value,name
 checks.append(name)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for current,old in [('census.py','census.py'),('entry_routes.py','entry_routes_v2.py')]:
 a=ast.parse((P/current).read_text());b=ast.parse((P/'history'/old).read_text())
 for node in b.body:
  if isinstance(node,ast.FunctionDef):
   matches=[n for n in a.body if isinstance(n,ast.FunctionDef) and n.name==node.name]
   ck(current+':function:'+node.name,len(matches)==1 and ast.dump(matches[0])==ast.dump(node))
 if current=='entry_routes.py':
  la=[ast.dump(n)for n in a.body if isinstance(n,ast.For)]
  lb=[ast.dump(n)for n in b.body if isinstance(n,ast.For)]
  ck('all controls and family loops unchanged',la==lb)
j=json.loads((P/'evidence/entry-routes.json').read_text());c=json.loads((P/'evidence/census.json').read_text())
ck('twelve positive original controls',len(j['controls'])==12 and all(x['status']=='EXACT_JOIN'for x in j['controls']))
for name,rows in j['groups'].items():
 ck(name+':217distinct entries',rows['entry_states']==217 and len(rows['records'])==217 and len({r['entry']for r in rows['records']})==217)
 ck(name+':zero survivors',not rows['survivors'] and all(r['first_rejection']for r in rows['records']))
 ck(name+':full class source prefixes',set(rows['prefixes'])<=set(c['paths']['122']))
ck('bounded97',j['bound']==97)
ck('six exact decoder prefixes',len(c['paths']['122'])==6)
for raw in [j,c]:
 for p,h in raw['pins' if 'pins'in raw else 'inputs'].items():
  ck('actual selected input current:'+p,Path(p).is_file()and sha(Path(p))==h)
relay=P.parent/'relay217.native.tm';ck('additive relay input identity',sha(relay)=='73deb3f0e1a6159646dcb153ad5082eddb6656f3cabbbba40e86bbef971b9111')
for target in re.findall(r'\]\(([^)]+)\)',(P/'README.md').read_text()):
 ck('link:'+target,(P/target).exists())
record={'status':'OWN_SOURCE_AND_METADATA_AUDIT_PASS','role':'Diagnostic author; no independent peer or fresh machine replay.','checks':checks,'additional_relay_input':{'path':str(relay),'sha256':sha(relay),'provenance':'Previously published frozen marker-relay table; raw diagnostic hash map omitted this file, preserved unchanged.'},'checked_sources':{str(p.relative_to(P)):sha(p)for p in[P/'README.md',P/'census.py',P/'entry_routes.py',P/'evidence/census.json',P/'evidence/entry-routes.json']}}
(P/'metadata-audit.json').write_text(json.dumps(record,indent=2)+'\n')
print(len(checks),'checks pass')
