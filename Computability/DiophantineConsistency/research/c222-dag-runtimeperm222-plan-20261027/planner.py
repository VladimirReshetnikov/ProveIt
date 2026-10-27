from pathlib import Path
import hashlib,json,re,copy,subprocess
R=Path('/home/codex/.codex/worktrees/46be/Proofs');D=R/'Computability/DiophantineConsistency';RES=D/'research';REV=D/'reviews';BB=R/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC'
pins={};checks=0
def rec(p):
 p=Path(p);p=p if p.is_absolute() else R/p
 return {'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size}
def check(r):
 global checks
 a=rec(r['path']);assert a['sha256']==r['sha256'],(r,a);pins[a['path']]=a;checks+=1;return a
def read(p,sha):
 a=check({'path':str(p),'sha256':sha});return json.loads(Path(a['path']).read_text())
def imports(p):
 s=Path(p).read_text();out=[];i=depth=0
 while i<len(s):
  pair=s[i:i+2]
  if depth:
   if pair=='/-':depth+=1;i+=2
   elif pair=='-/':depth-=1;i+=2
   else:out.append('\n'if s[i]=='\n'else' ');i+=1
  elif pair=='/-':depth=1;i+=2
  elif pair=='--':
   while i<len(s)and s[i]!='\n':i+=1
  else:out.append(s[i]);i+=1
 assert depth==0
 return list(dict.fromkeys(['Init']+[n for line in re.findall(r'^\s*(?:(?:public|private|meta)\s+)*import\s+([^\n]+)',''.join(out),re.M)for n in line.split()]))
def nested(x):
 if isinstance(x,dict):
  if 'path'in x and 'sha256'in x:yield x
  for v in x.values():yield from nested(v)
 elif isinstance(x,list):
  for v in x:yield from nested(v)
b=read(RES/'c222-dag-rootperm222-cache-plan-20261027.json','99ab05b4c499f031c65a58fc426777fac55ecc5584cfbd5a790eb2698cbcfa58')
for r in b['selected_authentication']:check(r)
old=read(RES/'c222-dagperm-runtime-cache-plan-20261027.json','9fc88539652bb8e9a6fc9ed528e00557c3f9f48227eb475e43f56e7f427c93f9')
root=read(REV/'arithmetic-dag-rootperm222-replay.json','47136eefb13b4fedd512e160a3538ba7fb96b5d456ebbe47d37805f41680e65a')
assert root['status']=='PASS'
check(root['evidence_manifest']);mf=json.loads(Path(root['evidence_manifest']['path']).read_text());assert len(mf)==17
for r in mf:check(r)
row=root['final']['records'][0]
for k in ['source','snapshot','object','log','timing']:check(row[k])
mods=copy.deepcopy({m['module']:m for m in b['modules']})
n=row['module'];mods[n]={'module':n,'source':row['source'],'actual_imports':imports(row['source']['path']),'objects':[row['object']],'inventory_parent':rec(REV/'arithmetic-dag-rootperm222-replay.json'),'provenance':'Author-frozen PASS; ROOT independent acceptance pending at planning time. Must select accepted root supplement before execution if available.'}
run=next(m for m in old['profiles']['all_internal_runtime_bridge']['modules']if m['module']=='DiophantineConsistency.ArithmeticEnumRunPerm222');mods[run['module']]=copy.deepcopy(run)
refresh='BusyBeaver.ZFC.ArithmeticPositiveSimulation254';ps=rec(BB/'ArithmeticPositiveSimulation254.lean');check(ps)
history=read('/tmp/zfc-positive-simulation/run4/verification.json',rec('/tmp/zfc-positive-simulation/run4/verification.json')['sha256'])
check({'path':history['source']['snapshot'],'sha256':history['source']['sha256']});assert ps['sha256']==history['source']['sha256']
comparisons=[]
for h in history['reused_modules']:
 m=mods[h['module']]
 comparisons.append({'module':h['module'],'historical_source_sha256':h['source_sha256'],'current_source':m['source'],'same_source':h['source_sha256']==m['source']['sha256'],'historical_object':{'path':h['object'],'sha256':h['object_sha256']},'selected_current_objects':m['objects']})
modfresh={'module':refresh,'source':ps,'actual_imports':imports(ps['path']),'objects':[],'action':'PROPOSED_EXPLICIT_FRESH_UNCHANGED_SOURCE_NOT_YET_AUTHORIZED','provenance':'Source matches historical successful build, but9/11 explicitly listed custom dependency source hashes differ. Old object excluded; request one reviewed unchanged-source refresh over current accepted closure.'}
mods[refresh]=modfresh
bound={x['module']:x for x in b['external']};seen=set();active=set();used=set();order=[]
def visit(n):
 if n not in mods:assert n in bound,('unknown',n);used.add(n);return
 if n in seen:return
 assert n not in active,('cycle',n);active.add(n);m=mods[n]
 check(m['source']);assert imports(m['source']['path'])==m['actual_imports'],('header',n)
 for x in m['actual_imports']:visit(x)
 for x in m['objects']:check(x)
 active.remove(n);seen.add(n);order.append(n)
direct=['BusyBeaver.ZFC.ArithmeticDagRootPerm222','DiophantineConsistency.ArithmeticEnumRunPerm222',refresh]
for n in direct:visit(n)
external=[bound[n]for n in sorted(used)]
for x in external:
 for r in nested(x):check(r)
 primary=x if 'path'in x else x['object'];rel=Path(*x['module'].split('.')).with_suffix('.olean')
 first=next((Path(q)/rel for q in b['package_paths']if(Path(q)/rel).exists()),None);assert first and rec(first)['sha256']==primary['sha256']
selected=[mods[n]for n in order]
counts={'closure_custom':len(selected),'cached_custom':len(selected)-1,'Foundation':sum(n.startswith('Foundation.')for n in seen),'cached_artifacts':sum(len(m['objects'])for m in selected),'external':len(used),'boundary_companion_observations':sum(len(x['companion_observations'])for x in external),'proposed_refresh':1,'new_leaves':2}
assert counts=={'closure_custom':152,'cached_custom':151,'Foundation':95,'cached_artifacts':436,'external':39,'boundary_companion_observations':117,'proposed_refresh':1,'new_leaves':2},counts
check(b['compiler']);check(rec(__file__))
guides=[rec(BB/(n+'.lean'))for n in ['ArithmeticPositiveSimulation254','ArithmeticL2Endpoint254','ArithmeticDagControlPerm222','ArithmeticDagRootPerm222','ArithmeticControlFile','ArithmeticControlTable']]
for r in guides:check(r)
for r in list(pins.values()):check(r)
x={'status':'READ_ONLY_PROPOSAL_REFRESH_REQUIRES_AUTHORIZATION','snapshot':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),'direct_imports':direct,'modules':selected,'external':external,'topological_order':order,'counts':counts,'compiler':b['compiler'],'package_paths':b['package_paths'],'parents':[rec(RES/'c222-dag-rootperm222-cache-plan-20261027.json'),rec(RES/'c222-dagperm-runtime-cache-plan-20261027.json'),rec(REV/'arithmetic-dag-rootperm222-replay.json')],'provisional_root_provider':row['object'],'generic_refresh_audit':{'historical_record':rec('/tmp/zfc-positive-simulation/run4/verification.json'),'source':ps,'historical_snapshot':rec(history['source']['snapshot']),'custom_dependency_comparisons':comparisons,'unchanged_source_count':sum(x['same_source']for x in comparisons),'changed_source_count':sum(not x['same_source']for x in comparisons),'old_object_excluded':True},'guide_pins':guides,'planner':rec(__file__),'observations':checks,'authenticated_paths':list(pins.values()),'scope':'No overlay, compiler or Lean-source writes. Proposes one unchanged generic transport refresh plus concrete actual runtime bridge pair. No p215 tape/boot, source-ZFC or final HA claim.'}
p=RES/'c222-dag-runtimeperm222-cache-plan-20261027.json';p.write_text(json.dumps(x,indent=2)+'\n')
print(json.dumps({'plan':rec(p),'counts':counts,'observations':checks,'paths':len(pins)},indent=2))
