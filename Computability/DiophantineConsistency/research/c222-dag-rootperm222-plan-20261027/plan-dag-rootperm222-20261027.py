from pathlib import Path
import json,hashlib,re,copy,subprocess
R=Path('/home/codex/.codex/worktrees/46be/Proofs');D=R/'Computability/DiophantineConsistency';RES=D/'research';REV=D/'reviews'
observed={};comparisons=0
def rec(p):
 p=Path(p);p=p if p.is_absolute() else R/p
 return {'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size}
def verify(x):
 global comparisons
 a=rec(x['path']);assert a['sha256']==x['sha256'],(x,a);observed[a['path']]=a;comparisons+=1;return a
def nested(x):
 if isinstance(x,dict):
  if 'path'in x and 'sha256'in x:yield x
  for v in x.values():yield from nested(v)
 elif isinstance(x,list):
  for v in x:yield from nested(v)
def read(p,sha):
 a=verify({'path':str(p),'sha256':sha});return json.loads(Path(a['path']).read_text())
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
oldpath=RES/'c222-dagperm-runtime-cache-plan-20261027.json'
old=read(oldpath,'9fc88539652bb8e9a6fc9ed528e00557c3f9f48227eb475e43f56e7f427c93f9')
profile=copy.deepcopy(old['profiles']['actual_macros_and_dispatch'])
for x in old['selected_authentication']:verify(x)
for x in old['source_guide_pins']:verify(x)
rootpath=REV/'arithmetic-dag-macros-perm222-root-replay.json'
root=read(rootpath,'f8c804dd50fa15f1d19657f3dfc968c906ca8a434b75103670b629ca0b77ec65')
for x in nested(root):verify(x)
manifest=read(root['manifest']['path'],root['manifest']['sha256'])
assert len(manifest)==18
for x in manifest:verify(x)
state=read(root['state']['path'],root['state']['sha256']);assert root['status']==state['status']=='PASS'
row=root['records'][0];name='BusyBeaver.ZFC.ArithmeticDagMacrosPerm222';assert row['module']==name
mods={m['module']:m for m in profile['modules']}
assert name not in mods
mods[name]={'module':name,'source':row['source'],'objects':[row['object']],'actual_imports':imports(row['source']['path']),'inventory_parent':rec(rootpath),'provenance':'Accepted ROOT independent fresh primary, byte-identical author; accepted commit d504e3006d. Historical runtime profile preserved unchanged.'}
assert mods[name]['actual_imports']==['Init','BusyBeaver.ZFC.ArithmeticDagControlPerm222']
ext={x['module']:x for x in profile['external']};order=[];seen=set();active=set();used=set()
def visit(n):
 if n not in mods:
  assert n in ext,('missing',n);used.add(n);return
 if n in seen:return
 assert n not in active,('cycle',n);active.add(n);m=mods[n]
 verify(m['source']);actual=imports(m['source']['path']);assert actual==m['actual_imports'],('header',n,actual,m['actual_imports'])
 for k in actual:visit(k)
 for o in m['objects']:verify(o)
 active.remove(n);seen.add(n);order.append(n)
direct=[name,'DiophantineConsistency.ArithmeticEnumStepPerm222']
for n in direct:visit(n)
for n in used:
 x=ext[n]
 for p in nested(x):verify(p)
 rel=Path(*n.split('.')).with_suffix('.olean')
 first=next((Path(q)/rel for q in old['package_paths'] if(Path(q)/rel).exists()),None)
 primary=x if 'path' in x else x['object']
 assert first and rec(first)['sha256']==primary['sha256'],('boundary-first',n)
selected=[mods[n]for n in order];external=[ext[n]for n in sorted(used)]
counts={'custom':len(selected),'Foundation':sum(n.startswith('Foundation.')for n in seen),'artifacts':sum(len(m['objects'])for m in selected),'external':len(used),'boundary_companion_observations':sum(len(x['companion_observations'])for x in external),'refresh':0}
assert counts=={'custom':149,'Foundation':95,'artifacts':434,'external':39,'boundary_companion_observations':117,'refresh':0},counts
verify(old['compiler'])
for p in list(observed.values()):verify(p)
out={'status':'READ_ONLY_AUTHENTICATED_PLAN','snapshot':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),'historical_plan':rec(oldpath),'historical_profile':'actual_macros_and_dispatch','accepted_macro_supplement':{'packet':rec(rootpath),'state':root['state'],'manifest':root['manifest'],'commit':'d504e3006d','source':row['source'],'selected':row['object'],'provider':root['private_provider'],'historical_author_packet':rec(REV/'arithmetic-dag-macros-perm222-replay.json')},'direct_imports':direct,'modules':selected,'external':external,'topological_order':order,'counts':counts,'compiler':old['compiler'],'package_paths':old['package_paths'],'planner':rec(__file__),'comparisons':comparisons,'selected_authentication':list(observed.values()),'scope':'RootPerm exact equality123/461-466, complete literal AX sequence and fold, actual selector dispatch/root_step/progress. No overlay/compiler executed. No control time/run halting equivalence or215 tape claims. No refresh, old254 semantic theorem or caller root IRun premise.'}
p=RES/'c222-dag-rootperm222-cache-plan-20261027.json';p.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'plan':rec(p),'counts':counts,'comparisons':comparisons,'unique_paths':len(observed)},indent=2))
