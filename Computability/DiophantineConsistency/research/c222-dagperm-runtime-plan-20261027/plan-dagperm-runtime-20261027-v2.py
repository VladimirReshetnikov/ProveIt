from pathlib import Path
import json,hashlib,re,copy,subprocess
R=Path('/home/codex/.codex/worktrees/46be/Proofs');D=R/'Computability/DiophantineConsistency';REV=D/'reviews';RES=D/'research'
def rec(p):
 p=Path(p);return {'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size}
def verify(r):
 a=rec(r['path']);assert a['sha256']==r['sha256'],str(r);observed[a['path']]=a;return a
def nested(x):
 if isinstance(x,dict):
  if 'path'in x and 'sha256'in x:yield x
  for v in x.values():yield from nested(v)
 elif isinstance(x,list):
  for v in x:yield from nested(v)
def primary(x):return x if 'path'in x else x['object']
def read(p,sha=None):
 a=rec(p)
 if sha:assert a['sha256']==sha,(p,a)
 observed[a['path']]=a;return json.loads(Path(p).read_text())
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
def normalized(m):
 m=copy.deepcopy(m)
 if isinstance(m['source'],str):m['source']={'path':m['source'],'sha256':m['source_sha256']}
 old=m.get('actual_imports',m.get('imports'))
 m['actual_imports']=imports(m['source']['path'])
 if old:assert m['actual_imports']==old,(m['module'],'header',old,m['actual_imports'])
 return m
observed={}
bi=read(REV/'arithmetic-control-bisim-perm215-replay.json','5771db7650be9a5b85a8e093b05f11b65d17b7d5abae9640ad8a2f314bc5d862')
verify(bi['final_inputs']);B=read(bi['final_inputs']['path'])
en=read(REV/'arithmetic-enum-soundnessperm222-replay.json');verify(en['inputs']);E=read(en['inputs']['path']);verify(E['plan']);EP=read(E['plan']['path'])
mods={};alternates=[]
for parent,rows in [(bi['final_inputs'],B['modules']),(en['inputs'],E['modules'])]:
 for x in rows:
  x=normalized(x);x['inventory_parent']=parent;n=x['module']
  if n in mods:
   assert mods[n]['source']['sha256']==x['source']['sha256'],('source conflict',n)
   if mods[n]['objects']!=x['objects']:alternates.append({'module':n,'selected':mods[n]['objects'],'alternate':x['objects'],'reason':'source-identical accepted parents; first Bisim inventory selected'})
  else:mods[n]=x
root_packet=read(REV/'arithmetic-control-bisim-perm215-root-replay.json','4dac153721bc15d83f4436031a6fa32ed9a8bdfacc384692ce29af969f8eea29')
for pin in nested(root_packet):verify(pin)
supplements=[]
for stem,expected in [('arithmetic-dag-controlperm222','f3228324a345d488692b682ed23b44cff2ef6e017dddb52101db535dc84092eb'),('arithmetic-control-bisim-perm215',None)]:
 path=REV/(stem+'-root-replay')/('state.json'if'bisim'in stem else'ROOT.json');root=read(path,expected);assert root['status']=='PASS'
 for row in root['records']:
  n=row['module']
  if n.endswith('Checks'):continue
  for k in ['source','snapshot','object','log','timing']:verify(row[k])
  old=mods.get(n)
  if old:
   assert old['source']['sha256']==row['source']['sha256']
   assert old['objects'][0]['sha256']==row['object']['sha256']
  supplements.append({'module':n,'root_state':rec(path),'historical_objects':old['objects']if old else None,'selected':row['object']})
  mods[n]={'module':n,'source':row['source'],'objects':[row['object']],'actual_imports':imports(row['source']['path']),'inventory_parent':rec(path),'provenance':'accepted root fresh replay, byte-identical with preserved author provider'}
external={x['module']:x for x in B['external']}
for x in EP['external']:
 if x['module']in external:assert primary(external[x['module']])['sha256']==primary(x)['sha256']
 else:external[x['module']]=x
profiles={}
for name,direct in [
 ('actual_macros_and_dispatch',['BusyBeaver.ZFC.ArithmeticDagControlPerm222','DiophantineConsistency.ArithmeticEnumStepPerm222']),
 ('all_internal_runtime_bridge',['BusyBeaver.ZFC.ArithmeticControlBisimPerm215','DiophantineConsistency.ArithmeticEnumRunPerm222'])]:
 seen=set();visiting=set();order=[];used=set()
 def visit(n):
  if n not in mods:
   assert n in external,('unknown',n);used.add(n);return
  if n in seen:return
  assert n not in visiting,('cycle',n);visiting.add(n)
  for k in mods[n]['actual_imports']:visit(k)
  visiting.remove(n);seen.add(n);order.append(n)
 for n in direct:visit(n)
 selected=[mods[n]for n in order]
 for m in selected:
  verify(m['source'])
  for o in m['objects']:verify(o)
 for n in used:
  for x in nested(external[n]):verify(x)
 boundary=[]
 for n in sorted(used):
  x=copy.deepcopy(external[n]);p=Path(primary(x)['path']);x['companion_observations']=[]
  for suf in ['.server','.private','.ir']:
   q=p.with_suffix('.ir')if suf=='.ir'else Path(str(p)+suf)
   if q.exists():x['companion_observations'].append(rec(q))
  boundary.append(x)
 profiles[name]={'direct_imports':direct,'modules':selected,'external':boundary,'topological_order':order,'counts':{'custom':len(selected),'Foundation':sum(n.startswith('Foundation.')for n in seen),'artifacts':sum(len(x['objects'])for x in selected),'external':len(used),'boundary_companion_observations':sum(len(x['companion_observations'])for x in boundary),'refresh':0},'selected_provider_scope':'No overlay created; all selected primary/recorded companions rehashed at preserved paths. Package companions are current observations, not newly asserted historical captures.'}
for r in B['compiler'],rec(__file__):verify(r)
guides=['ArithmeticDagRun','ArithmeticDagLoops','ArithmeticL2Lib254','ArithmeticL2Macros254','ArithmeticL2Control254','ArithmeticL2Endpoint254','ArithmeticPositiveSimulation254','Dag219','Dag219Bisim','DagDom','DagPerm','L2Perm','L2AxiomsPerm','L2RootPerm','ArithmeticControlSimulation254','ArithmeticControlFrame254','ArithmeticSymbolicTapePerm252','KEndpoint215','KBoot215','KSites215','KSim','KDense215','KSource215Program']
guide_pins=[rec(R/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC'/(n+'.lean'))for n in guides]
for n in ['ArithmeticCommandWordPerm222','ArithmeticCommandStepPerm222','ArithmeticCommandFetchPerm222','ArithmeticEnumStepPerm222','ArithmeticEnumRunPerm222','ArithmeticEnumSoundnessPerm222','DecimalMachine215']:
 guide_pins.append(rec(D/'Lean/DiophantineConsistency'/(n+'.lean')))
out={'status':'READ_ONLY_AUTHENTICATED_PLAN','snapshot':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),'profiles':profiles,'accepted_provider_supplements':supplements,'source_identical_alternate_records':alternates,'parents':[rec(REV/'arithmetic-control-bisim-perm215-replay.json'),rec(REV/'arithmetic-enum-soundnessperm222-replay.json')],'source_guide_pins':guide_pins,'selected_authentication':list(observed.values()),'compiler':B['compiler'],'package_paths':B['LEAN_PATH'][1:],'scope':'No compilation, overlay, provider mutation or proof changes. Old fixed-Dag254/Nat L2 and tape guides are source-only, not selected semantic premises. Generic PositiveSimulation254 is not in these selected closures: an eventual direct import requires separate source/object authentication (or explicitly authorized unchanged fresh replay).'}
path=RES/'c222-dagperm-runtime-cache-plan-20261027.json';path.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'output':rec(path),'profiles':{n:x['counts']for n,x in profiles.items()},'observations':len(observed),'source_guides':len(guide_pins)},indent=2))
