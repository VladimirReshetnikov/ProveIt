from pathlib import Path
import hashlib,json,re,shutil
R=Path('/home/codex/.codex/worktrees/46be/Proofs');D=R/'Computability/DiophantineConsistency';H=D/'research'
def need(c,m):
 if not c:raise RuntimeError(m)
def rec(p):
 p=Path(p);p=p if p.is_absolute()else R/p;b=p.read_bytes();return dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
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
 need(depth==0,'comments');s=''.join(out)
 return list(dict.fromkeys(([]if re.search(r'^\s*prelude\s*$',s,re.M)else['Init'])+[n for line in re.findall(r'^\s*(?:(?:public|private|meta)\s+)*import\s+([^\n]+)',s,re.M)for n in line.split()]))
cases=[dict(name='arithmetic-carrier-soundness2011',plan='arithmetic-carrier-soundness2011-cache-plan.json',psha='f6672cfd5ef1d6d487fefb2060821cd7feb0c8b4b46644db215525535f1a8a8d',mf='arithmetic-carrier-soundness2011-plan-FILES.json',msha='459032856ea45191d2f311ec0c6922ac5eba41e50d8fbcbe5b36f04373a307da',files=7,counts=(135,95,420,50,570)),dict(name='validator-seed-transitive222',plan='validator-seed-transitive-plan.json',psha='ab31208a45cd28e5950c62b6133d4f79a8f650bdc31838028a0a22f3d7ea8f43',mf='validator-seed-transitive-plan-FILES.json',msha='5c8e9503904ad6d411f3e8a8d057cd7081be6101c851d9a4cf29cbb713dcf6fd',files=4,counts=(217,136,625,45,670)),dict(name='arithmetic-runtime215',plan='c222-runtime215-composition-plan-20261027/cache-plan.json',psha='4a93686eebfefcd2b325e88a9644e9a7aad5f8a45e4744bafb287959377ebb34',mf='c222-runtime215-composition-plan-20261027/FILES.json',msha='6419d84589931c450ac7ea94915c50285bf0457ed14111bcd2356b55179ad4b6',files=7,counts=(207,95,492,41,656))]
for case in cases:
 pins={};observations=0
 def check(x):
  global observations
  a=rec(x['path']);need(a['sha256']==x['sha256'],'hash '+str(x['path']))
  if 'bytes'in x:need(a['bytes']==x['bytes'],'bytes')
  pins[a['path']]=a;observations+=1;return a
 def load(p,h):check(dict(path=str(p),sha256=h));return json.loads(Path(p).read_text())
 mf=H/case['mf'];entries=load(mf,case['msha']);entries=entries.get('files',[])if isinstance(entries,dict)else entries
 need(len(entries)==case['files'],'manifest size')
 for x in entries:
  p=Path(x['path']);base=R if p.parts[0]in ['Computability','Logic']else mf.parent
  check(dict(x,path=str(base/p)))
 plan=load(H/case['plan'],case['psha'])
 for x in plan.get('pins',plan.get('authenticated_pins',plan.get('observations',[]))):check(x)
 rows=plan.get('modules',plan.get('modules_dependency_order'));mods={x['module']:x for x in rows};ext={x['module']:x for x in plan['external']}
 seen=set();active=set();used=set();order=[];expected={}
 def source(x):return x['source']if isinstance(x['source'],dict)else dict(path=x['source'],sha256=x['source_sha256'])
 def artifacts(x):return x.get('objects',x.get('artifacts',[x['object'],*x.get('companion_observations',[])]if'object'in x else[x]))
 def add(n,obj):
  a=check(obj);rel=str(Path(*n.split('.')[:-1])/Path(a['path']).name);need(rel not in expected,'duplicate relative');expected[rel]=(n,a['sha256'])
 def visit(n):
  if n not in mods:need(n in ext,'unknown '+n);used.add(n);return
  if n in seen:return
  need(n not in active,'cycle');active.add(n);m=mods[n];s=check(source(m));actual=imports(s['path']);need(actual==m.get('actual_imports',m.get('imports')),'header '+n)
  need(not m.get('refresh',False),'refresh')
  for c in actual:visit(c)
  for obj in m['objects']:add(n,obj)
  active.remove(n);seen.add(n);order.append(n)
 for n in plan.get('direct_imports',plan.get('imports')):visit(n)
 need(seen==set(mods)and used==set(ext),'reachable DAG')
 if 'topological_order'in plan:need(order==plan['topological_order'],'topological order')
 for n,m in ext.items():
  if 'source'in m:check(source(m))
  for obj in artifacts(m):add(n,obj)
 providers=plan.get('first_providers',plan.get('actual_first_artifact_providers'));matched=set()
 paths=plan.get('audited_existing_search',plan.get('existing_search_path',plan.get('package_paths')))
 for x in providers:
  rel=x.get('relative',x.get('relative_path'));p=x.get('actual',x.get('provider',x));a=check(p)
  need(rel in expected and expected[rel]==(x['module'],a['sha256']),'provider mapping '+str(rel));need(rel not in matched,'duplicate provider');matched.add(rel)
  if 'actual'in x:check(x['expected'])
  if 'kind'not in x or x['module']in ext:
   first=next((Path(q)/rel for q in paths if(Path(q)/rel).is_file()),None)
   need(first is not None and first.resolve()==Path(a['path']).resolve(),'first provider '+rel)
 need(matched==set(expected),'provider coverage')
 counts=(len(mods),sum(n.startswith('Foundation.')for n in mods),sum(len(m['objects'])for m in mods.values()),len(ext),len(providers));need(counts==case['counts'],'exact counts')
 need(not plan.get('new_prerequisite_refresh',[]),'no new refresh');check(plan['compiler']);check(rec(__file__))
 for x in list(pins.values()):check(x)
 need(shutil.disk_usage('/tmp').free>=512*1024**2,'disk reserve')
 out=D/'reviews'/(case['name']+'-plan-root.json');need(not out.exists(),'new ROOT audit')
 result=dict(status='ROOT_READ_ONLY_REVIEW_PASS',plan=rec(H/case['plan']),manifest=rec(mf),counts=counts,observations=observations,unique_paths=len(pins),pins=list(pins.values()),driver=rec(__file__),qualification='Independent metadata reauthentication, source/header DAG and exact provider coverage. Full proposals and planner sources reviewed separately. No compiler, overlay or dependency refresh.')
 out.write_text(json.dumps(result,indent=2)+'\n');print(case['name'],counts,observations,len(pins),rec(out),flush=True)
