from pathlib import Path
import hashlib,json,re,shutil
R=Path('/home/codex/.codex/worktrees/46be/Proofs');D=R/'Computability/DiophantineConsistency'
P=D/'research/arithmetic-pell-power-recovery-cache-plan.json';O=D/'research/arithmetic-pell-squared-seed-cache-plan.json'
pins={};observations=0

def need(c,m):
 if not c:raise RuntimeError(m)
def rec(p):
 p=Path(p);b=p.read_bytes();return dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
def check(x):
 global observations
 a=rec(x['path']);need(a['sha256']==x['sha256'],'hash '+x['path']);pins[a['path']]=a;observations+=1;return a
def imports(p):
 s=Path(p).read_text();o=[];i=depth=0
 while i<len(s):
  t=s[i:i+2]
  if depth:
   if t=='/-':depth+=1;i+=2
   elif t=='-/':depth-=1;i+=2
   else:o.append('\n'if s[i]=='\n'else' ');i+=1
  elif t=='/-':depth=1;i+=2
  elif t=='--':
   while i<len(s)and s[i]!='\n':i+=1
  else:o.append(s[i]);i+=1
 need(depth==0,'comments');s=''.join(o)
 return list(dict.fromkeys(([]if re.search(r'^\s*prelude\s*$',s,re.M)else['Init'])+[n for line in re.findall(r'^\s*(?:(?:public|private|meta)\s+)*import\s+([^\n]+)',s,re.M)for n in line.split()]))
need(not O.exists(),'fresh inventory');need(shutil.disk_usage('/tmp').free>=512*1024**2,'reserve')
check(dict(path=str(P),sha256='2884c1845d1c273ad9139dfc5955970271f62846b61f667efff0921a6d88e2ad'))
j=json.loads(P.read_text())
for x in j['pins']:check(x)
mods={x['module']:x for x in j['modules']};ext={x['module']:x for x in j['external']};seen=set();active=set();used=set();order=[]
def visit(n):
 if n not in mods:need(n in ext,'unknown '+n);used.add(n);return
 if n in seen:return
 need(n not in active,'cycle');active.add(n);m=mods[n];check(m['source']);actual=imports(m['source']['path']);need(actual==m['imports'],'header '+n)
 for c in actual:visit(c)
 for x in m['objects']:check(x)
 active.remove(n);seen.add(n);order.append(n)
direct=['DiophantineConsistency.ArithmeticPellPeriodicity']
for n in direct:visit(n)
modules=[mods[n]for n in order];external=[ext[n]for n in sorted(used)];providers=[]
search=['/tmp/arithmetic-pell-first-index-root-obnhr4v8/lib',*j['boundary_search']]
for m in modules+external:
 check(m['source'])
 for obj in m.get('objects',m.get('artifacts',[])):
  check(obj);rel=Path(*m['module'].split('.')[:-1])/Path(obj['path']).name
  p=next((Path(q)/rel for q in search if(Path(q)/rel).is_file()),None)
  need(p is not None,'missing '+str(rel));a=check(dict(obj,path=str(p)));providers.append(dict(module=m['module'],relative=str(rel),expected=obj,actual=a))
counts=dict(custom=len(modules),Foundation=sum(n.startswith('Foundation.')for n in order),artifacts=sum(len(m['objects'])for m in modules),external=len(external),boundary_artifacts=sum(len(m['artifacts'])for m in external),actual_first_providers=len(providers),fresh_prerequisites=0)
check(j['compiler']);check(rec(__file__));check(rec(D/'research/arithmetic-pell-squared-seed-proposal.md'))
for x in list(pins.values()):check(x)
result=dict(status='READ_ONLY_PLAN_NO_LEAN_OVERLAY_OR_REFRESH',parent=rec(P),direct_imports=direct,counts=counts,modules=modules,topological_order=order,external=external,boundary_search=j['boundary_search'],compiler=j['compiler'],first_providers=providers,pins=list(pins.values()),observations=observations,unique_paths=len(pins),proposal=rec(D/'research/arithmetic-pell-squared-seed-proposal.md'),auditor=rec(__file__),scope='Direct positive strong seed at explicit internal index R*ycoord(R,a); no arbitrary-modulus pigeonhole premise, full cofinal polynomial converse remains open.')
O.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(dict(plan=rec(O),counts=counts,observations=observations,unique_paths=len(pins)),indent=2))
