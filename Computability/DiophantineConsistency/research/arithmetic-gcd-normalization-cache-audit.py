from pathlib import Path
import hashlib,json,re
ROOT=Path('/home/codex/.codex/worktrees/46be/Proofs');D=ROOT/'Computability/DiophantineConsistency'
PARENT=D/'research/arithmetic-pell-congruences-cache-plan.json'
OUT=D/'research/arithmetic-gcd-normalization-cache-plan.json'
seenpins={};observations=0
def require(x,msg):
 if not x:raise RuntimeError(msg)
def rec(p):
 p=Path(p);return dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)
def check(x):
 global observations
 a=rec(x['path']);require(a['sha256']==x['sha256'],'hash '+x['path']);seenpins[a['path']]=a;observations+=1;return a
def imports(p):
 s=Path(p).read_text();o=[];i=depth=0
 while i<len(s):
  pair=s[i:i+2]
  if depth:
   if pair=='/-':depth+=1;i+=2
   elif pair=='-/':depth-=1;i+=2
   else:o.append('\n'if s[i]=='\n'else' ');i+=1
  elif pair=='/-':depth=1;i+=2
  elif pair=='--':
   while i<len(s)and s[i]!='\n':i+=1
  else:o.append(s[i]);i+=1
 require(depth==0,'comments')
 return list(dict.fromkeys(['Init']+[n for line in re.findall(r'^\s*(?:(?:public|private|meta)\s+)*import\s+([^\n]+)',''.join(o),re.M)for n in line.split()]))
require(not OUT.exists(),'new inventory')
check(dict(path=str(PARENT),sha256='a5182706264e4a28a0ff58f2a97cf32a2860e7246ff3c04d76a163a9e83f8f99'))
p=json.loads(PARENT.read_text())
for pin in p['pins']:check(pin)
mods={m['module']:m for m in p['modules']};ext={e['module']:e for e in p['external']}
seen=set();active=set();order=[];used=set()
def visit(n):
 if n not in mods:require(n in ext,'new boundary '+n);used.add(n);return
 if n in seen:return
 require(n not in active,'cycle');active.add(n);m=mods[n]
 check(m['source']);require(imports(m['source']['path'])==m['imports'],'header '+n)
 for dep in m['imports']:visit(dep)
 for obj in m['objects']:check(obj)
 active.remove(n);seen.add(n);order.append(n)
direct=['Foundation.FirstOrder.Arithmetic.IOpen.Basic','Mathlib.Tactic.Ring']
for name in direct:visit(name)
bound=[ext[n]for n in sorted(used)];providers=[]
for e in bound:
 check(e['source'])
 for a in e['artifacts']:
  check(a);rel=Path(*e['module'].split('.')[:-1])/Path(a['path']).name
  first=next((Path(q)/rel for q in p['boundary_search']if(Path(q)/rel).is_file()),None)
  require(first is not None,'first provider')
  providers.append(dict(module=e['module'],expected=a,actual=check(dict(a,path=str(first)))))
counts=dict(custom=len(order),Foundation=sum(n.startswith('Foundation.')for n in order),artifacts=sum(len(mods[n]['objects'])for n in order),external=len(bound),boundary_artifacts=sum(len(e['artifacts'])for e in bound),boundary_primaries=len(bound),boundary_companions=sum(len(e['artifacts'])-1 for e in bound),fresh_prerequisites=0)
require(counts==dict(custom=86,Foundation=86,artifacts=344,external=37,boundary_artifacts=111,boundary_primaries=37,boundary_companions=74,fresh_prerequisites=0),'exact narrowed scope')
check(p['compiler']);check(rec(__file__))
for pin in list(seenpins.values()):check(pin)
result=dict(status='READ_ONLY_AUTHENTICATED_PLAN_NO_COMPILER_OR_OVERLAY',parent=rec(PARENT),direct_imports=direct,counts=counts,modules=[mods[n]for n in order],topological_order=order,external=bound,boundary_search=p['boundary_search'],boundary_first_providers=providers,compiler=p['compiler'],audit=rec(__file__),pins=list(seenpins.values()),observations=observations,unique_paths=len(seenpins),scope='New ArithmeticGcdNormalization + Checks only: derive a fixed Sigma1 unique gcd graph through bounded positive natural Bezout minimum, then normalize actual R^2+D=D*f^2 with positive R,D,f. No supplied gcd/coprime/minimality, no common Pell unit consumer, no prerequisite refresh.')
OUT.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(plan=rec(OUT),counts=counts,observations=observations,unique_paths=len(seenpins)),indent=2))
