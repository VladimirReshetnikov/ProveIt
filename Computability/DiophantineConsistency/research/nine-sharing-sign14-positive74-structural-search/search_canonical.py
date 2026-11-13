import re,random,json,itertools,hashlib,sys
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
from pathlib import Path
source=Path('Computability/DiophantineConsistency/research/nine-sharing-sign14-positive74-circuit-retry01-check/src/DiophantineConsistency/Sign14Positive74Circuit.lean')
if hashlib.sha256(source.read_bytes()).hexdigest()!='cdd4117cd0b8af7eefbca2d53388068350970f78dba7e73dc9be2fe1b51f105d':raise RuntimeError('source pin')
src=source.read_text().split('def gates : List Gate := [',1)[1].split(']\ndef parents',1)[0];gates=re.findall(r'⟨\.(add|sub|mul), \.(var|port|lit|reg) (-?\d+), \.(var|port|lit|reg) (-?\d+)⟩',src);assert len(gates)==74
N=[];I={}
def node(op,a,b):
 if op in ('add','mul') and str(a)>str(b):a,b=b,a
 k=(op,a,b)
 if k not in I:I[k]=len(N);N.append(k)
 return I[k]
def arg(t,n):return out[int(n)] if t=='reg' else t+':'+n
out=[]
for op,a,b,c,d in gates:out.append(node(op,arg(a,b),arg(c,d)))
root=out[73]
def graph(root):
 seen=set();todo=[root]
 while todo:
  k=todo.pop()
  if isinstance(k,int) and k not in seen:
   seen.add(k);_,a,b=N[k];todo.extend((a,b))
 return seen
def opof(i,op):return isinstance(i,int) and N[i][0]==op
def alternatives(i):
 op,a,b=N[i];ret=set()
 def emit(x):
  if x!=i:ret.add(x)
 if op in ('add','mul'):
  emit(node(op,b,a))
  for pair,other in ((a,b),(b,a)):
   if opof(pair,op):
    x,y=N[pair][1:]
    for l,m,r in itertools.permutations((x,y,other)):
     emit(node(op,node(op,l,m),r));emit(node(op,l,node(op,m,r)))
 if op in ('add','sub'):
  # Expand one signed child into three signed atoms, and reassemble.
  for side in (0,1):
   child=(a,b)[side];other=(b,a)[side];outside=1 if side==0 or op=='add' else -1
   if isinstance(child,int) and N[child][0] in ('add','sub'):
    cop,x,y=N[child]; signs=[(other,1 if side==1 or op=='add' else -1),(x,outside),(y,outside*(1 if cop=='add' else -1))]
    for perm in itertools.permutations(signs):
     (x,sx),(y,sy),(z,sz)=perm
     if sx!=1:continue
     inner=node('add' if sy==1 else 'sub',x,y)
     emit(node('add' if sz==1 else 'sub',inner,z))
     if sy==1:emit(node('add' if sz==1 else 'sub',x,node('add' if sz==1 else 'sub',y,z))) if sz==1 else None
     if sy==-1 and sz==-1:emit(node('sub',x,node('add',y,z)))
     if sy==1 and sz==-1:emit(node('add',x,node('sub',y,z)))
     if sy==-1 and sz==1:emit(node('sub',x,node('sub',y,z)))
  # Factor a common product from a sum or difference.
  if opof(a,'mul') and opof(b,'mul'):
   _,a1,a2=N[a];_,b1,b2=N[b]
   for x,y in ((a1,a2),(a2,a1)):
    for z,w in ((b1,b2),(b2,b1)):
     if x==z:emit(node('mul',x,node(op,y,w)));emit(node('mul',node(op,y,w),x))
 if op=='mul':
  # Distribute over +/- on either side.
  for child,other in ((a,b),(b,a)):
   if isinstance(child,int) and N[child][0] in ('add','sub'):
    cop,x,y=N[child]
    emit(node(cop,node('mul',x,other),node('mul',y,other)))
    emit(node(cop,node('mul',other,x),node('mul',other,y)))
 return ret

def replace(root,old,new):
 memo={}
 def go(x):
  if x==old:return new
  if not isinstance(x,int):return x
  if x not in memo:
   op,a,b=N[x];memo[x]=node(op,go(a),go(b))
  return memo[x]
 return go(root)
assert len(graph(root)) == 74
control=node('add',node('mul','control:a','control:b'),node('mul','control:a','control:c'))
if len(graph(control)) != 3 or min(len(graph(x)) for x in alternatives(control)) != 2:raise RuntimeError('factor control')
rng=random.Random(18674); beam={root:[]};seen={root};best=(74,root,[])
for depth in range(12):
 candidates={}
 for r,path in beam.items():
  allg=sorted(graph(r));rng.shuffle(allg)
  for target in allg:
   alt=list(alternatives(target));rng.shuffle(alt)
   for other in alt:
    nr=replace(r,target,other)
    if nr in seen:continue
    seen.add(nr);count=len(graph(nr));
    if count<best[0]:
     best=(count,nr,path+[(target,other)]);print('BEST',depth,count,'rewrites',path+[(target,other)],flush=True)
    if count<=76:candidates[nr]=(count,path+[(target,other)])
 if not candidates:break
 ranked=sorted(candidates.items(),key=lambda x:(x[1][0],rng.random()))[:600];beam={r:p for r,(c,p) in ranked};print('DEPTH',depth,'states',len(candidates),'beam',len(beam),'best',best[0],flush=True)
 if best[0]<74:break
print('DONE',best[0],flush=True)
if best[0]<74:
 Path('/tmp/positive74-canonical-candidate.json').write_text(json.dumps({'root':best[1],'rewrites':best[2],'nodes':N,'original':root,'count':best[0]}))
