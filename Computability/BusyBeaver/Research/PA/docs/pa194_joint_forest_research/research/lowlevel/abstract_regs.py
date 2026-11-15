from common import *
K=3
init=tuple((2,2)if j==0 else(0,0)for j in range(9));vals={25:init};queue=collections.deque([25]);scheduled={25};steps=0
# Infinity for upper cap = K+1; lower cap K.
def join(a,b):return tuple((min(x[0],y[0]),max(x[1],y[1]))for x,y in zip(a,b))
def push(pc,v):
 if pc in vals:
  v=join(vals[pc],v)
  if vals[pc]==v:return
 vals[pc]=v
 if pc not in scheduled:queue.append(pc);scheduled.add(pc)
while queue:
 i=queue.popleft();scheduled.remove(i);v=vals[i];c=ins[i];steps+=1
 if c[0]=='inc':
  _,j,p=c;a,b=v[j];w=list(v);w[j]=(min(K,a+1),min(K+1,b+1));push(p,tuple(w))
 elif c[0]=='dec':
  _,j,z,p=c;a,b=v[j]
  if a==0:
   w=list(v);w[j]=(0,0);push(z,tuple(w))
  if b>0:
   w=list(v);w[j]=(max(0,a-1),K+1 if b==K+1 else b-1);push(p,tuple(w))
 elif c[0]=='jump':push(c[1],v)
static=[]
for i,c in enumerate(ins):
 if c[0]=='dec' and i in vals:
  a,b=vals[i][c[1]]
  if b==0 or a>0:static.append({'site':i,'instruction':c,'interval':vals[i],'branch':'zero'if b==0 else'positive'})
result={'reachable':len(vals),'steps':steps,'static_decrements':static,'intervals':vals,'unreachable':[i for i in range(len(ins))if i not in vals]};(B/'abstract_regs.json').write_text(json.dumps(result,indent=2));print('Reachable',len(vals),'static',len(static),'unreachable',len(ins)-len(vals),'iterations',steps);print(static[:30]);print(result['unreachable'][:100])
