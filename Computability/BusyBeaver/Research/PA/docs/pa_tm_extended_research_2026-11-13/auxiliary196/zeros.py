from core import *
from collections import deque,Counter
import time
ss,ins=program();seen=[0]*len(ins);seen[25]=1<<1;todo=deque([(25,1)]);steps=0;start=__import__('time').time()
while todo:
 pc,m=todo.popleft();op=ins[pc];steps+=1
 nxt=[]
 if op[0]=='inc':
  _,r,q=op;nxt=[(q,m|1<<r)]
 elif op[0]=='dec':
  _,r,z,p=op
  if m>>r&1:nxt=[(p,m),(p,m&~(1<<r))]
  else:nxt=[(z,m)]
 elif op[0]=='jump':nxt=[(op[1],m)]
 for q,mm in nxt:
  if q==len(ins):q=0
  flag=1<<mm
  if not seen[q]&flag:seen[q]|=flag;todo.append((q,mm))
zeros=[]
for i,bits in enumerate(seen):
 ms=[m for m in range(512)if bits>>m&1];union=0
 for m in ms:union|=m
 zz=[r for r in range(9)if not union>>r&1]if ms else []
 zeros.append(zz)
 if ss[i][1]=='breakTo':print(i,ss[i],zz,len(ms))
Path('zero_invariants.json').write_text(json.dumps({'steps':steps,'seconds':time.time()-start,'known_zero':zeros,'reachable_masks':[str(x)for x in seen]},indent=2))
print('done',steps,time.time()-start)
