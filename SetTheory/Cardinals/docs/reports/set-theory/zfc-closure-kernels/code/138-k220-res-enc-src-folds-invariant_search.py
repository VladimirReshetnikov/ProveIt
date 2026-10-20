import json,sys,itertools,collections,time
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
import context as _ctx
import os
BASE=_ctx.BASE; b=_ctx.b; T=_ctx.T
_local_output=_ctx.OUT/'local_folds'; _local_output.mkdir(parents=True,exist_ok=True); os.chdir(_local_output)
Q=sorted({q for q,bit in T}); ENGINE=_ctx.ENGINE
def inv(radius):
 n=2*radius+1;mask=(1<<n)-1
 I={q:0 for q in Q};I[0]=1;todo=collections.deque([(0,0)])
 while todo:
  q,x=todo.popleft();v=x>>radius&1;w,d,z=T[q,v]
  if z not in I:continue
  y=(x&~(1<<radius))|(w<<radius)
  outs=[y>>1,(y>>1)|(1<<(n-1))] if d==1 else [y<<1&mask,(y<<1&mask)|1]
  for yy in outs:
   if not (I[z]>>yy&1):I[z]|=1<<yy;todo.append((z,yy))
 return {q:[x for x in range(1<<n) if I[q]>>x&1] for q in Q}
if __name__=='__main__':
 radius=int(sys.argv[1])if len(sys.argv)>1 else 3;I=inv(radius)
 Path(f'invariant_r{radius}.json').write_text(json.dumps(I,indent=2))
 for q in Q:
  vals=I[q];c=''.join(str(next(iter(ss)))if len(ss:={x>>i&1 for x in vals})==1 else '?' for i in range(2*radius+1))
  print(q, 'E'if q in ENGINE else'D',len(vals),c)
