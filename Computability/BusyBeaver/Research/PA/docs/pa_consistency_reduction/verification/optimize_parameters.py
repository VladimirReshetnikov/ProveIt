#!/usr/bin/env python3
"""Permute six independent axiom heads and optimize their physical bracketing."""
import symbolic as S, optimize_bounded as B
from pathlib import Path
import sys,json,random,math,time,collections,functools
WORK=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(WORK/'math_reduction/folding'))
import compatible_folds as F
import fast_folds
from rotate_search import tree,nodes,paths,replace,replace_one,expand
from search_grammar import TOKENS,WORD
@functools.lru_cache(maxsize=100000)
def width(t):return 1 if isinstance(t,str) else width(t[0])+width(t[1])
def join(a,b):return b if a is None else a if b is None else (a,b)
def split(t,k):
 if k==0:return None,t
 if k==width(t):return t,None
 a,b=t;n=width(a)
 if k<n:
  x,y=split(a,k);return x,join(y,b)
 if k==n:return a,b
 x,y=split(b,k-n);return join(a,x),y

def headswap(t,order,rng):
 sizes=[17,19,16,16,16,19]
 units=[];pre,tail=split(t,18)
 for i in order:
  h,tail=split(tail,sizes[i]);units.append(h)
 a,b=rng.sample(range(6),2);units[a],units[b]=units[b],units[a]
 neworder=list(order);neworder[a],neworder[b]=neworder[b],neworder[a]
 # Preserve cut boundary fragments and vary the concatenation skeleton.
 items=[pre]+units+[tail]
 def assemble(xs):
  if len(xs)==1:return xs[0]
  mid=rng.randrange(1,len(xs));return assemble(xs[:mid]),assemble(xs[mid:])
 return assemble(items),tuple(neworder)

def parameter_change(t,order,rng):
 sizes=[17,19,16,16,16,19]
 j=rng.randrange(6);lo=18+sum(sizes[i]for i in order[:j]);hi=lo+sizes[order[j]]
 names=list('HAD');new=rng.sample(names,3);mapping=dict(zip(names,new))
 def go(q,start):
  end=start+width(q)
  if end<=lo or start>=hi:return q
  if isinstance(q,str):return mapping.get(q,q)
  a,b=q;return go(a,start),go(b,start+width(a))
 return go(t,0)

def evaluate(t):
 if B.zero_shape(t)[1]>6:return 1000,0,0,[]
 new={};m=B.BASE.copy()
 def emit(x):
  if x in B.FREE:return B.FREE[x]
  if isinstance(x,str):return B.ATOM[x]
  if x in new:return new[x]
  a,b=x
  def row(y,bit):return (0,-1,131 if bit else 5) if y=='B' else (bit,1,emit(y))
  z0=row(a,0);z1=row(b,1)
  q=1000+len(new);new[x]=q;m[q,0]=z0;m[q,1]=z1
  return q
 entry=emit(t);m[89,1]=(1,1,entry)
 if any(x[0]=='G' or x[1]in('R','S')for x in new):return 1000,len(new),0,[]
 reached={0};todo=[0]
 while todo:
  q=todo.pop()
  for b in (0,1):
   if(q,b)not in m:continue
   z=m[q,b][2]
   if z not in reached:reached.add(z);todo.append(z)
 m={k:v for k,v in m.items()if k[0]in reached}
 protected={q for q,b in S.ENGINE_ROWS}|{m[k][2] for k in S.ENGINE_ROWS if k in m}|{0,S.ROOT}
 opts=F.candidates(m,{q for q,b in m if q not in protected})
 selected,tested=fast_folds.select(m,opts)
 return len(m)//2-len(selected),len(m)//2,len(selected),selected

def output(t,order,path):
 rules={};rev={}
 def go(q):
  if isinstance(q,str):return q
  if q in rev:return rev[q]
  a,b=map(go,q);n=f'r{len(rules)}';rev[q]=n;rules[n]=(a,b)
  return n
 root=go(t)
 data={'nodes':len(rules),'root':root,'rules':rules,'tokens':TOKENS,'word':expand(t),'head_permutation':[x+1 for x in order]}
 path.write_text(json.dumps(data,indent=2))

def main():
 budget=int(sys.argv[1])if len(sys.argv)>1 else 100000
 rng=random.Random(int(sys.argv[2])if len(sys.argv)>2 else 382517)
 base=tree('x67');initial=tuple(range(6));best=196;bestt=(base,initial)
 t,order=bestt;score=best;start=time.monotonic();ties=[bestt]
 print('BASE',evaluate(base),flush=True)
 seen={base}
 for it in range(budget):
  if it%5000==0:t,order=rng.choice([bestt]+ties[-30:]);score=evaluate(t)[0]
  neworder=order
  if rng.random()<.015:
   cand,neworder=headswap(t,order,rng)
  elif rng.random()<.10:
   cand=parameter_change(t,order,rng)
  else:
   cand=t
   for _ in range(2 if rng.random()<.15 else 1):
    ps=paths(cand);p,q=rng.choice(ps);a,b=q
    if rng.randrange(2):
     if not isinstance(a,tuple):continue
     u,v=a;alt=(u,(v,b))
    else:
     if not isinstance(b,tuple):continue
     u,v=b;alt=((a,u),v)
    cand=replace(cand,q,alt)if rng.random()<.75 else replace_one(cand,p,alt)
  if cand in seen:continue
  seen.add(cand)
  if len(nodes(cand))>82:continue
  s,n,c,ds=evaluate(cand)
  temp=.75*(1-(it%5000)/5000)+.08
  if s<1000 and(s<=score or rng.random()<math.exp((score-s)/temp)):t=cand;order=neworder;score=s
  if s<=best:
   if s<best:best=s;bestt=(cand,neworder);ties=[];print('BEST',best,n,c,neworder,'iteration',it,'seconds',round(time.monotonic()-start,1),flush=True)
   ties.append((cand,neworder))
   if len(ties)>500:ties.pop(rng.randrange(400))
   if s<196:
    path=Path(__file__).with_name(f'parameter_safe_{s}_{it}.json');output(cand,neworder,path)
    print('TARGET',path.name,ds,flush=True)
    if s<=194:break
  if it%10000==0:print('progress',it,'best',best,'current',score,'order',order,'seconds',round(time.monotonic()-start,1),flush=True)
 print('DONE','best',best,'visited',len(seen),'seconds',round(time.monotonic()-start,1),flush=True)
if __name__=='__main__':main()
