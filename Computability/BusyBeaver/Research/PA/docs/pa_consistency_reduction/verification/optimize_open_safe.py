#!/usr/bin/env python3
"""Expose closed copy suffixes while preserving the exact AX source word."""
import symbolic as S
from pathlib import Path
import sys,json,random,math,time,collections,re,functools
WORK=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(WORK/'math_reduction/grammar'))
from rotate_search import tree,nodes,paths,replace,replace_one,expand
from search_grammar import TOKENS as T0
sys.path.insert(0,str(WORK/'math_reduction/folding'))
import compatible_folds as F
TOKENS=dict(T0, node57='h',node54='a',node69='d')
NM=json.loads((WORK/'verification/node_map.json').read_text())
ATOM={v:NM[k][0] for k,v in TOKENS.items()}|{'i':58}
FREE={('i','i'):87,(('i','i'),('i','i')):121,('P','h'):12,('P','a'):86,('P','d'):116}
BASE={k:v for k,v in S.load_machine().items()if k[0]<134}
RAW=S.source_tree()[1]
LEADING={};MAXRUN={}
for name,atom in TOKENS.items():
 pp=[''.join(map(str,p)) for p,op in S.flatten(RAW[name])]
 LEADING[atom]=max(len(x)-len(x.lstrip('0')) for x in pp)
 MAXRUN[atom]=max([0]+[len(z)for x in pp for z in re.findall('0+',x)])
LEADING.update(i=0,B=0);MAXRUN.update(i=0,B=0)
@functools.lru_cache(maxsize=200000)
def zero_shape(t):
 if isinstance(t,str):return LEADING[t],MAXRUN[t]
 la,ma=zero_shape(t[0]);lb,mb=zero_shape(t[1])
 return 1+la,max(1+la,ma,mb)
def opened(t):
 if t=='H':return ('P','h')
 if t=='A':return ('P','a')
 if t=='D':return ('P','d')
 if isinstance(t,str):return t
 return tuple(map(opened,t))
def evaluate(t):
 if zero_shape(t)[1]>6:return 1000,len(nodes(t)),0,[]
 new={};m=BASE.copy()
 def emit(x):
  if x in FREE:return FREE[x]
  if isinstance(x,str):return ATOM[x]
  if x in new:return new[x]
  a,b=x
  def row(y,bit):return (0,-1,131 if bit else 5) if y=='B' else (bit,1,emit(y))
  z0=row(a,0);z1=row(b,1)
  q=1000+len(new);new[x]=q;m[q,0]=z0;m[q,1]=z1
  return q
 entry=emit(t);m[89,1]=(1,1,entry)
 tags=collections.defaultdict(set)
 for (q,b),(w,d,r)in m.items():tags[r].update([w]if d==1 else [0,1])
 if any(x[0]=='G' or x[1] in ('R','S') for x in new):return 1000,len(new),0,[]
 # Retain exactly the control graph reachable from blank's state0.
 reached={0};todo=[0]
 while todo:
  q=todo.pop()
  for b in (0,1):
   if (q,b) not in m:continue
   z=m[q,b][2]
   if z not in reached:reached.add(z);todo.append(z)
 m={k:v for k,v in m.items()if k[0]in reached}
 protected={q for q,b in S.ENGINE_ROWS}|{m[k][2] for k in S.ENGINE_ROWS if k in m}|{0,S.ROOT}
 candidates={q for q,b in m if q not in protected}
 opts=F.candidates(m,candidates)
 selected,tested=F.best_subset(m,opts)
 return len(m)//2-len(selected),len(m)//2,len(selected),selected

def output(t,path):
 rules={};rev={}
 def go(q):
  if isinstance(q,str):return q
  if q in rev:return rev[q]
  a,b=map(go,q);n=f'r{len(rules)}';rev[q]=n;rules[n]=(a,b)
  return n
 root=go(t)
 data={'nodes':len(rules),'root':root,'rules':rules,'tokens':TOKENS,'word':expand(t)}
 path.write_text(json.dumps(data,indent=2))

def main():
 budget=int(sys.argv[1])if len(sys.argv)>1 else 30000
 rng=random.Random(int(sys.argv[2]) if len(sys.argv)>2 else 424273)
 base=opened(tree('x67'));bestt=base;best=evaluate(base)[0]
 t=base;score=best;start=time.monotonic()
 print('BASE',evaluate(base),flush=True)
 output(base,Path(__file__).with_name('open_safe_base.json'))
 seen={base};ties=[]
 for it in range(budget):
  if it%3000==0:t=rng.choice([base,bestt]+ties[-12:]);score=evaluate(t)[0]
  cand=t
  for _ in range(2 if rng.random()<.12 else 1):
   ps=paths(cand);p,q=rng.choice(ps);a,b=q
   if rng.randrange(2):
    if not isinstance(a,tuple):continue
    u,v=a;alt=(u,(v,b))
   else:
    if not isinstance(b,tuple):continue
    u,v=b;alt=((a,u),v)
   cand=replace(cand,q,alt)if rng.random()<.7 else replace_one(cand,p,alt)
  if cand in seen:continue
  seen.add(cand)
  if len(nodes(cand))>83:continue
  s,n,c,ds=evaluate(cand)
  temp=.45*(1-(it%3000)/3000)+.05
  if s<1000 and (s<=score or rng.random()<math.exp((score-s)/temp)):t=cand;score=s
  if s<=best:
   if s<best:best=s;bestt=cand;print('BEST',best,n,c,'iteration',it,'seconds',round(time.monotonic()-start,1),flush=True)
   if len(ties)<200:ties.append(cand)
   if s<196:
    path=Path(__file__).with_name(f'open_safe_{s}_{it}.json');output(cand,path)
    print('TARGET',path.name,ds,flush=True)
    if s<=194:break
  if it%10000==0:print('progress',it,'best',best,'current',score,'seconds',round(time.monotonic()-start,1),flush=True)
 print('DONE','best',best,'visited',len(seen),'seconds',round(time.monotonic()-start,1),flush=True)
if __name__=='__main__':main()
