"""Parse a changed AX word using existing context-correct stored subtrees."""
from pathlib import Path
import sys,json,random,collections,time
import symbolic as S
WORK=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(WORK/'math_reduction/grammar'))
from rotate_search import tree,expand,output
from search_grammar import DEFS,TOKENS
m0=S.load_machine();NM=json.loads((WORK/'verification/node_map.json').read_text());base=tree('x67')
def pure(q):return all(m0[q,b][:2]==(b,1)for b in(0,1))
tags=collections.defaultdict(set)
def visit(t,b):
 if isinstance(t,str):return
 tags[t].add(b);visit(t[0],0);visit(t[1],1)
visit(base,1)
fixed={}
for name in DEFS:
 if name.startswith('x'):
  t=tree(name);q=NM[name][0];fixed[t]=(q,{0,1}if pure(q)else tags[t])
for name,token in TOKENS.items():
 q=NM[name][0];fixed[token]=(q,{0,1}if pure(q)else ({1}if token=='G'else {0}))
fixed['i']=(58,{0,1});fixed[('i','i')]=(87,{0,1});fixed[(('i','i'),('i','i'))]=(121,{0,1})
free_by_word=collections.defaultdict(list)
for t,v in fixed.items():free_by_word[tuple(expand(t))].append(t)
def make(t):
 m=m0.copy();new={}
 def emit(t,b):
  if t in fixed and b in fixed[t][1]:return fixed[t][0]
  if t in new:return new[t]
  if isinstance(t,str):raise ValueError(('tag',t,b))
  def row(y,b):return(0,-1,131 if b else 5)if y=='B'else(b,1,emit(y,b))
  z0=row(t[0],0);z1=row(t[1],1);q=2000+len(new);new[t]=q;m[q,0]=z0;m[q,1]=z1;return q
 entry=emit(t,1);m[89,1]=(1,1,entry)
 reached={0};todo=[0]
 while todo:
  q=todo.pop()
  for b in(0,1):
   if(q,b)not in m:continue
   z=m[q,b][2]
   if z not in reached:reached.add(z);todo.append(z)
 m={k:v for k,v in m.items()if k[0]in reached}
 return m,len(new)
def parse(word,seed):
 rng=random.Random(seed);n=len(word);cost={};ts={}
 for length in range(1,n+1):
  for i in range(n-length+1):
   j=i+length;s=tuple(word[i:j]);free=free_by_word.get(s,[])
   if length==1:
    for b in(0,1):
     if word[i]=='B' or(word[i]in fixed and b in fixed[word[i]][1]):cost[i,j,b]=0;ts[i,j,b]=word[i]
     else:cost[i,j,b]=999
    continue
   vals=[]
   for k in range(i+1,j):
    v=cost[i,k,0]+cost[k,j,1]+1
    if v<999:vals.append((v+rng.random()*.1,k))
   best=min(vals)if vals else(999,None)
   for b in(0,1):
    opts=[t for t in free if b in fixed[t][1]]
    if opts:cost[i,j,b]=0;ts[i,j,b]=rng.choice(opts)
    else:
     cost[i,j,b]=int(best[0]);k=best[1]
     if k is not None:ts[i,j,b]=(ts[i,k,0],ts[k,j,1])
 return ts[0,n,1],cost[0,n,1]
if __name__=='__main__':
 word=json.load(open('math_reduction/folding/integrated_start.json'))['opaque_word'];best=1000;start=time.time()
 for seed in range(100):
  t,c=parse(word,seed);m,nn=make(t);score=len(m)//2
  if score<best:
   best=score;path=Path(__file__).with_name(f'integrated_reuse_{score}.json');output(t,path);d=json.load(open(path));d['word']=word;d['design']='integrated witness gate';path.write_text(json.dumps(d,indent=2))
   print('BEST',best,'new',nn,'DPcost',c,'seed',seed,'seconds',time.time()-start,flush=True)
 print('DONE',best,time.time()-start,flush=True)
