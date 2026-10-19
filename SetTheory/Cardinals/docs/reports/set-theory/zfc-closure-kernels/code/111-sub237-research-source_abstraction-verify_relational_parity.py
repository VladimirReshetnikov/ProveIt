#!/usr/bin/env python3
"""Reduced product of finite value classes and full nine-register parity patterns."""
import importlib.util,json,hashlib,time,argparse,sys
from pathlib import Path
from collections import deque
R=Path(__file__).resolve().parent
ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,default=R/'replay-relational');args=ap.parse_args();args.output.mkdir(parents=True,exist_ok=True)
assert __debug__ and not sys.flags.optimize
S=R/'source.json'
assert hashlib.sha256(S.read_bytes()).hexdigest()=='7fd152d1f5371d2a561d4ad1870d241683b010ce7b7a27399b95363a4537cfb6'
spec=importlib.util.spec_from_file_location('source_graph',R/'graph_interface.py');G=importlib.util.module_from_spec(spec);spec.loader.exec_module(G)
ordered,graph,start,depth=G.graph(json.loads(S.read_text()))
K=16;ALL=(1<<(K+2))-1;EVEN=sum(1<<i for i in range(K+2) if i%2==0);ODD=ALL^EVEN
PM=[[sum(1<<v for v in range(512) if (v>>r)&1==b) for b in (0,1)] for r in range(9)]
def box(v):return 1<<(v if v<K else K+v%2)
def shift(a,d):
 result=0
 while a:
  bit=a&-a;i=bit.bit_length()-1;a-=bit
  if i<K:
   if i+d>=0:result|=box(i+d)
  else:
   first=K+((i-K-K)%2);result|=box(first+d)|box(first+2+d)
 return result
def toggle(p,r):return ((p&PM[r][0])<<(1<<r))|((p&PM[r][1])>>(1<<r))
def reduce(a,p):
 for r,m in enumerate(a):
  if m==0:return None
  if not m&EVEN:p&=PM[r][1]
  if not m&ODD:p&=PM[r][0]
 if p==0:return None
 a=list(a)
 for r in range(9):
  if not p&PM[r][0]:a[r]&=ODD
  if not p&PM[r][1]:a[r]&=EVEN
 return tuple(a),p
def transfer(i,ap):
 a,p=ap;d=graph[i]
 if d[0]=='INC':
  n=list(a);n[d[1]]=shift(n[d[1]],1);v=reduce(n,toggle(p,d[1]));assert v;yield d[2],v
 elif d[0]=='DEC':
  r=d[1]
  if a[r]&~1:
   n=list(a);n[r]&=~1;v=reduce(n,p)
   if v:
    n=list(v[0]);n[r]=shift(n[r],-1);w=reduce(n,toggle(v[1],r));assert w;yield d[2],w
  if a[r]&1:
   n=list(a);n[r]=1;v=reduce(n,p&PM[r][0])
   if v:yield d[3],v
 elif d[0]=='JUMP':yield d[1],ap
 else:assert d==('HALT',)
seed=(3,0,0,0,3,0,0,0,0);seedpar=sum((v%2)<<r for r,v in enumerate(seed));facts=[None]*len(graph);facts[start]=(tuple(map(box,seed)),1<<seedpar);todo=deque([start]);pending={start};updates=0;began=time.monotonic()
while todo:
 i=todo.popleft();pending.remove(i)
 for j,new in transfer(i,facts[i]):
  old=facts[j]
  joined=new if old is None else reduce(tuple(a|b for a,b in zip(old[0],new[0])),old[1]|new[1])
  assert joined
  if joined!=old:
   facts[j]=joined;updates+=1
   if j not in pending:pending.add(j);todo.append(j)
for i,f in enumerate(facts):
 if f:
  for j,new in transfer(i,f):assert facts[j] and all(a&~b==0 for a,b in zip(new[0],facts[j][0])) and new[1]&~facts[j][1]==0
assert facts[start][1]&(1<<seedpar) and all(box(v)&~m==0 for v,m in zip(seed,facts[start][0]))
missing=[i for i,f in enumerate(facts) if f is None];forced=[]
for i,f in enumerate(facts):
 if f and graph[i][0]=='DEC':
  mask=f[0][graph[i][1]]
  if mask==1 or not mask&1:forced.append({'index':i,'path':ordered[i][0],'reg':graph[i][1],'only':'zero' if mask==1 else 'positive','zero_registers':[r for r,m in enumerate(f[0]) if m==1]})
summary={'status':'PASS_REDUCED_PRODUCT_POSTFIXPOINT','source_sha256':hashlib.sha256(S.read_bytes()).hexdigest(),'threshold':K,'value_domain':list(range(K))+['large even','large odd'],'parity_domain':'arbitrary subset of the 512 parity patterns of nine registers','initial_registers':seed,'instructions':len(graph),'reachable_in_abstraction':len(graph)-len(missing),'unreachable_instructions':missing,'forced_decrement_guards':forced,'updates':updates,'seconds':time.monotonic()-began}
(args.output/'source_relational_parity_summary.json').write_text(json.dumps(summary,indent=2)+'\n')
(args.output/'source_relational_parity_facts.json').write_text(json.dumps([None if f is None else [f[0],hex(f[1])] for f in facts])+'\n')
print(json.dumps({k:v for k,v in summary.items() if k!='forced_decrement_guards'},indent=2));print('forced',len(forced));print(json.dumps(forced,indent=2))
