#!/usr/bin/env python3
"""Bounded heuristic search for seven consumed U15 affine projections.

Emits only controller candidates, never a complete Diophantine compiler.
The independent complete505 wrapper authenticates and proves its frozen winner.
"""
import argparse,collections,hashlib,itertools,json,random
from pathlib import Path
PARENT='u15_packed_loader_offset506.json'
PIN='8337d0ec9ddf7d5857e1d64bf33798e7ae149494346855120e7c8346b129800e'
CUTS=('binary75','binary76','binary77','v131','v140','v156','binary89')
CONSTANTS=dict(zip(CUTS,(-29,-14,-15,-18,-16,1,17)))
def read_rules(root):
 data=(Path(root)/PARENT).read_bytes()
 if hashlib.sha256(data).hexdigest()!=PIN:raise ValueError('Changed parent receipt')
 return next(x['compiler']['rules'] for x in json.loads(data)['forms'] if x['form']=='base:1:1')
def weights(rules):
 return {n:[1 if k==0 else r[1] if k==1 else r[3] if k==2 else 2*r[3]*r[4] if k==3 else 2*(1-r[3])*r[4] if k==4 else r[0]-7 if k==5 else r[2]-7 for r in rules] for k,n in enumerate(CUTS)}
class DAG:
 def __init__(self):self.rows=[];self.memo={}
 def op(self,op,a,b):
  if op in ('+','*') and repr(a)>repr(b):a,b=b,a
  if type(a)is int and type(b)is int:return a+b if op=='+' else a-b if op=='-' else a*b
  if op=='+' and a==0:return b
  if op=='+' and b==0:return a
  if op=='-' and b==0:return a
  if op=='-' and a==b:return 0
  if op=='*' and (a==0 or b==0):return 0
  if op=='*' and a==1:return b
  if op=='*' and b==1:return a
  key=op,a,b
  if key not in self.memo:
   n='c'+str(len(self.rows));self.memo[key]=n;self.rows.append((n,op,a,b))
  return self.memo[key]
 def sum(self,vals):
  z=0
  for v in vals:z=self.op('+',z,v)
  return z
 def linear(self,f):
  a=[];b=[]
  for n,v in sorted(f.items()):
   if v:(a if v>0 else b).append(n if abs(v)==1 else self.op('*',abs(v),n))
  return self.op('-',self.sum(a),self.sum(b))
def digits(n,mode):
 sign=1 if n>=0 else -1;n=abs(n);a=[]
 while n:
  d=n%2 if mode=='binary' else 0 if n%2==0 else (1 if n%4==1 or n==1 else -1)
  a.append(sign*d);n=(n-d)//2
 return a

def initial(mode,rules):
 WEIGHTS=weights(rules)
 forms={n:{f'edge{i}':v for i,v in enumerate(WEIGHTS[n]) if v} for n in CUTS};extra={};plans={}
 for n,f in forms.items():
  if mode=='direct' or n not in ('v156','binary89'):extra[n]=f;plans[n]=[n];continue
  ds={k:digits(v,mode) for k,v in f.items()};size=max(map(len,ds.values()));plans[n]=[n+'_'+str(j) for j in range(size)]
  for j,name in enumerate(plans[n]):extra[name]={k:dd[j] for k,dd in ds.items() if j<len(dd) and dd[j]}
 return extra,plans

def cost(f):
 pos=sum(v>0 for v in f.values());neg=sum(v<0 for v in f.values());m=sum(abs(v)>1 for v in f.values())
 return max(0,pos-1)+max(0,neg-1)+int(neg>0)+m

def run(mode,seed,rules):
 if mode not in ('binary','naf','direct') or type(seed)is not int:raise ValueError('Mode and integer seed required')
 rng=random.Random(seed);forms,plans=initial(mode,rules);d=DAG()
 while True:
  candidates=collections.defaultdict(list)
  for name,f in forms.items():
   bins=collections.defaultdict(list)
   for n,v in f.items():bins[abs(v)].append((n,1 if v>0 else -1))
   for terms in bins.values():
    for (a,sa),(b,sb) in itertools.combinations(sorted(terms),2):candidates[(a,b,sa*sb)].append(name)
  choices=[];best=0
  for (a,b,s),names in candidates.items():
   gain=-1
   for name in names:
    f=forms[name];ff=dict(f);v=ff.pop(a);ff.pop(b);ff['$new']=v;gain+=cost(f)-cost(ff)
   if gain>best:choices=[];best=gain
   if gain==best and gain>0:choices.append((a,b,s,names))
  if not choices:break
  a,b,s,names=rng.choice(choices);n=d.op('+' if s==1 else '-',a,b)
  for name in names:
   f=forms[name];v=f.pop(a);f.pop(b);f[n]=v
 refs={name:d.linear(f) for name,f in forms.items()};cuts={}
 for name,terms in plans.items():
  v=refs[terms[-1]]
  for t in reversed(terms[:-1]):v=d.op('+',d.op('*',2,v),refs[t])
  cuts[name]=d.op('+',v,CONSTANTS[name])
 live=set(cuts.values())
 for n,op,a,b in reversed(d.rows):
  if n in live:live.update(v for v in (a,b) if type(v)is str)
 rows=[r for r in d.rows if r[0]in live]
 return rows,cuts
def proof(rows,cuts,rules):
 expected=weights(rules);env={f'edge{i}':tuple(int(j==i) for j in range(30)) for i in range(29)}
 def atom(x):return env[x] if type(x)is str else (0,)*29+(x,)
 for n,op,a,b in rows:
  a,b=atom(a),atom(b)
  if op=='*':
   if any(a[:-1]) and any(b[:-1]):raise ValueError('Nonlinear candidate')
   if any(a[:-1]):a,b=b,a
   out=tuple(a[-1]*v for v in b)
  else:out=tuple(x+(1 if op=='+' else -1)*y for x,y in zip(a,b))
  env[n]=out
 for n,out in cuts.items():
  if env[out]!=tuple(expected[n])+(CONSTANTS[n],):raise ValueError('Wrong actual affine coefficients')
 return True
if __name__=='__main__':
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--root',type=Path,default=Path(__file__).resolve().parent)
 ap.add_argument('--modes',nargs='+',choices=('binary','naf','direct'),default=['binary','naf','direct'])
 ap.add_argument('--start',type=int,default=0);ap.add_argument('--stop',type=int,default=500)
 ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
 if a.start<0 or a.stop<=a.start:ap.error('Require 0 <= start < stop')
 rules=read_rules(a.root);summary=[]
 for mode in a.modes:
  sizes=collections.Counter();best=None
  for seed in range(a.start,a.stop):
   rows,cuts=run(mode,seed,rules);proof(rows,cuts,rules);n=len(rows);sizes[n]+=1
   if best is None or n<best['count']:best=dict(mode=mode,seed=seed,count=n,rows=rows,cuts=cuts)
  summary.append(dict(mode=mode,seed_start=a.start,seed_stop_exclusive=a.stop,counts=dict(sizes),best=best))
  print(mode,best['count'],best['seed'],flush=True)
 a.output.write_text(json.dumps(dict(parent_sha256=PIN,search=summary,scope='Bounded greedy affine-subgraph search, not complete sources or a circuit minimum.'),indent=2,sort_keys=True)+'\n')
