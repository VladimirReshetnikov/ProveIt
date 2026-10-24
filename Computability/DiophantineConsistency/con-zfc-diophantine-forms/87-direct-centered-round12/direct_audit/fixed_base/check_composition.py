#!/usr/bin/env python3
"""Independent schematic composition audit with certified arithmetic graphs as cuts."""
import json,pathlib,functools,collections
D=pathlib.Path(__file__).resolve().parent;J=json.loads((D.parent.parent/'direct/fixed_base/circuit.json').read_text());N=J['nodes'];L=J['call_ledger'];E=J['equalities'];over={};counts=collections.Counter()
# Cut the arbitrary polynomial argument of the first factorial; its source binding is audited separately.
first_fact=next(r for r in L if r['kind']=='fact');over[first_fact['arguments'][0]]=('arbitrary_upper_bound',)
def req(c,m):
 if not c:raise ValueError(m)
def calc(op,*args):
 if op in ['add','mul']:
  flat=[];num=0 if op=='add' else 1
  for a in args:
   if a[0]==op:flat.extend(a[1:])
   else:flat.append(a)
  out=[]
  for a in flat:
   if a[0]=='c':num=num+a[1] if op=='add' else num*a[1]
   else:out.append(a)
  if op=='mul' and num==0:return ('c',0)
  if (op=='add' and num) or (op=='mul' and num!=1):out.append(('c',num))
  if not out:return ('c',num)
  if len(out)==1:return out[0]
  return (op,*sorted(out,key=repr))
 return (op,*args)
def c(x):return('c',x)
def A(*xs):return calc('add',*xs)
def M(*xs):return calc('mul',*xs)
def Pow(a,b):return('pow',a,b)
def Div(a,b):return('div',a,b)
def Mod(a,b):return('mod',a,b)
def Choose(a,b):return('choose',a,b)
def Fact(a):return('fact',a)
def Pred(a):return('pred',a)
def evaluator():
 @functools.lru_cache(None)
 def ev(i):
  if i in over:return over[i]
  n=N[i]
  if n[0]=='c':return c(n[1])
  if n[0]=='v':return ('v',n[1])
  return calc('add' if n[0]=='a' else 'mul',ev(n[1]),ev(n[2]))
 return ev
for ix,row in enumerate(L):
 ev=evaluator();args=list(map(ev,row['arguments']));typ=row['kind'];res=row['result']
 if typ=='pell':continue
 if typ=='pow':over[res]=Pow(*args)
 elif typ=='divmod':
  over[res[0]]=Div(*args);over[res[1]]=Mod(*args)
 elif typ=='choose':
  n,k=args;q=A(Pow(c(2),n),c(1));want=Mod(Div(Pow(A(q,c(1)),n),Pow(q,k)),q)
  req(ev(res)==want,'choose composition '+str(ix));over[res]=Choose(n,k)
 elif typ=='fact':
  n=args[0];radius=Pow(A(n,c(2)),A(n,c(2)));choose=Choose(A(radius,n),n)
  # The sole factorial-level predecessor equality encodes choose-1.
  eqs=[eq for eq in E[row['before'][1]:row['after'][1]] if eq[2]=='positive binomial predecessor'];req(len(eqs)==1,'factorial predecessor count')
  left,right,_=eqs[0];req(ev(left)==choose,'factorial binomial mismatch');rr=N[right];req(rr[0]=='a','predecessor sum')
  children=rr[1:];ones=[i for i in children if ev(i)==c(1)];req(len(ones)==1,'predecessor one');pre=next(i for i in children if i not in ones);req(N[pre][0]=='v','predecessor variable');over[pre]=Pred(choose)
  # Rebuild certified division tag with the now interpreted predecessor.
  dc=[r for r in L if r['kind']=='divmod' and r['result'][0]==res];req(len(dc)==1,'factorial quotient')
  ev=evaluator();na,de=map(ev,dc[0]['arguments']);wantnum=A(Pow(A(radius,c(1)),n),Pred(choose));req(na==wantnum and de==choose,'factorial quotient formula');over[res]=Fact(n)
 else:raise ValueError(typ)
 counts[typ]+=1
# Factual arithmetic identities checked with Python arbitrary precision on bounded arguments.
import math
for n in range(9):
 q=2**n+1
 for k in range(12):req((q+1)**n//q**k%q==(math.comb(n,k) if k<=n else 0),'binomial boundary')
 r=(n+2)**(n+2);b=math.comb(r+n,n);req(((r+1)**n+b-1)//b==math.factorial(n),'factorial boundary')
out={'status':'PASS','instances':dict(counts),'scope':'Exact schematic composition of33binomial and3factorial instances through independently audited power/division graphs; small arithmetic boundary controls. Generic unbounded identity proofs are pinned FactorialRepresentation.lean, not inferred from tests.'}
(D/'COMPOSITION_CHECK.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
