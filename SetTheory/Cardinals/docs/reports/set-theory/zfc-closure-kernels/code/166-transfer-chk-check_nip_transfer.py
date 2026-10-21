"""Owned symbolic stack-contract checker, not a numerical-calculus verifier.

AX axiom outputs are formal tag-0 tokens; their internal formula trees are
irrelevant to these equations. Native I(0,0)=0 and Q tag2 are explicit.
Unknown stack suffixes are never inspected in a claimed strong block.
"""
from dataclasses import dataclass
from pathlib import Path
import json,hashlib
ROOT=Path(__file__).resolve().parents[1];OUT=Path(__file__).resolve().parent
@dataclass(frozen=True)
class Term:
 op:str
 args:tuple=()
def V(x):return Term('variable',(x,))
def I(x,y):return 0 if x==0 and y==0 else Term('I',(x,y))
def Q(i,x):return Term('Q',(i,x))
def add(x,y):return y if x==0 else x if y==0 else x+y if isinstance(x,int)and isinstance(y,int)else Term('+',(x,y))
def tag(x):
 if isinstance(x,int):return x%4
 return 0 if x.op in('I','row','gate')else 2 if x.op=='Q'else None
@dataclass(frozen=True)
class Stack:
 head:object
 tail:object
class Halt(Exception):pass
class NeedDecision(Exception):pass
steps=0

def ax(st,c=0,x=0,y=0):
 t,w,d,h=st;a=add(d,x);b=add(h,y)
 gate=0 if c==a or c==b else Term('gate',(a,b,c))
 rows=[Term('row',(j,a,b,c))for j in range(1,8)]+[Term('row',(8,a,b,c,d)),Q(d,h),t]
 for r in rows[::-1]:w=Stack(r,w)
 return gate,w,0,0

def shift(st):
 t,w,d,h=st
 if h==1:raise Halt()
 # Every symbolic variable in these checks is non-1 unless tested by a
 # separate concrete h=1 case. Formal AX outputs never equal1.
 assert isinstance(w,Stack),('attempt to inspect protected suffix',w)
 return h,w.tail,d,w.head

def mp(st,x):
 t,w,d,h=st;y=add(d,x);target=I(t,y)
 if target==h:return y,Stack(0,w),y,0
 # A mismatch is certified structurally, by disjoint constructor tags,
 # or because a nonzero implication cannot be native0.
 if h==0:
  assert target!=0
 elif tag(h)==2:
  assert tag(target)==0
 else:raise NeedDecision((target,h))
 return 0,w,y,0

def run(st,block):
 global steps
 for k in block:
  steps+=1
  if k[0]=='S':st=shift(st)
  elif k[0]=='M':st=mp(st,k[1])
  else:st=ax(st,*k[1:])
 return st
S=('S',);AX=lambda c=0,x=0,y=0:('A',c,x,y);MP=lambda x:('M',x)
H=[AX()]+[S]*11
PUSH=[AX()]+[S]*9+[MP(0)]
DISCARD=[MP(1),AX(1)]+[S]*10+[MP(0)]
J=lambda u:[]if u==0 else[MP(u)]
records=[]
def check(name,st,block,expected):
 before=steps
 try:
  out=run(st,block);assert out==expected,(name,out,expected)
  records.append(dict(name=name,status='EXACT_RETURN',commands=steps-before))
 except Halt:
  records.append(dict(name=name,status='PERMITTED_EARLY_HALT',commands=steps-before))

w=V('protected arbitrary stack');t=V('arbitrary incoming top');d=V('arbitrary counter');h=V('arbitrary cache');x=V('arbitrary head')
check('H arbitrary', (t,Stack(x,w),d,h),H,(t,w,0,x))
check('H top1',(1,Stack(x,w),d,h),H,None)
check('PUSH arbitrary',(t,w,d,h),PUSH,(0,Stack(t,w),0,0))
check('PUSH cache1',(t,w,d,1),PUSH,(0,Stack(t,w),0,0))
check('PUSH top1',(1,w,d,h),PUSH,(0,Stack(1,w),0,0))
check('DISCARD arbitrary',(t,w,0,0),DISCARD,(0,w,0,0))
for a,b,c in [(2,3,4),(0,0,0),(0,1,0)]:
 for j in range(1,8):
  target=Term('row',(j,a,b,c));B=DISCARD+[AX(c,a,b)]+[S]*(j+1)+H*(9-j)
  check(f'row {j} {a,b,c}',(t,w,0,0),B,(target,w,0,0))
for a,b,c,u in [(0,0,0,0),(2,1,0,0),(2,1,3,1),(2,3,4,2)]:
 target=Term('row',(8,a,b,c,u));B=DISCARD+J(u)+[AX(c,a-u,b)]+[S]*9+H
 check(f'dominated {a,b,c,u}',(t,w,0,0),B,(target,w,0,0))
for a,b,c in [(2,3,4),(0,0,1)]:
 target=Term('gate',(a,b,c));B=DISCARD+[AX(c,a,b)]+H*10
 check(f'bundle {a,b,c}',(t,w,0,0),B,(target,w,0,0))
for i in [0,1,3]:
 for X in [0,1,I(V('p'),V('q')),Q(0,V('p'))]:
  B=PUSH+J(i)+[S,AX(i)]+[S]*10
  check(f'GEN {i} {X}',(X,w,0,0),B,(Q(i,X),w,0,0))
# Test the exact inductive hypotheses as atomic state substitutions:
# major block returns major above w; minor block returns A above [major;w].
for A,B in [(0,0),(0,1),(1,0),(1,1),(V('A'),V('B')),(Q(0,V('x')),I(V('p'),V('q')))]:
 major=I(A,B)
 saved=run((major,w,0,0),PUSH);assert saved==(0,Stack(major,w),0,0)
 minor_state=(A,saved[1],0,0)
 block=PUSH+[S,S,MP(B),AX(B)]+[S]*11
 check(f'MP {A} {B}',minor_state,block,(B,w,0,0))
# Wire encoding uses independent small natural computations and strict pred
# projection, including a sequence of nullary S commands with zero tails.
def P(a,b):return(a+b)*(a+b+1)//2+b
def unP(n):
 s=0
 while(s+1)*(s+2)//2<=n:s+=1
 b=n-s*(s+1)//2;return s-b,b
def fields(k):return[0]if k[0]=='S'else[1,k[1]]if k[0]=='M'else[k[1]+2,k[3],k[2]]
def F(fs,r):
 for a in fs[::-1]:r=P(a,r)
 return r
def tail(L):
 r=0
 for k in L[::-1]:r=1+F(fields(k),r)
 return r
def read(p):
 selector,p=unP(p)
 if selector==0:return S,p
 if selector==1:x,p=unP(p);return MP(x),p
 y,p=unP(p);x,p=unP(p);return AX(selector-2,x,y),p
for L in [[S],[S,S,S],[MP(0),S],[AX(0),S],[AX(1,1,0),MP(0)]]:
 p=tail(L)
 for k in L:
  old=p;actual,p=read(p-1);assert actual==k and p<old
 assert p==0
for Y in range(10):
 R=tail([S]);N=P(2,P(Y,P(1,R)));assert N>=Y
 k,r=read(N);assert k==AX(0,1,Y)and r==R
report=dict(status='PASS',cases=len(records),commands=steps,cases_by_status={s:sum(r['status']==s for r in records)for s in['EXACT_RETURN','PERMITTED_EARLY_HALT']},results=records,scope='Symbolic stack equations and exact finite wire checks corroborate the written all-natural command proof. AX internal axiom formulas are opaque tagged tokens. No binary execution, proof-calculus validation, or complete-tape startup claim.')
(OUT/'NIP_TRANSFER_SYMBOLIC_CHECK.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items()if k!='results'},indent=2))
