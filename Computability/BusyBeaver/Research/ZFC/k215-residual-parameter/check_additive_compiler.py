#!/usr/bin/env python3
"""Finite interface checks for root's additive-A/opposite-X compiler extension.
Uses Source164's pure arithmetic/abstract safe-row model, NOT its command step.
HOLE stands for the induction hypothesis; no source/binary emitter is executed.
"""
import argparse,json,sys
from pathlib import Path
from itertools import product
sys.path.insert(0,str(Path(__file__).resolve().parent/'vendor'))
from source164_contract_model import State,pair,unpair,imp,quant,push,rows,bundle
N=('NIP',);D=('DROP',);M=('MP',)
def ax(c,y,x):return ('AX',c,y,x)
def step(command,w,mode):
 t,S,d,h=w.t,w.s,w.d,w.h
 if command==D:return State(h,pair(t,S),d,h)
 if command==N:
  if h==1:return None
  top,rest=unpair(S);return State(t,rest,d,top)
 if command==M:return State(d,pair(0,S),d,0) if imp(t,d)==h else State(0,S,d,0)
 if command[0]=='AX':
  _,c,y,x=command;a=d+x;b=h+y;u=d;assert u<=a
  rr=rows(mode,a,b,c,u)+(quant(u,h),t)
  g=0 if c in (a,b) else bundle(mode,a,b,c)
  return State(g,push(rr,S),max(c-a-1,0),0)
 if command[0]=='HOLE':return State(command[1],S,command[2],0)
 raise AssertionError(command)
def run(commands,w,mode):
 for c in commands:
  w=step(c,w,mode)
  if w is None:return None
 return w
def reset():return ([ax(0,0,0)]+[N]*10)*3
def z():return [ax(0,0,0)]+[N]*10+[D,N]
def setter(v):return z()+[ax(v+1,v+1,0)]+[N]*10+[D,N]
def select(j):return [N]*j+[D]+[N]*(11-j)
def leaf(j,a,b,c,u):
 assert 0<=u<=a and 1<=j<=8
 return reset()+setter(u)+[ax(c,b,a-u)]+select(j)
def bundle_leaf(a,b,c):
 assert c not in (a,b)
 return reset()+[ax(c,b,a)]+[N]*10
def gen(i,p):return p+setter(i)+[D,N,ax(0,0,0)]+select(9)
def mp(b,pa,pab):return pa+[D]+pab+setter(b)+[N,D,N,M,N]
def pack(c,tail):
 if c==N:return pair(0,tail)
 if c==D:return pair(1,tail)
 if c==M:return pair(2,tail)
 _,z,y,x=c;return pair(z+3,pair(y,pair(x,tail)))
def decode(raw):
 tag,tail=unpair(raw)
 if tag<3:return (N,D,M)[tag],tail
 y,tail=unpair(tail);x,tail=unpair(tail);return ax(tag-3,y,x),tail
def cursor(cs):
 n=0
 for c in reversed(cs):n=1+pack(c,n)
 return n
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();assert __debug__
 stacks=(0,pair(1,0),push((7,1,0),0));initial=[State(t,S,d,h) for t,d,h,S in product(range(3),range(3),range(3),stacks)];counts={}
 checks=0
 for mode,w in product(range(3),initial):assert run(reset(),w,mode)==State(0,w.s,0,0);checks+=1
 counts['three_AX_reset_arbitrary_cache']=checks
 for name,block in [('zero_preserving',lambda v:z()),('setter',setter)]:
  checks=0
  for mode,t,d,S,v in product(range(3),range(4),range(3),stacks,range(4)):
   result=run(block(v),State(t,S,d,0),mode);want=0 if name=='zero_preserving' else v
   assert result==(None if t==1 else State(t,S,want,0));checks+=1
  counts[name]=checks
 checks=0
 for mode,w,j,A,U in product(range(3),initial[::10],range(1,9),range(4),range(4)):
  if U>A:continue
  B,C=2,3;got=run(leaf(j,A,B,C,U),w,mode)
  assert got==State(rows(mode,A,B,C,U)[j-1],w.s,max(C-A-1,0),0);checks+=1
 counts['dominated_row_selection']=checks
 checks=0
 for mode,w,ABC in product(range(3),initial[::10],[(0,0,1),(1,2,0),(2,3,1)]):
  A,B,C=ABC;assert run(bundle_leaf(A,B,C),w,mode)==State(bundle(mode,A,B,C),w.s,max(C-A-1,0),0);checks+=1
 counts['bundle_selection']=checks
 checks=0
 for mode,w,H,i,dp in product(range(3),initial[::10],range(4),range(3),range(2)):
  assert run(gen(i,[('HOLE',H,dp)]),w,mode)==(None if H==1 else State(quant(i,H),w.s,0,0));checks+=1
 counts['generalization_additive_A_equals_i']=checks
 checks=0
 for mode,w,A,B,d1,d2 in product(range(3),initial[::10],range(4),range(4),range(2),range(2)):
  assert run(mp(B,[('HOLE',A,d1)],[('HOLE',imp(A,B),d2)]),w,mode)==(None if A==1 else State(B,w.s,B,0));checks+=1
 counts['MP_inductive_compiler']=checks
 checks=0
 for mode,S,d in product(range(3),stacks,range(4)):
  assert run([D,N,N],State(1,S,d,0),mode) is None;checks+=1
 counts['terminal_detection']=checks
 checks=0
 for length in range(1,4):
  for cs in product([M,D,N,ax(0,0,0),ax(1,2,3)],repeat=length):
   n=cursor(cs)
   for c in cs:
    got,rest=decode(n-1);assert got==c and rest<n;n=rest
   assert n==0;checks+=1
 assert cursor([N])==1 and unpair(0)==(0,0)
 counts['command_order210_roundtrip']=checks
 out={'status':'PASS_FINITE_ADDITIVE_X_COMPILER_INTERFACE','tests':counts,'total':sum(counts.values()),'AX':'A=oldD+x,B=oldH+y,U=oldD; d_out=max(C-A-1,0)','wire_order':{'NIP':0,'DROP':1,'MP':2,'AX':'c+3'},'scope':'Finite exact interface tests with3 abstract safe-row instantiations and explicit HOLE induction hypotheses; ordinary proof separate. No literal native AX emitter or machine runtime execution.'}
 a.output.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':main()
