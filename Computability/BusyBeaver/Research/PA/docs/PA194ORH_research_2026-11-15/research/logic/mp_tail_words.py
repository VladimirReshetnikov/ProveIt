#!/usr/bin/env python3
"""Universal free-term command identities for DD, HD, DH and direct SP protocols.
Uses only Cantor projection/zero aliases, constructor residues, and positivity.
The source binding and literal Turing-table simulation are separate obligations.
"""
from pathlib import Path
import sys,json,importlib.util
ROOT=Path(__file__).resolve().parent
REF=ROOT/'reference/ax11_commands.py'
spec=importlib.util.spec_from_file_location('term_model',REF)
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
I,U,pair,projections,add,atom,req=m.I,m.U,m.pair,m.projections,m.add,m.atom,m.require
S=('S',)
def AX(c,x=0,y=0):return('AX',c,x,y)
def MP(x):return('MP',x)
PUSH=[AX(0)]+[S]*9+[MP(0)]
POP=[AX(0)]+[S]*11
ERASE=PUSH+POP+PUSH+POP

def run(words,store,family,known=frozenset()):
 t,w,d,h=store
 for cmd in words:
  if cmd[0]=='S':
   if m.sum_one(t,h,known):return None
   nh,nw=projections(w);t,w,h=h,nw,nh
  elif cmd[0]=='AX':
   c,x,y=cmd[1:];qs=m.heads(add(d,x),add(h,y),c,d,h)
   for a in reversed(qs[1:]+[t]):w=pair(a,w)
   t,d,h=qs[0],0,0
  elif cmd[0]=='MP':
   b=add(d,cmd[1]);major=I(t,b)
   if major==h:
    if family=='DD':t,w=b,pair(b,pair(0,w))
    elif family=='HD':t,w=b,pair(0,pair(0,w))
    elif family=='DH':t,w=0,pair(b,pair(0,w))
    elif family=='SP':t,w=0,pair(b,w)
    else:raise AssertionError(family)
   else:
    req(m.distinct(major,h),'undecided MP branch');t=0
   d,h=b,0
  else:raise AssertionError(cmd)
 return(t,w,d,h)

def check(family):
 t,w,d,h,a,b=map(atom,('t','w','d','h','a','b'))
 req(run(PUSH,(t,w,d,h),family)==(0,pair(t,w),0,0),'Push')
 req(run(POP,(t,pair(a,w),d,h),family)==(t,w,0,a),'Pop')
 req(run(POP,(1,pair(a,w),d,h),family)==(1,w,0,a),'Pop at contradiction')
 req(run(POP,(t,0,d,h),family)==(t,0,0,0),'Pop zero alias')
 req(run(ERASE,(t,w,d,h),family)==(0,w,0,0),'universal Erase')
 req(run(ERASE,(1,0,d,1),family)==(0,0,0,0),'Erase handles two contradictions')
 for z in [0,('positive','z')]:
  off=[]if z==0 else[MP(z)]
  req(run(off,(0,w,0,0),family)==(0,w,z,0),'Offset')
 # A genuine successful MP is given its matching major premise. Cleanup
 # preserves arbitrary carried stack w and every conclusion, including0and1.
 for b0 in ([] if family=='SP' else [0,1,b]):
  tail=POP*2 if family in['DD','HD']else POP+[S]
  out=run([MP(b0)]+tail,(a,w,0,I(a,b0)),family,frozenset({b}) if b0==b else frozenset())
  req(out==((b0,w,0,0)if family!='DH'or b0!=1 else None),'successful MP normalization')
 req(run([MP(0)],(0,0,0,0),family)==(0,0,0,0),'all-zero Cantor alias')
 # Sourceproof compiler creates a stack[a,I(a,b),0;w], then selects both.
 # The reserved zero beneath them is removed by one final Pop.
 for b0 in[0,1,b]:
  tail=POP*3 if family in['DD','HD']else POP+[S]+(POP if family=='DH' else [])
  out=run([S,S,MP(b0)]+tail,(0,pair(a,pair(I(a,b0),pair(0,w))),0,0),family,frozenset({a,b}) if b0==b else frozenset({a}))
  req(out==((b0,w,0,0)if family in['DD','HD']or b0!=1 else None),'composed MP compiler suffix')
 # Ordinary axiom selectors and theorem-only GEN use no successful MP.
 A,D,H=map(atom,('A','D','H'))
 for j in range(10):
  select=POP*10 if j==0 else [S]*(j+1)+POP*(9-j)
  req(run(ERASE+[AX(A,D,H)]+select,(t,w,d,h),family)==
      (m.heads(D,H,A,0,0)[j],w,0,0),'axiom selector'+str(j))
 for i in [0,('positive','i')]:
  off=[]if i==0 else[MP(i)]
  req(run(PUSH+off+[S,AX(i)]+[S]*10,(a,w,0,0),family)==
      (U(i,a),w,0,0),'generalization')
  xx=atom('x');dv=add(i,xx)
  expected=I(I(I(H,i),dv),I(I(dv,H),I(A,H)))
  req(run(ERASE+off+[AX(A,xx,H)]+[S]*9+POP,(t,w,d,h),family)==
      (expected,w,0,0),'dominated rho')
 return dict(family=family,status='PASS',push_shifts=9,pop_shifts=11,
  erase='Push;Pop;Push;Pop',offset_zero='empty word',
  mp_cleanup='Pop^2'if family in['DD','HD']else'Pop;Shift',
  mp_suffix_uses_reserved_zero=True,axiom_selectors=10,generalization=True,dominated_rho=True,
  cleanup_scope='arbitrary carried stack'if family!='SP'else'reserved-zero compiler suffix only',
  final_refutation='Shift'if family in['DD','HD']else'cleanup itself may halt')
if __name__=='__main__':
 out=dict(status='PASS',scope='Universal symbolic command identities, separate from source and physical machine correctness',results=[check(f)for f in['DD','HD','DH','SP']])
 (ROOT/'mp_tail_words_receipt.json').write_text(json.dumps(out,indent=2)+'\n')
 print(json.dumps(out,indent=2))
