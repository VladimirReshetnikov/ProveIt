#!/usr/bin/env python3
"""Exact free-term PA194DHS command identities, including all halt branches.

Uses inherited free-constructor emitter computation with a new cache-only
Shift evaluator and independently stated command words. Arithmetic assumptions
are Cantor projection identities (including p(0,0)=0), I(0,0)=0, nonzero pair
positivity, and the formula-constructor residues. Ordinary proofs accompany
these executable symbolic checks; no soundness follows from sampling.
"""
from pathlib import Path
import argparse,json
import command_terms as p
ROOT=Path(__file__).resolve().parents[1]
require=p.require

def safe_cache(h,nonone):
 r=p.residue(h)
 return r is not None and r!=1 or h in nonone

def run(word,store,nonone=frozenset()):
 t,w,d,h=store
 for cmd in word:
  if cmd[0]=='S':
   if h==1:return None
   require(safe_cache(h,nonone),'unresolved cache guard')
   newh,neww=p.projections(w);t,w,h=h,neww,newh
  elif cmd[0]=='AX':
   a,x,y=cmd[1:];D,H=p.add(d,x),p.add(h,y)
   for f in reversed(p.source_heads(D,H,a,d,h)+[t]):w=p.pair(f,w)
   t,d,h=('gate',H,D,a),0,0
  elif cmd[0]=='MP':
   b=p.add(d,cmd[1]);test=p.I(t,b)
   if b==0:t,d,h=0,0,0
   elif test==h:t,d,h=b,b,0
   else:
    require(p.definitely_distinct(test,h),'unresolved MP equality')
    t,d,h=0,b,0
  else:raise ValueError(cmd)
 return t,w,d,h

POP=[p.AX(0)]+[p.S]*11
PUSH=[p.AX(0)]+[p.S]*9+[p.MP(0)]
DISCARD=[p.MP(0)]
DETECT=POP

def check():
 if not __debug__:raise RuntimeError('Run verification without Python -O')
 emitter=p.emitter_check()
 t,w,d,h,a,b,A,D,H=map(p.atom,('t','w','d','h','a','b','A','D','H'))
 require(run([p.AX(A)]+[p.S]*9,(t,w,d,h))==(p.I(p.I(p.I(h,d),d),p.I(p.I(d,h),p.I(A,h))),p.pair(t,w),0,p.U(d,h)),'AX S9')
 require(run([p.AX(A)]+[p.S]*10,(t,w,d,h))==(p.U(d,h),w,0,t),'AX S10')
 for stack,expected in [(p.pair(a,w),(t,w,0,a)),(0,(t,0,0,0))]:
  require(run(POP,(t,stack,d,h),frozenset({t}))==expected,'pop nonfalse')
  require(run(POP,(1,stack,d,h)) is None,'pop false halt')
 require(run(PUSH,(t,w,d,h))==(0,p.pair(t,w),0,0),'push')
 require(run(PUSH,(0,0,d,h))==(0,0,0,0),'zero push collapse')
 require(run(DISCARD,(t,w,0,h))==(0,w,0,0),'discard all caches')
 for j in range(1,8):
  word=DISCARD+[p.AX(A,D,H)]+[p.S]*(j+1)+POP*(9-j)
  require(run(word,(t,w,0,0))==(p.source_heads(D,H,A,0,0)[j-1],w,0,0),'head selector')
 require(run(DISCARD+[p.AX(0,b,0)]+[p.S]*2+POP*8,(t,w,0,0))==(p.I(b,p.U(b,b)),w,0,0),'Gamma-D selector')
 require(run(DISCARD+[p.AX(A,D,H)]+POP*10,(t,w,0,0))==(('gate',H,D,A),w,0,0),'gate selector')
 for i in (0,('positive','i')):
  word=PUSH+[p.MP(i),p.S,p.AX(i)]+[p.S]*10
  require(run(word,(a,w,0,0))==(p.U(i,a),w,0,0),'generalization')
  require(run(word,(1,w,0,0))==(p.U(i,1),w,0,0),'generalization of false is total')
  x=p.atom('x');Dvalue=p.add(i,x);rho=p.I(p.I(p.I(H,i),Dvalue),p.I(p.I(Dvalue,H),p.I(A,H)))
  require(run(DISCARD+[p.MP(i),p.AX(A,x,H)]+[p.S]*9+POP,(t,w,0,0))==(rho,w,0,0),'dominated head')
 require(run(DISCARD+PUSH,(t,w,0,0))==(0,p.pair(0,w),0,0),'reserve zero')
 suffix=[p.S,p.S,p.MP(b)]+POP
 premises=(0,p.pair(a,p.pair(p.I(a,b),p.pair(0,w))),0,0)
 require(run(suffix,premises,frozenset({a,b}))==(b,w,0,0),'MP suffix if a,b not false')
 require(run(suffix,(0,p.pair(1,p.pair(p.I(1,b),p.pair(0,w))),0,0)) is None,'false antecedent halt')
 require(run([p.S,p.S,p.MP(1)]+POP,(0,p.pair(a,p.pair(p.I(a,1),p.pair(0,w))),0,0),frozenset({a})) is None,'false conclusion halt in Pop')
 require(run([p.S,p.S,p.MP(0)]+POP,(0,p.pair(0,p.pair(0,0)),0,0))==(0,0,0,0),'truth/empty stack aliases')
 require(run(DETECT,(1,w,d,h)) is None,'unconditional false detector')
 require(run([p.S],(1,0,0,0))==(0,0,0,0),'NS differs from original Shift')
 require(run([p.MP(b)],(a,w,0,p.I(a,b)))==(b,w,b,0),'no push and top-result MP')
 return {'status':'PASS','emitter':emitter,'shift_test':'h=1','MP_success':'(b,w,b,0)','Push_total':True,'Pop_halts_exactly_when_saved_top_is_1':True,'Pop_nonfalse_exact':True,'all_seven_head_selectors':True,'GammaD_selector':True,'dominated_head_selector':True,'gate_selector':True,'generalization_total_including_false':True,'MP_false_antecedent_and_false_conclusion_branches':True,'MP_reserved_zero_consumed':True,'Cantor_zero_and_implication_aliases':True,'all_store_false_detector':'AX(0,0,0); S^11','final_plain_Shift_is_insufficient':True,'symbolic_all_parameters':True,'kernel_checked':False}

if __name__=='__main__':
 parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--output',type=Path);args=parser.parse_args();receipt=check()
 if args.output:args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_text(json.dumps(receipt,indent=2)+'\n')
 print(json.dumps(receipt,indent=2))
