#!/usr/bin/env python3
"""Exact small identities and negative controls; not unbounded semantic proofs."""
import itertools
import json
import math
import sys
from fractions import Fraction
from pathlib import Path
from exact_ring import Ring, equal, require

ROOT=Path(__file__).resolve().parent
r=Ring(['Q','V','y']);Q,V,y=(r.var(n) for n in r.names)
Vp=(2*Q-1)*V-2*(Q-1)*y; yp=(2*Q-1)*y-2*Q*V
equal(Q*Vp**2-(Q-1)*yp**2,Q*V**2-(Q-1)*y**2,'Pell descent preserves norm exactly')

roots=0; steps=0
for Q in range(2,121):
    for V in range(1,121):
        rat=Fraction(Q*V*V-1,Q-1)
        a,b=math.isqrt(rat.numerator),math.isqrt(rat.denominator)
        if a*a==rat.numerator and b*b==rat.denominator:
            roots+=1; yy=Fraction(a,b)
            require(yy.denominator==1,'Bounded rational root integrality')
            if V>1:
                vp=(2*Q-1)*V-2*(Q-1)*yy
                yprime=(2*Q-1)*yy-2*Q*V
                require(vp.denominator==1 and 0<abs(vp)<V,'Strict descent')
                require(Q*vp*vp-(Q-1)*yprime*yprime==1,'Numeric norm preservation')
                steps+=1

branch_tests=0
for q,d,F,K,X in itertools.product(range(2,35),range(0,16),range(1,20),(1,3),(1,7)):
    alpha=q-F+d
    if alpha<1:continue
    mask=2*q*q-1
    R=(q*(q-F)+d)*(q*q-1)+mask
    B=(q*K+X)*d+q*F
    require(q*B>=q*q*d+q*q*F,'Lower transport magnitude')
    require(R<q*B+q**4+q*q,'Exceptional negative-C upper bound')
    branch_tests+=1

# The full signed-sum hypothesis that suffices for three roots fails for four.
# Radicands2,8,18,10000 have roots1,2,3 times sqrt2 and100.
four_full=[]
for signs in itertools.product((-1,1),repeat=4):
    irrational_coefficient=signs[0]+2*signs[1]+3*signs[2]
    rational_part=100*signs[3]
    require(2*irrational_coefficient**2!=rational_part**2,'No full signed sum vanishes')
    four_full.append([list(signs),irrational_coefficient,rational_part])
require(1+2-3==0,'Three irrational terms cancel')

q=32;Y=q**3;X=192;H=4*Y*(X+1)+3;Bt=(q+X)-q
require(H==25296899 and H%(q-1)==0,'Residue control H')
require(Bt==192 and Bt%(q-1)!=0 and (H*Bt)%(q-1)==0,'Failed cancellation control')

result={'status':'passed','scope':'Exact symbolic descent identity and bounded arithmetic checks; no finite test is an unbounded proof.',
  'python_optimization':sys.flags.optimize,'bounded_rational_pell_roots':roots,
  'bounded_strict_descent_steps':steps,'negative_C_bound_checks':branch_tests,
  'four_root_counterexample':{'radicands':[2,8,18,10000],'signed_sum':100,'signs':[1,1,-1,1],
    'all_16_full_signed_sums_nonzero':True},
  'residue_counterexample':{'q':q,'Y':Y,'X':X,'H':H,'Bt':Bt,'Bt_remainder':Bt%(q-1)}}
path=ROOT/('NEW_LEMMA_CHECKS_OPTIMIZED.json' if sys.flags.optimize else 'NEW_LEMMA_CHECKS.json')
path.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
