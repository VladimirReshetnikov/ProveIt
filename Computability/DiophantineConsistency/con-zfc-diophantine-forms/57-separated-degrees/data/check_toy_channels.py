#!/usr/bin/env python3
"""Independent small-base positive/negative controls for the channel architecture."""
import sys
if sys.flags.optimize:
    raise RuntimeError('Run this exact audit without -O/-OO; assertions are part of the checker.')
import json
from pathlib import Path
count=0; zeros=0; negative=0
for b in (2,4,8,16):
 M=8;B=8192*M*b*b;W=2;Q=8;K=13;E=17
 ell=B+B*B;At=B**4+B**8;N0=B**3;Z=B**14;L=4*b*B**17
 Mc=N0-1-(b-1)*ell;Tc=Mc+N0*(B-2)*At
 for n1 in range(b):
  for n2 in range(b):
   valid=n1*B+n2*B*B
   for corrupt in (0,1,b*B):
    g=valid+corrupt;y=g+ell
    # r1=x1^2-x2, r2=x1-2. Two channels deliberately share exponent 2.
    F=2*B**2*y*y+(-2*B**2+2*B**7)*y-4*B**8+B**9*(y*y+1)
    J=2*F+At;Sc=g+N0*J
    assert F>0 and Sc+Tc<L
    expected=(corrupt==0 and n1==1 and n2==3)
    # The b*B corruption can normalize a valid digit pair into another valid one
    # only through a base-B carry, impossible here since 2b<B.
    assert (Sc&Tc==0)==expected,(b,n1,n2,corrupt,Sc&Tc,expected)
    R=(Sc+Tc)*L+L-1-Sc
    threshold=(L.bit_length()-1)+Tc.bit_count()
    assert (R.bit_count()>=threshold)==expected
    count+=1;zeros+=expected;negative+=corrupt!=0
 for y in (-B**20,-B,-2,-1,0,1,2,B,B**20):
  F=2*B**2*y*y+(-2*B**2+2*B**7)*y-4*B**8+B**9*(y*y+1)
  assert F>0
out={'status':'pass','toy_source':'x1^2=x2, x1=2; pure quadratic and linear channels intentionally collide at exponent2','source_and_carry_cases':count,'positive_zero_cases':zeros,'forbidden_digit_negative_controls':negative,'all_integer_y_positivity_regressions':36,'base_choices':[2,4,8,16]}
Path(__file__).with_name('TOY_CHANNEL_CHECKS.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
