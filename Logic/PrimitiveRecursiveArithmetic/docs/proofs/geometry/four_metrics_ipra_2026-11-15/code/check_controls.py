#!/usr/bin/env python3
"""Negative controls for the finite localized-ring arithmetic and rejection."""
import json
from pathlib import Path
import verify_stdlib as k

r,x,a,m,q = [k.Rat(p) for p in (k.P_R,k.P_X,k.P_A,k.P_M,k.P_Q)]
S,D,s = k.Rat(k.P_S),k.Rat(k.P_D),k.Rat(k.P_s)
iS,iD,is_ = k.Rat(1,(0,1,0,0)),k.Rat(1,(0,0,1,0)),k.Rat(1,(0,0,0,1))
k.check('basic_denominator_cancellation',[S*iS-1,D*iD-1,s*is_-1])
k.check('quotient_rule',[iS.diff(1)+2*r*iS*iS,iS.diff(2)+2*a*a*x*iS*iS])
bad = {
  'one_is_not_zero':k.Rat(1),
  'charge_is_not_zero':q*q,
  'wrong_Ricci_tt_sign':2*q*q*(D+a*a*s)*iS**3,
  'wrong_Maxwell_normalization':q*q*iS**2,
}
rejected=[]
for name,value in bad.items():
    try: k.check(name,[value])
    except ValueError: rejected.append(name)
    else: raise RuntimeError(f'Negative control {name} was falsely accepted')
out={'status':'PASS','negative_controls_rejected':rejected,'positive_controls':5,
     'note':'These are deliberately nonzero symbolic polynomials, not physical counterexamples.'}
dest=Path(__file__).resolve().parents[1]/'certificates'/'negative_controls.json'
dest.write_text(json.dumps(out,indent=2)+'\n')
print(f'PASS: all {len(rejected)} nonzero residuals rejected')
