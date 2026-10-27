#!/usr/bin/env python3
"""Fixed intermediate-degree corollary; authored code only, no archive execution."""
from fractions import Fraction as F
import json
from verify_rectangular_tree import I, constants, sq, require

beta2=F(27980397750833,82810000000000)
alpha2=F(24,169)
f0=F(33,500)
A=F(119,1000)
theta=F(24,125)
f1=F(5353,125000)
rho=F(2,13)
degree=F(51,100)

require(f1==(A-f0)*(1-theta),'tail capacity identity failed')
require(f0+f1/(1-theta)==A,'total taper capacity failed')
require(13**66<2**245,'root symmetric degree gate failed')
require(13**119<2**490,'retained-side gate failed')
require(338**119<2**1000,'fresh-side and rounding gates failed')
require(A<degree,'fresh packet degree exceeds cap')
require(rho<F(1,6)<theta,'depth/taper bootstrap failed')

kappa=constants();beta=sq(beta2);alpha=sq(alpha2)
rootK=kappa/sq(f0);childK=kappa*rho/sq(f1)
gamma=I(rho)/sq(theta)
one_minus_gamma=I(1-gamma.hi,1-gamma.lo)
tail_cache=alpha/one_minus_gamma
require(tail_cache.hi<beta.lo,'tail paid-cache term not below local aggregation')
root=beta*rootK
descendant=alpha*rootK+beta*childK
require(descendant.hi<root.lo,'root is not time-dominant')
require(childK.hi<rootK.lo,'root is not space-dominant')
require(root.hi<F(14503,1000),'safe eventual coefficient 14.503 failed')
require(root.lo>F(14502,1000),'incorrect lower bound')
require(beta2/f0==F(27980397750833,5465460000000),'closed radical mismatch')

# Negative controls: raising the root taper to .067 fails its claimed gate;
# raising total taper to .120 fails the packet-rounding gate.
require(not(13**67<2**245),'root counterexample not detected')
require(not(338**120<2**1000),'capacity counterexample not detected')

result={
'scope':'Degree <= ceil(s^(51/100)); other normalized oracle/ring/precision premises unchanged. Arithmetic certificate, not new verification of inherited identities.',
'r':13,'beta_squared':str(beta2),'f0':str(f0),'A':str(A),'theta':str(theta),'f1':str(f1),'child_mass_ratio':str(rho),
'root_time_and_space':root.decimal_enclosure(),
'descendant_time':descendant.decimal_enclosure(),
'geometric_K_ratio':gamma.decimal_enclosure(),
'paid_tail_coefficient':tail_cache.decimal_enclosure(),
'local_coefficient':beta.decimal_enclosure(),
'safe_eventual_time_and_space':'14.503',
'exact_final_constant':'(pi/ln(2))*sqrt(27980397750833/2732730000000)',
'negative_controls':2,
}
print(json.dumps(result,indent=2,sort_keys=True))
