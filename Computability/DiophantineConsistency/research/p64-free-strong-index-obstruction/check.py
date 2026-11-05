#!/usr/bin/env python3
"""Exact partial witness only: does not assert graph zero or Lean result."""
import json
import sys
import math
from pathlib import Path
import hashlib

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('Use python3 -I -S -B without optimization')

beta,J,F,alpha,z,w,s,K0=2,1,1,1,1,1,1,2
eta,zeta=4,4
q=beta*J+1
Y=q**3*s
X=w*q
a=Y*(X+1)
H=4*a+3
delta=a*a+H
k=eta+zeta
c=k*Y+eta
g=24199
f=110
I=12099
U=Y*Y
b0=X+a*c
C=q-F-alpha
if (q,Y,X,a,H,delta,k,c,C,U,b0)!=(3,27,3,108,435,12099,8,220,1,729,23763):
    raise RuntimeError('unexpected coordinate values')
if min(beta,J,F,alpha,z,w,s,K0,eta,zeta,g,f,I)<=0:
    raise RuntimeError('nonpositive input')
if (K0+w)*C-F-z*(q-1)!=0:
    raise RuntimeError('transport equation failed')
if g*g!=1+delta*c*c or I*I!=delta*(f*f-1):
    raise RuntimeError('Pell or strong norm failed')
if I % (c*c) == 0:
    raise RuntimeError('I unexpectedly divisible by c²')
# For any integer D*, M=0 implies D*²=U²g², hence D*=±Ug.
# But D*=U*b0+H*gap for integer gap, so one residue must vanish.
remainders=[U*(sign*g-b0)%H for sign in (1,-1)]
if remainders != [294,132]:
    raise RuntimeError('main-carrier nondivisibility mismatch')
P=X*Y*Y
ell=P*k
radicand=ell*(ell+k)+1
root=math.isqrt(radicand)
if not (root*root<radicand<(root+1)*(root+1)):
    raise RuntimeError('first Pell nonsquare check failed')
result={'status':'PASS_PARTIAL_ONLY','script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
 'transport':0,'c':c,'c_squared':c*c,'independent_I':I,'I_mod_c_squared':I%(c*c),
 'main_residues_mod_H':remainders,'first_norm_radicand':radicand,'first_norm_floor_root':root,
 'scope':'Exact transport and scalar main/strong norms only; M and first residual cannot both be zero for this tuple.'}
print(json.dumps(result,indent=2,sort_keys=True))
