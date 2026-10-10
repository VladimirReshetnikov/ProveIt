#!/usr/bin/env python3
"""Numerical diagnostics for identities proved in findings.md.
All values use Mellin-integral representations. These are not proofs.
"""
import json
import argparse
from functools import lru_cache
from pathlib import Path
import mpmath as mp

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output',type=Path,default=Path(__file__).with_name('analytic_identity_checks.json'),
                    help='Destination JSON file (default: beside this script).')
args=parser.parse_args()

mp.mp.dps=90
@lru_cache(None)
def double(a,b,x,y):
    return mp.im(mp.quad(lambda t:(-mp.log(t))**(a-1)*x*mp.polylog(b,x*y*t)/(1-x*t),
                         [0,mp.mpf('.5'),1])/mp.factorial(a-1))

def beta(p):return mp.im(mp.polylog(p,1j))
def eta(p):return mp.log(2) if p==1 else (1-mp.mpf(2)**(1-p))*mp.zeta(p)
def g(a,b):return double(a,b,1j,1)
def S(p):
    return -mp.quad(lambda t:(-mp.log(t))**(p-1)*mp.log(1+t*t)/(1+t*t),
                    [0,mp.mpf('.5'),1])/mp.factorial(p-1)

checks=[]
def check(name,left,right):
    residual=left-right
    assert abs(residual)<mp.mpf('1e-80'),(name,residual)
    checks.append({'name':name,'left':str(left),'right':str(right),'residual':str(residual)})
    print(name,mp.nstr(residual,10),flush=True)

for p in [1,2,4,5]:
    check(f'K_A_identity_p_{p}',double(p,1,1j,-1)+(-1)**(p-1)*double(1,p,1j,1j),
          beta(p+1)-2*mp.log(2)*beta(p)+sum((-1)**j*eta(j)*beta(p+1-j) for j in range(2,p+1)))
check('g_weight_5_shuffle_23',g(2,3)+3*g(3,2)+6*g(4,1),
      -3*mp.catalan*mp.zeta(3)/32-mp.pi**5/1536)
check('g_weight_5_shuffle_14',g(1,4)+g(2,3)+g(3,2)+2*g(4,1),
      -beta(4)*mp.log(2)/2-7*mp.pi**5/46080)
check('S4_original_candidate',S(4),(4*g(4,1)-3*g(3,2)-9*g(2,3))/7
      +mp.pi**5/224-27*mp.catalan*mp.zeta(3)/224-2*beta(4)*mp.log(2))
check('S4_simplified_candidate',S(4),(10*g(4,1)-8*g(2,3))/7
      +7*mp.pi**5/1536-3*mp.catalan*mp.zeta(3)/28-2*beta(4)*mp.log(2))
check('S4_A14_equivalent_candidate',161280*double(1,4,1j,1j)+69120*(g(4,1)+g(3,2)+3*g(2,3))
      +617*mp.pi**5-101520*mp.catalan*mp.zeta(3),mp.mpf(0))
check('Gaussian_inverse_weight_6_closed',double(5,1,1j,-1j),
      3*beta(6)-mp.pi**2*beta(4)/6-mp.pi**4*mp.catalan/90-5*mp.pi**5*mp.log(2)/3072)
rho=mp.exp(2j*mp.pi/3)
check('Eisenstein_inverse_weight_6_g_coordinates',double(5,1,rho,1/rho),
      sum(double(a,6-a,rho,1) for a in range(1,6))
      +5*mp.im(mp.polylog(6,rho))-mp.pi**2*mp.im(mp.polylog(4,rho))/6
      -mp.pi**4*mp.im(mp.polylog(2,rho))/90-2*mp.pi**3*mp.zeta(3)/81-mp.pi*mp.zeta(5)/6)
args.output.parent.mkdir(parents=True,exist_ok=True)
args.output.write_text(json.dumps({
    'status':'Numerical diagnostics; S4 remains a conjecture',
    'precision':mp.mp.dps,'mpmath_version':mp.__version__,'checks':checks},indent=2)+'\n')
print(args.output)
