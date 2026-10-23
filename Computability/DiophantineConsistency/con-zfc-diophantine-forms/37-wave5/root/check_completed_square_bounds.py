"""Independent checks of two new signed majorants; not a proof of equivalence."""
from pathlib import Path
import json, random
import sympy as s
R,sigma,r,j=s.symbols('R sigma r j', integer=True)
A=R*sigma;C=2*R+1+r;H=(j+1)*C-r
MD=A*C+sigma*(r+1)**2+1
MH=C*H+r*r
assert s.expand(MD-A*C-1-sigma*(r+1)**2)==0
assert s.expand(4*(MD+A*C-1)-sigma*((4*R+r+1)**2+3*(r+1)**2))==0
assert s.expand(MH-C*H)==r*r
assert s.expand(2*(MH+C*H)-(2*C-r)**2-(4*j*C*C+r*r))==0
rng=random.Random(492710);n=0
for R0 in list(range(-20,21))+[rng.randrange(-100000,100000) for _ in range(800)]:
 for sig0,r0,j0 in [(1,0,1),(1,1,1),(2,17,2),(rng.randrange(1,100),rng.randrange(1000),rng.randrange(1,100))]:
  aa=R0*sig0;cc=2*R0+1+r0;hh=(j0+1)*cc-r0
  md=aa*cc+sig0*(r0+1)**2+1;mh=cc*hh+r0*r0
  dd=(aa*aa-1)*cc*cc+1
  assert md>0 and md>abs(aa*cc) and md*md>abs(dd)
  assert mh>=abs(cc*hh)
  n+=1
out={'status':'PASS','symbolic_identities':4,'signed_fixtures':n,'zero_R_explicitly_checked':True,'scope':'Majorant identities and finite checks only; proof in report.'}
Path(__file__).with_name('COMPLETED_SQUARE_CHECKS.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
