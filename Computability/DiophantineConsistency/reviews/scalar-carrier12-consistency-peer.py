#!/usr/bin/env python3
"""Independent finite arithmetic controls for the scalar12 ordinary proof.

No candidate generator, norm emitter, proof assistant or native calibration code.
These diagnostics supplement the unbounded peer argument in the companion note.
"""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import sys

ROOT=Path(__file__).resolve().parents[1]
CANDIDATE=ROOT/'candidates/scalar-carrier12'
def need(p,s):
 if not p:raise ValueError(s)
def psi(A,n,mod=None):
 a,b=0,1
 for _ in range(n):a,b=b,(2*A*b-a)if mod is None else(2*A*b-a)%mod
 return a

def cheb_quotient(h,x,mod=None):
 a,b=1,4*x-3
 if h==0:return a
 for _ in range(1,h):a,b=b,(4*x-2)*b-a
 # Reduce each step as well in real-sized uses; the test bounds here are small.
 return b if mod is None else b%mod

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
 odd=0
 for A in range(3,12):
  for h in range(15):
   need(cheb_quotient(h,1-A*A)==(-1)**h*psi(A,2*h+1),'exact odd-index identity')
   need(cheb_quotient(h,0)==(-1)**h*(2*h+1),'constant term for signed auxiliary index');odd+=1
 monic=0
 for H in list(range(-12,0))+list(range(1,13)):
  for z in range(-80,81):
   phi=(z*z+3*H*H)*(z**3-19*H**3)
   need(phi!=0,'nonzero scalar carrier control')
   if phi%(H**5)==0:need(z%H==0,'monic homogeneous valuation conclusion')
   monic+=1
 roots=[]
 for m in range(1,201):
  r=next((x for x in range(m)if((x*x+3)*(x**3-19))%m==0),None)
  need(r is not None,'intersective finite modulus control');roots.append(r)
 rank=0;nontrivial=0
 for A in range(3,8):
  values=[psi(A,m)for m in range(81)]
  for p in range(1,6):
   c=values[p]
   for m in range(1,81):
    if values[m]%(c*c)==0:
     need(m%p==0 and m%c==0,'squared-ordinate rank conclusion');rank+=1;nontrivial+=int(c>1)
 def pin(n):return sha256((CANDIDATE/n).read_bytes()).hexdigest()
 result=dict(status='PASS',optimized_python=bool(sys.flags.optimize),
             source_pins={n:pin(n)for n in ['PROOF.md','SOURCE_PINS.json','source/INTERPOLATION12.md','source/signed-quadratic-proof.md','source/RESIDUE_AND_DETERMINANT.md','rational.json','integral.json']},
             controls=dict(exact_odd_index_and_constant_term_cases=odd,homogeneous_scalar_cases=monic,
                           intersective_moduli=200,squared_ordinate_rank_cases=rank,nontrivial_rank_cases=nontrivial),
             scope='Independent arithmetic controls and ordinary proof chronology review only. No circuit/count/degree replay or new calibration is claimed by this supplementary peer.')
 raw=json.dumps(result,indent=2,sort_keys=True)+'\n';args.output.write_text(raw);print(raw,end='')
if __name__=='__main__':main()
