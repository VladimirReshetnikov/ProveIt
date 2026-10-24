#!/usr/bin/env python3
"""Independent exact arithmetic diagnostics for the zero-offset ordinary peer.

No literal producer, author checker, archived emitter or Lean is imported.
"""
import argparse
from fractions import Fraction
from hashlib import sha256
import importlib.util
import json
from math import gcd
from pathlib import Path
import sys

ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('independent_poly',ROOT/'reviews/main-root-modulus-signs-peer.py')
p=importlib.util.module_from_spec(spec);spec.loader.exec_module(p)
def need(ok,message):
    if not ok:raise ValueError(message)
def pell(a,n):
    x,y=1,0
    for _ in range(n):x,y=a*x+(a*a-1)*y,x+a*y
    return x,y
def sha(path):return sha256(path.read_bytes()).hexdigest()

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
    proof=ROOT/'research/ten-positive-zero-offset/PROOF.md'
    candidate=ROOT/'candidates/ten-positive-zero-offset/PROOF.md'
    need(sha(proof)=='8555e4f3cb78aba44e091e35d61b08a26f63f638b60d3d1795d3395680eff6f9'and proof.read_bytes()==candidate.read_bytes(),'exact final ordinary proof and copied candidate')
    C,V,add,mul=p.C,p.V,p.plus,p.times
    X,Y,L=[V(i)for i in range(3)];one=C(1);a=mul(Y,add(X,one));A=add(mul(L,a),one)
    P=add(p.product([C(2),X,mul(L,L),mul(Y,Y)]),one)
    left=add(mul(mul(add(mul(C(2),A),C(-1)),add(mul(C(2),A),C(-1))),X),mul(mul(add(X,one),add(X,one)),mul(C(2),P)),-1)
    right=add(add(p.product([C(4),L,a,X]),X),mul(C(2),mul(add(X,one),add(X,one))),-1)
    need(left==right,'full free-ring lower ratio identity')
    need(mul(L,add(mul(X,Y),Y))==mul(mul(L,Y),add(X,one)),'full shared scaled-base identity')
    ratios=0
    for x in(32,33,64,256):
        for y in(1,2,3):
            for lam in(1,2,5,1025):
                aa=y*(x+1);aaP=lam*aa+1;pp=2*x*lam*lam*y*y+1
                for r in(1,2,3,4):
                    ratio=Fraction(pell(aaP,2*r+1)[1],pell(pp,r+1)[1]);xi=Fraction((x+1)**(2*r),x**r)
                    need(xi<ratio<xi*Fraction(aa+1,aa)**(2*r),'exact new ratio inequalities, no floating arithmetic');ratios+=1
    bounds=0
    for q in range(32,41):
        mu=q*q+1
        for w in(1,2,3):
            for y in(1,2,3,4):
                x=w*q;aa=y*(x+1);aaP=mu*aa+1;H=4*aaP-5;delta=aaP*aaP-1;v0=x*mu*mu*y*y
                need(aaP>4 and aaP>y and H>3*aa>x and delta>v0+1 and 2*v0+1>aaP,'all changed unconditional/first-index bounds');bounds+=1
    coprime=0
    for q in range(32,101,2):
        mu=q*q+1
        for w in(1,2):
            for y in(1,2):
                aa=y*(w*q+1);H=4*mu*aa-1
                need(gcd(mu*mu,q**3*(q-1)*H)==1,'post-parity unchanged denominator license');coprime+=1
    q=33;mu=q*q+1;H=4*mu*(q+1)-1
    need(gcd(mu*mu,q**3*(q-1)*H)>1,'odd-q control forbids premature coprimality')
    intervals=0
    for R in(7,11,15):
        r=(R-1)//2;x=2**R;M=((x+1)**(2*r))//(x**r)
        need(M%2==0,'half-quotient toy interval is integral')
        y=M//2
        for mu in(1025,4097,16385):
            aa=mu*y*(x+1)+1;pp=2*x*mu*mu*y*y+1;c=pell(aa,R)[1];k=2*pell(pp,r+1)[1]
            need(k*y<c<k*(y+1),'fresh-ratio eta/zeta interval diagnostics');intervals+=1
    auxiliary=0
    for aa in(2,3,4,5):
        R=3;c=pell(aa,R)[1];D=pell(aa,R)[0];f,I=pell(aa,R*c);delta=aa*aa-1
        need(I==c*pell(D,c)[1]and I%(c*c)==0 and I>=c*c and f*f-delta*I*I==1,'universal fresh strong composition/divisibility')
        S=delta*I;chi,y=pell(S,R)
        need(chi%S==0,'odd auxiliary coordinate integral')
        v=chi//S;numerator=v+c+R*f*f
        need(numerator%(c*f*f)==0,'exact simultaneous auxiliary congruences')
        T=numerator//(c*f*f)
        need(T>0 and v==f*f*(c*T-R)-c and y>v and S*S*v*v-(S*S-1)*y*y==1,'fresh auxiliary completeness diagnostics');auxiliary+=1
    paths=[proof,candidate,ROOT/'candidates/ten-positive-short-projection/PROOF.md',ROOT/'candidates/ten-positive-free-j/source/ORIGINAL_PROOF.md',ROOT/'candidates/ten-positive-free-j/source/SOURCE61.tex',Path(__file__)]
    result={'status':'PASS','optimized_python':bool(sys.flags.optimize),
      'source_pins':{str(f.relative_to(ROOT)):sha(f)for f in paths},
      'exact_free_ring_identities':2,'exact_fraction_ratio_cases':ratios,'changed_unconditional_bounds':bounds,
      'post_parity_coprimality_controls':coprime,'odd_q_coprimality_counterexample':33,
      'toy_half_quotient_ratio_intervals':intervals,'universal_smallindex_strong_auxiliary_controls':auxiliary,
      'ordinary_findings':['all soundness licenses survive with A=mu*a+1','new direct P4 ratio replaces the offset-specific L4 use','fresh c/k interval precedes candidate zero construction','fresh psi_A(Rc) is divisible by c squared','auxiliary Tstar growth exceeds alpha for the actual canonical r>=48','kappa<Xc<f and tau>k>Y give positive n even at transport t=0','unscaled source restoration uses fresh parameter a+2 independently of present A'],
      'reported_target':{'strictly_positive_variables':10,'operations':99,'exact_degree':368,'literal_count_and_payloads_not_attested_by_this_peer':True},
      'scope':'Independent complete ordinary chronology/witness review with exact scalar diagnostics. Full literal graph/count/degree/payload replay is separate author/root scope. Toy interval/auxiliary examples are not full calibrated input tuples. No Lean or historical emitter invoked.'}
    args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n');print(json.dumps(result,indent=2))

if __name__=='__main__':main()
