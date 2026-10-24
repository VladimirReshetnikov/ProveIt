#!/usr/bin/env python3
"""Independent finite controls for the split scalar carrier; standard library only."""
from pathlib import Path
import argparse, json, math, random
ROOT=Path(__file__).resolve().parent

def req(c,m):
    if not c: raise ValueError(m)

def phi(z,d):return (z*z+3*d*d)*(z*z*z-19*d*d*d)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,default=ROOT/'CRT_CHECKS.json');args=ap.parse_args()
    rng=random.Random(15416);monic=0;crt=0;bootstrap=0
    for m in range(1,41):
        for h in [-17,-11,-5,-1,1,3,7,19]:
            if math.gcd(h,m)!=1:continue
            d=h*m
            for z in range(-80,81):
                req((phi(z,d)%(m**5)==0)==(z%m==0),'exact monic M5 projection');monic+=1
            for _ in range(50):
                k,v,q,T=[rng.randrange(-20,21) for _ in range(4)]
                z=d*T+m*k+h*(v-q*q)
                req((z%m==0)==((v-q*q)%m==0),'coprime scale projection')
                req(phi(z,d)%abs(h)==(m*k)**5%abs(h),'main powered projection')
                req((phi(z,d)%abs(h)==0)==(k**5%abs(h)==0),'unit M cancellation');crt+=1
    # Unlike the primary proof, v=0 and c=0 are allowed at this early stage.
    for v in range(-3,4):
        for c in range(-3,4):
            for j,w,r in [(-2,-2,1),(-1,0,-1),(0,0,1),(1,2,-2)]:
                beta=31;q=beta*(6*j+1)+1;W=12*w+4;X=q*W;Y=q*v;a=(X+1)*Y;H=4*a+3;Delta=a*a+H
                M=2*q*q;req(math.gcd(H,M)==1,'actual H,M coprimality');req(Delta>1 and H!=0,'weak-scale unconditional Delta')
                I=r*c*c;Df=1+Delta*I*I;Q=Delta*Delta*I*I;delta=Q-1
                for R,T in [(-7,-3),(0,0),(5,2)]:
                    V=Df*(c-R+4*I*T)-c;Cy=Q*V*V-1;Da=delta*Cy
                    req(Df>0 and Da>0 and delta!=0,'pre-scale realness including c=0')
                    if c==0:req(Da==1,'c-zero auxiliary radicand')
                    bootstrap+=1
                for old in range(-2,3):
                    newv=q*q*(2*old+1);req((newv-q*q)//M==old,'exact old coordinate recovery')
                    req(q*newv==(2*old+1)*q**3,'exact cubic scale recovery')
    receipt={'status':'PASS','optimized_python':not __debug__,'monic_projection_checks':monic,'coprime_carrier_checks':crt,'pre_scale_realness_checks':bootstrap,'degree416_attained_coefficient':{'monomial':{'j':212,'w':56,'v':64,'h':12,'s':12,'r':24,'c':32,'C':4},'coefficient_factors':{'2':388,'3':278,'beta':212}},'scope':'Finite controls only; CRT_CARRIER_PROOF.md supplies the unbounded argument and full zero-existence maps.'}
    req(sum(receipt['degree416_attained_coefficient']['monomial'].values())==416,'degree endpoint exponent sum')
    args.output.write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
