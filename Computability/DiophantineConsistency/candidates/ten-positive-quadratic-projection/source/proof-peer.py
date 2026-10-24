#!/usr/bin/env python3
"""Independent finite controls for the three-root quadratic projection proof.

No candidate producer/verifier or polynomial emitter is imported.
The unbounded argument is in the adjoining peer note, not inferred from tests.
"""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import sys

ROOT=Path(__file__).resolve().parents[1]
CANDIDATE=ROOT/'candidates/ten-positive-quadratic-projection'


def need(ok,message):
    if not ok:raise ValueError(message)


def pell(a,n):
    x,y=1,0
    for _ in range(abs(n)):x,y=a*x+(a*a-1)*y,x+a*y
    return x,y if n>=0 else -y


def add(a,b,scale=1):
    out=dict(a)
    for m,c in b.items():out[m]=out.get(m,0)+scale*c
    return{m:c for m,c in out.items()if c}


def mul(a,b):
    out={}
    for m,c in a.items():
        for n,d in b.items():
            k=tuple(sorted(m+n));out[k]=out.get(k,0)+c*d
    return{m:c for m,c in out.items()if c}


def scale(a,c):return{m:c*d for m,d in a.items()if c*d}


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path);args=ap.parse_args()
    folding=classification=wholeheight=projection=0
    for a in range(3,10):
        for m in range(1,10):
            f,I=pell(a,m)
            need(f>2*I,'strong gap')
            for v in range(-5*m,5*m+1):
                z=pell(a,v)[1];t=v%(2*m);p=t if t<=m else 2*m-t
                need(0<=p<=m,'folded interval')
                need(any((z-e*pell(a,p)[1])%f==0 for e in [-1,1]),'signed folding')
                folding+=1
            S=(a*a-1)*I
            wanted={pell(a,p)[1]for p in range(1,m+1)}
            for v in range(1,16,2):
                xv,y=pell(S,v);need(xv%S==0,'odd auxiliary numerator')
                for V in [xv//S,-xv//S]:
                    c=(-V)%f
                    if 0<c<=I:
                        need(S*S*V*V-(S*S-1)*y*y==1,'auxiliary norm')
                        need(c in wanted,'recovered main psi value')
                        classification+=1
    for q in [32,33,47,64]:
        for X in [q,q+1,2*q]:
            for r in range(30,61):
                R=2*r+1
                need(q**4*2**(2*R+2)*X**2<X**(r+1),'whole-product strict height')
                wholeheight+=1
    # Directly verify both residue projections at small Pell indices.
    for a in range(3,25):
        H=4*a-5
        for R in range(1,16):
            D,c=pell(a,R);e=2**R
            need((D-(a-2)*c-e)%H==0,'minus projection')
            need((e*(D+(a-2)*c)-1)%H==0,'plus projection')
            for X in range(1,12):
                K=X*(X+2*(a-2)*c)-1
                need((e*K-(X-e)*(e*X+1))%H==0,'whole-product congruence')
                projection+=1
    # Exact polynomial reduction: e*K-(X-e)(eX+1)
    # = X*(2*e*u+e^2-1), where u=(A-2)c.
    X={(0,):1};u={(1,):1};e={(2,):1};one={():1}
    K=add(mul(X,add(X,scale(u,2))),one,-1)
    lhs=add(mul(e,K),mul(add(X,e,-1),add(mul(e,X),one)),-1)
    relation=add(add(scale(mul(e,u),2),mul(e,e)),one,-1)
    need(add(lhs,mul(X,relation),-1)=={},'exact projection reduction identity')
    proof=CANDIDATE/'PROOF.md'
    result=dict(status='PASS',optimized_python=bool(sys.flags.optimize),proof_sha256=sha256(proof.read_bytes()).hexdigest(),
                folding_controls=folding,main_recovery_controls=classification,
                strict_whole_product_controls=wholeheight,residue_projection_controls=projection,
                exact_sparse_reduction_identity=True,
                scope='Independent ordinary proof peer and supplementary finite controls only; no candidate circuit/count certification, no Lean, no new native calibration.')
    s=json.dumps(result,indent=2)+'\n'
    if args.output:args.output.write_text(s)
    print(s,end='')


if __name__=='__main__':main()
