"""Finite critical coefficient algorithm from article Sections 6 and 7.

Pure Python exact rational Laurent arithmetic. This is a reference implementation,
not an optimized large-order package. Example:
  python3 code/general_coefficients.py --ell 3 --order 3 --sign 1
The default regression checks cubic and quartic coefficients and the first prime/composite-length corrections.
"""
from fractions import Fraction as F
from math import factorial, comb, gcd
from itertools import product
import argparse,json
from pathlib import Path

# Laurent polynomials in lambda: {exponent: rational coefficient}.
def add(out,p,scale=F(1),shift=0):
    for e,a in p.items():
        out[e+shift]=out.get(e+shift,F(0))+scale*a
        if not out[e+shift]:del out[e+shift]
    return out

def phi(d):return sum(gcd(i,d)==1 for i in range(1,d+1))

def multiply(p,terms,K):
    # h series with Laurent coefficients, indexed by (h degree, lambda degree).
    out={}
    for (i,e),a in p.items():
        for j,f,b in terms:
            if i+j<=K:
                key=(i+j,e+f);out[key]=out.get(key,F(0))+a*b
    return {k:v for k,v in out.items() if v}

def factor_coefficient(ell,J,blocks,k):
    p={(0,0):F(1)};v=len(blocks)
    for i in range(v):
        if i:p=multiply(p,[(0,0,F(1)),(2,0,F(-i))],k)
    for w in blocks:
        for i in range(1,w):p=multiply(p,[(0,0,F(1)),(ell-2,-1,F(-i))],k)
    for i in range(1,J):p=multiply(p,[(0,0,F(1)),(ell,-1,F(-ell*i))],k)
    for i in range(1,ell*J):
        p=multiply(p,[(ell*a,-a,F(i**a)) for a in range(k//ell+1)],k)
    return {e:a for (h,e),a in p.items() if h==k}

def partitions_with_deficit(slots,D):
    # Restricted-growth construction: each distinguishable slot joins an existing
    # block or creates the next block. Every set partition occurs exactly once.
    blocks=[]
    def rec(i,delta):
        if i==len(slots):
            yield tuple(blocks),delta;return
        w=slots[i]
        blocks.append(w)
        yield from rec(i+1,delta)
        blocks.pop()
        if delta<D:
            for j in range(len(blocks)):
                blocks[j]+=w
                yield from rec(i+1,delta+1)
                blocks[j]-=w
    yield from rec(0,0)

def positive_vectors(ell,K,s):
    modes=[]
    for d in range(1,ell+1):
        if ell%d:continue
        for j in range(1,(K+2*ell//d)//ell+1):
            grade=ell*j-2*ell//d
            if grade>0:
                modes.append((grade,j,ell//d,j*d,F(s**(j-1)*phi(d),ell*j)))
    def rec(i,remaining,W,J,slots,alpha):
        if i==len(modes):
            yield W,J,slots,alpha;return
        g,j,m,t,a=modes[i]
        for q in range(remaining//g+1):
            yield from rec(i+1,remaining-q*g,W+q*g,J+q*j,
                           slots+(t,)*(m*q),alpha*a**q/factorial(q))
    yield from rec(0,K,0,0,(),F(1))

def E(ell,k,s,b,c,vectors):
    out={};base=(2,)*(ell*b+(ell//2*c if ell%2==0 else 0))
    for W,J0,slots,alpha in vectors:
        for blocks,delta in partitions_with_deficit(base+slots,(k-W)//2):
            residual=k-W-2*delta
            coef=factor_coefficient(ell,2*b+c+J0,blocks,residual)
            add(out,coef,alpha,J0)
    return out

def critical_coefficient(ell,k,s):
    assert ell>=3 and k>=0 and s in [-1,1]
    even=ell%2==0;vectors=list(positive_vectors(ell,k,s));values={}
    for b in range(k+1):
        for c in range(k-b+1 if even else 1):values[b,c]=E(ell,k,s,b,c,vectors)
    out={}
    for i in range(k+1):
        for j in range(k-i+1 if even else 1):
            diff={}
            for b in range(i+1):
                for c in range(j+1):
                    add(diff,values[b,c],F((-1)**(i+j-b-c)*comb(i,b)*comb(j,c)))
            scale=F(s,2*ell)**i/F(factorial(i))*F(1,ell)**j/F(factorial(j))
            add(out,diff,scale,2*i+j)
    return out

def show(p):return {str(k):str(v) for k,v in sorted(p.items())}

def regression():
    expected={
      (3,0,1):{0:F(1)},(3,0,-1):{0:F(1)},
      (3,1,1):{1:F(1,6)},(3,1,-1):{1:F(7,6)},
      (3,2,1):{2:F(1,72),0:F(-3,2)},(3,2,-1):{2:F(49,72),0:F(-5,2)},
      (3,3,1):{-1:F(7,6),1:F(-1,4),3:F(-71,1296)},
      (3,3,-1):{-1:F(3,2),1:F(-35,12),3:F(271,1296)},
      (4,1,1):{},(4,1,-1):{},(4,2,1):{0:F(-1,2)},(4,2,-1):{1:F(1),0:F(-1,2)},
      (5,1,1):{},(5,2,1):{},(5,3,1):{1:F(3,10)},
      (5,1,-1):{},(5,2,-1):{},(5,3,-1):{1:F(13,10)},
      (6,1,1):{},(6,2,1):{1:F(1,3)},(6,1,-1):{},(6,2,-1):{1:F(1,3)}
    }
    out={}
    for key,want in expected.items():
        got=critical_coefficient(*key);assert got==want,(key,got,want)
        out[str(key)]=show(got)
    return out

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--ell',type=int);ap.add_argument('--order',type=int,default=3);ap.add_argument('--sign',type=int,choices=[-1,1],default=1);args=ap.parse_args()
    if args.ell is None:
        out={'scope':'Exact finite algorithm regressions; not a proof of uniform remainders. Laurent polynomial maps use lambda exponents as keys.','coefficients':regression()}
        (Path(__file__).resolve().parents[1]/'results/general-algorithm-results.json').write_text(json.dumps(out,indent=2)+'\n')
        print('PASS: finite general-length coefficient algorithm matches cubic, quartic, prime-length and composite-length targets')
    else:print(json.dumps(show(critical_coefficient(args.ell,args.order,args.sign)),indent=2))
