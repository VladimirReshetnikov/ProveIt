#!/usr/bin/env python3
"""Independent selected-grid interval check using direct rational log arguments."""
from fractions import Fraction as R
from math import ceil,floor
from pathlib import Path
import argparse
import json
import sys

ROOT=Path(__file__).resolve().parents[1]



class AuditFailure(RuntimeError):
    """A mathematical, provenance, or frozen-receipt check failed."""


def require(condition, message):
    """Checks remain active under python -O."""
    if not condition:
        raise AuditFailure(message)


def run_checks():
    def series(t,N=48):
        z=(t-1)/(t+1);require(0<=z<=R(1,3), 'Check failed: 0<=z<=R(1,3)')
        terms=[z**(2*k+1)/R(2*k+1) for k in range(N)]
        lo=2*sum(terms)
        hi=lo+2*z**(2*N+1)/((2*N+1)*(1-z*z))
        return lo,hi
    log2=series(R(2))
    def logs(r):
        # Multiply/divide the rational by powers of two rather than estimate its logarithm.
        r=R(r);require(r>0, 'Check failed: r>0')
        k=0
        while r<1:r*=2;k-=1
        while r>=2:r/=2;k+=1
        lo,hi=series(r)
        if k>=0:return lo+k*log2[0],hi+k*log2[1]
        return lo+k*log2[1],hi+k*log2[0]

    def candidate(q,w,s,t):
        X=w*q**3;Y=s*q**3;E=X*Y;A=Y*(X+1)+2;P=2*X*Y*Y+1
        amin=2*A-R(1,A);amax=2*A-R(1,2*A)
        bmin=2*P-R(1,P);bmax=2*P-R(1,2*P)
        rmin=R(P*P-1,2*A*P)*(1-R(1,(2*A-1)**26))
        rmax=R(P*A,2*(A*A-1))/(1-R(1,(2*P-1)**14))
        am,ap,bm,bp,rm,rp,ly,ly1=map(logs,(amin,amax,bmin,bmax,rmin,rmax,Y,Y+1))
        half=R(t*E+1,2)
        lower_num=ly[0]-rp[1]+half*bm[0]
        lower_den=ap[1]+bm[1]/2
        upper_num=ly1[1]-rm[0]+half*bp[1]
        upper_den=am[0]+bp[0]/2
        require(min(lower_num,lower_den,upper_num,upper_den)>0, 'Check failed: min(lower_num,lower_den,upper_num,upper_den)>0')
        lower=lower_num/lower_den;upper=upper_num/upper_den
        lo=max(13,ceil(R(t*E,3))+1,floor(lower)+1)
        hi=min(X*q**4-1,(t*E-6)//2,ceil(upper)-1)
        if lo%2==0:lo+=1
        if hi%2==0:hi-=1
        require(lower<upper and upper-lower<R(1,q**3)+R(1,q**5), 'Check failed: lower<upper and upper-lower<R(1,q**3)+R(1,q**5)')
        require(lo>hi, 'Check failed: lo>hi')
        return {'q':q,'w':w,'s':s,'t':t,'lo_odd':lo,'hi_odd':hi,'no_odd_integer':True,
                'width_less_than_qm3_plus_qm5':True}

    # Cover scale extremes, all three q's, both odd rounding directions, and maximal t.
    points=[(16,2,2,1),(16,3,5,3),(20,3,7,2),(20,4,3,4),(32,4,5,3),(32,2,7,5),(16,1,1,1),(16,1,1,47),(16,4,47,1),(20,1,1,59),(20,3,19,3),
            (20,4,59,1),(32,1,1,95),(32,4,1,95),(32,2,95,1),(32,3,31,3)]
    result={'scope':'Selected exact rational exclusions, not a compiler instance or full-zero search.',
            'independent_direct_log_points':[candidate(*p) for p in points]}
    return result

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        help="Write the deterministic receipt outside the packet; default is stdout only")
    parser.add_argument("--expect", type=Path,
                        help="Require a byte-exact match with this frozen JSON receipt")
    args = parser.parse_args()
    if args.output is not None:
        target = args.output.resolve()
        require(not target.is_relative_to(ROOT), "--output must be outside the packet")
        require(args.expect is None or target != args.expect.resolve(),
                "--output must not overwrite the frozen --expect receipt")
    result = run_checks()
    rendered = (json.dumps(result, indent=2, sort_keys=True, ensure_ascii=True) + "\n").encode("utf-8")
    if args.expect is not None:
        require(args.expect.read_bytes() == rendered,
                "Generated receipt differs from the frozen --expect receipt")
    if args.output is not None:
        args.output.write_bytes(rendered)
    sys.stdout.buffer.write(rendered)


if __name__ == "__main__":
    main()
