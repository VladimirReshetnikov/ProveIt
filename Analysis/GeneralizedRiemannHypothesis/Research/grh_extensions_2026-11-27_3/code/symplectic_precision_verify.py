#!/usr/bin/env python3
"""Exact checks for stable-range symplectic precision persistence.

Standard-library only. Uses integer Fourier transforms, never floating point,
for Z/2, Z/3, Z/4 and F_2[t]/(t^2). The pair-Gram distributions are independently
enumerated, and every alternating residual at precision two is checked.
"""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import argparse
import json
import time


class Ring:
    def __init__(self, p, e=1, dual=False):
        self.p, self.e, self.dual = p, e, dual
        self.n = p ** e
        self.name = "F2[t]/(t^2)" if dual else f"Z/{self.n}Z"
        assert (p, e, dual) in [(2, 1, False), (3, 1, False), (2, 2, False), (2, 2, True)]

    def add(self, x, y):
        return x ^ y if self.dual else (x + y) % self.n

    def neg(self, x):
        return x if self.dual else (-x) % self.n

    def sub(self, x, y):
        return self.add(x, self.neg(y))

    def mul(self, x, y):
        if self.dual:
            return ((x & 1) * (y & 1)) | ((((x & 1) * (y >> 1)) ^ ((x >> 1) * (y & 1))) << 1)
        return x * y % self.n

    def inv(self, x):
        if self.dual:
            assert x & 1
            return x
        return pow(x, -1, self.n)


def digits(i, base, k):
    a = []
    for _ in range(k):
        a.append(i % base)
        i //= base
    return a


def index(a, base):
    z = 0
    for x in reversed(a):
        z = z * base + x
    return z


def rank_field(A, p):
    A = [[x % p for x in row] for row in A]
    if not A:
        return 0
    nr, nc, r = len(A), len(A[0]), 0
    for j in range(nc):
        pivot = next((i for i in range(r, nr) if A[i][j]), None)
        if pivot is None:
            continue
        A[r], A[pivot] = A[pivot], A[r]
        z = pow(A[r][j], -1, p)
        A[r] = [(x * z) % p for x in A[r]]
        for i in range(nr):
            if i != r:
                z = A[i][j]
                A[i] = [(x - z * y) % p for x, y in zip(A[i], A[r])]
        r += 1
        if r == nr:
            break
    return r


def image_length(A, R):
    """Composition length of image over a length-one or length-two DVR ring."""
    if R.e == 1:
        return rank_field(A, R.p)
    A = [row[:] for row in A]
    s, r = len(A), 0
    while r < s:
        pos = next(((i, j) for i in range(r, s) for j in range(r, s) if A[i][j] & 1), None)
        if pos is None:
            break
        i, j = pos
        A[r], A[i] = A[i], A[r]
        for row in A:
            row[r], row[j] = row[j], row[r]
        z = R.inv(A[r][r])
        A[r] = [R.mul(x, z) for x in A[r]]
        for i in range(s):
            if i != r:
                z = A[i][r]
                A[i] = [R.sub(x, R.mul(z, y)) for x, y in zip(A[i], A[r])]
        r += 1
    tail = [[A[i][j] >> 1 for j in range(r, s)] for i in range(r, s)]
    return 2 * r + rank_field(tail, 2)


def alt_matrix(v, s, R):
    A = [[0] * s for _ in range(s)]
    k = 0
    for i in range(s):
        for j in range(i + 1, s):
            A[i][j], A[j][i] = v[k], R.neg(v[k])
            k += 1
    return A


def fourier_integer(weights, R, m):
    """Unnormalized negative DFT over the additive alternating-coordinate group."""
    base = R.n
    N = len(weights)
    if R.dual or base == 2:
        out = weights[:]
        step = 1
        while step < N:
            for block in range(0, N, 2 * step):
                for j in range(step):
                    a, b = out[block+j], out[block+j+step]
                    out[block+j], out[block+j+step] = a+b, a-b
            step *= 2
        if R.dual:
            # psi(a+bt)=(-1)^b, so the duality swaps the two bits of each coordinate.
            out = [out[index([((x & 1) << 1) | (x >> 1) for x in digits(h, 4, m)], 4)] for h in range(N)]
        return out
    pairs = [(x, 0) for x in weights]
    step = 1
    for _ in range(m):
        for block in range(0, N, base * step):
            for j in range(step):
                z = [pairs[block+j+k*step] for k in range(base)]
                if base == 4:
                    a,b,c,d = z
                    out = [
                        (a[0]+b[0]+c[0]+d[0], a[1]+b[1]+c[1]+d[1]),
                        (a[0]+b[1]-c[0]-d[1], a[1]-b[0]-c[1]+d[0]),
                        (a[0]-b[0]+c[0]-d[0], a[1]-b[1]+c[1]-d[1]),
                        (a[0]-b[1]-c[0]+d[1], a[1]+b[0]-c[1]-d[0])]
                else:
                    # Eisenstein coordinates x+y*w, w^2+w+1=0.
                    a,b,c = z
                    out = [
                        (a[0]+b[0]+c[0], a[1]+b[1]+c[1]),
                        (a[0]+b[1]-b[0]-c[1], a[1]-b[0]+c[0]-c[1]),
                        (a[0]-b[1]+c[1]-c[0], a[1]+b[0]-b[1]-c[0])]
                for k, val in enumerate(out):
                    pairs[block+j+k*step] = val
        step *= base
    assert all(y == 0 for x,y in pairs), "Fourier result must be an ordinary integer"
    return [x for x,y in pairs]


def gram_density(R, s, c, lengths=None):
    m = s * (s-1) // 2
    N = R.n ** m
    if lengths is None:
        lengths = [image_length(alt_matrix(digits(i, R.n, m), s, R), R) for i in range(N)]
    den = R.p ** (c * R.e * s)
    numer = fourier_integer([R.p ** (c * (R.e*s-l)) for l in lengths], R, m)
    assert min(numer) >= 0
    assert sum(numer) == N * den
    return numer, den, lengths


def pair_gram_counts(R, s):
    m = s*(s-1)//2
    counts = [0] * R.n**m
    vs = list(product(range(R.n), repeat=s))
    for x in vs:
        for y in vs:
            g = [R.sub(R.mul(x[i], y[j]), R.mul(y[i], x[j])) for i in range(s) for j in range(i+1,s)]
            counts[index(g, R.n)] += 1
    return counts


def D(q, v, k):
    ans = F(1)
    for i in range(v-k+1,v+1):
        ans *= 1-F(1,q**(2*i))
    return ans


def j_coords(s):
    return [int(j==i+1 and i%2==0) for i in range(s) for j in range(i+1,s)]


def beta_rank_chain(q,a,b):
    """Existing finite-field rank chain, O(a*b), credited in the paper."""
    state=[F(0)]*(b+1)
    state[b]=F(1)
    for _ in range(a):
        new=[F(0)]*(b+1)
        for i,mass in enumerate(state):
            d=2*b-2*i
            up=(1-F(1,q**d))*(1-(F(1,q**(d-1)) if d else F(q)))
            down=F(1,q**(2*d+1))*(1-F(1,q**(2*i)))
            if i<b:
                new[i+1]+=mass*up
            if i:
                new[i-1]+=mass*down
            new[i]+=mass*(1-up-down)
        state=new
    return state[b]


def exact_case(R, a, b, c, independent_pair=True):
    s, n = 2*b, a+c
    m=s*(s-1)//2
    N=R.n**m
    fc, dc, lengths = gram_density(R,s,c)
    fa, da, _ = gram_density(R,s,a,lengths)
    pair_checks = 0
    if independent_pair:
        f1,d1,_ = gram_density(R,s,1,lengths)
        counts=pair_gram_counts(R,s)
        total=R.n**(2*s)
        assert all(f1[h]*total==counts[h]*N*d1 for h in range(N))
        pair_checks=total
    denframe = D(R.p,n,b)
    alpha = D(R.p,c,b)/denframe
    J=j_coords(s)
    beta_num=0
    tvsum=0
    sign_checks=0
    min_singular=None
    max_nonsingular=None
    for h in range(N):
        H=digits(h,R.n,m)
        g=index([R.sub(x,y) for x,y in zip(J,H)],R.n)
        rank=rank_field(alt_matrix(H,s,R),R.p)
        likelihood=F(fc[h],dc)/denframe
        if rank<s:
            assert likelihood>1, (R.name,a,b,c,h,likelihood)
            min_singular=likelihood if min_singular is None else min(min_singular,likelihood)
        else:
            assert likelihood==alpha and likelihood<1
            beta_num += fa[g]
            max_nonsingular=likelihood
        tvsum += fa[g]*abs(fc[h]*denframe.denominator-dc*denframe.numerator)
        sign_checks+=1
    beta=F(beta_num,N*da)
    assert beta==beta_rank_chain(R.p,a,b)
    tv=F(tvsum,2*N*da*dc*denframe.numerator)
    assert tv==(1-alpha)*beta
    return dict(ring=R.name,a=a,b=b,c=c,n=n,precision=R.e,
                alpha=str(alpha),beta=str(beta),tv=str(tv),tv_decimal=float(tv),
                min_singular_likelihood=str(min_singular),
                nonsingular_likelihood=str(max_nonsingular),
                alternating_residuals_checked=sign_checks,
                independently_enumerated_pairs=pair_checks)


def exhaustive_observed_field(q,a,b):
    """Independent enumeration of every observed B matrix over F_q."""
    s=2*b
    J=j_coords(s)
    nonsingular=0
    total=q**(2*a*s)
    for entries in product(range(q), repeat=2*a*s):
        rows=[entries[i*s:(i+1)*s] for i in range(2*a)]
        G=[sum(rows[2*k][i]*rows[2*k+1][j]-rows[2*k][j]*rows[2*k+1][i] for k in range(a))%q
           for i in range(s) for j in range(i+1,s)]
        H=[(x-y)%q for x,y in zip(J,G)]
        if rank_field(alt_matrix(H,s,Ring(q)),q)==s:
            nonsingular+=1
    return dict(q=q,a=a,b=b,total=total,nonsingular=nonsingular,beta=str(F(nonsingular,total)))


def inequality_checks():
    checks=0
    for q in [2,3,4,5,7,8,9,11]:
        for b in range(1,9):
            s=2*b
            for c in range(s-1,s+5):
                for r in range(b):
                    t=s-2*r
                    u=c-s+r+1
                    L=D(q,c,c-u)*(1+F(1,q**(2*u))*sum(F(1,q**j) for j in range(1,t)))
                    assert L>1
                    checks+=1
    return checks


def fourier_recursion_checks():
    """Check conductor recursion against independently enumerated image lengths."""
    checks=0
    for R in [Ring(2),Ring(3),Ring(2,2),Ring(2,2,True)]:
        q,e=R.p,R.e
        for s in range(2,5):
            def z(level,d,c):
                if level==0 or d<2:
                    return F(1)
                ring=Ring(q,level,R.dual and level==2)
                m=d*(d-1)//2
                return sum(F(1,q**(c*image_length(alt_matrix(digits(i,ring.n,m),d,ring),ring)))
                           for i in range(ring.n**m))
            rankcounts={r:0 for r in range(1,s//2+1)}
            field=Ring(q)
            for i in range(q**(s*(s-1)//2)):
                rank=rank_field(alt_matrix(digits(i,q,s*(s-1)//2),s,field),q)
                if rank:
                    rankcounts[rank//2]+=1
            for c in range(1,6):
                lhs=z(e,s,c)-z(e-1,s,c)
                rhs=F(0)
                for r,A in rankcounts.items():
                    exponent=2*c*r+r*(2*c-2*s+2*r+1)*(e-1)
                    factor=F(1,q**exponent) if exponent>=0 else F(q**(-exponent))
                    rhs+=A*factor*z(e-1,s-2*r,c)
                assert lhs==rhs,(R.name,s,c,lhs,rhs)
                checks+=1
    return checks


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--output",default=str(Path(__file__).resolve().parents[1]/"data"/"symplectic_precision_checks.json"))
    args=parser.parse_args()
    start=time.time()
    cases=[]
    for R in [Ring(2),Ring(3),Ring(2,2),Ring(2,2,True)]:
        cases.append(exact_case(R,2,2,3))
    cases.append(exact_case(Ring(3),1,2,3,False))
    observed=[exhaustive_observed_field(2,2,2),exhaustive_observed_field(3,1,2)]
    assert observed[0]["beta"]==cases[0]["beta"]
    assert observed[1]["beta"]==cases[-1]["beta"]
    assert cases[0]["tv"]==cases[2]["tv"]==cases[3]["tv"]
    result={"arithmetic":"exact integer and rational arithmetic; floating point only for displayed decimals",
            "cases":cases,"independent_observed_matrix_counts":observed,
            "strict_lower_bound_parameter_checks":inequality_checks(),
            "fourier_conductor_recursion_checks":fourier_recursion_checks(),
            "elapsed_seconds":round(time.time()-start,3),"status":"all assertions passed"}
    out=Path(args.output)
    out.parent.mkdir(parents=True,exist_ok=True)
    out.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps(result,indent=2))


if __name__=="__main__":
    main()
