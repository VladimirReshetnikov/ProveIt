#!/usr/bin/env python3
"""Portable supporting checks. Exact integer boundaries; numerical asymptotic evidence.
Default mode compares the saved receipt and never writes. Use --write to refresh it.
No source-repository code is imported or run. Python 3 standard library only.
"""
from __future__ import annotations
import argparse
import json
import math
from pathlib import Path
from decimal import Decimal, getcontext

# Reference constants affect only displayed numerical residuals, never counts.
ZETA_HALF = Decimal("-1.46035450880958681288949915251529801246722933101258149054288608782553053")
ZETA_TWO = Decimal("1.64493406684822643647241516664602518921894990120679843773555822937000747")

HERE = Path(__file__).resolve().parent
RECEIPT = HERE / 'SECOND-TERM-RECEIPT.json'


def check(ok, message):
    if not ok:
        raise RuntimeError(message)


def pell_pair(base, n):
    delta = base * base - 1
    x, y, u, v = 1, 0, base, 1
    while n:
        if n & 1:
            x, y = x*u + delta*y*v, x*v + y*u
        u, v = u*u + delta*v*v, 2*u*v
        n >>= 1
    return x, y


class ExactPellModel:
    def __init__(self, A, p, M):
        self.A, self.p, self.M = A, p, M
        self.delta = A*A-1
        self.lam = math.acosh(A)
        self.rs = {}
        self.ys = {}

    def R(self, l):
        if l not in self.rs:
            self.rs[l] = self.delta * pell_pair(self.A, self.M*l)[1]
        return self.rs[l]

    def height(self, l, n):
        key = (l, n)
        if key not in self.ys:
            self.ys[key] = pell_pair(self.R(l), n)[1]
        return self.ys[key]

    def endpoint(self, H, height):
        # Entirely integer bracketing, no float endpoint claim.
        lo, hi = 0, 1
        while height(hi) <= H:
            lo, hi = hi, 2*hi
        while hi-lo > 1:
            mid = (lo+hi)//2
            if height(mid) <= H:
                lo = mid
            else:
                hi = mid
        return lo

    def baseline(self, H):
        return self.endpoint(H, lambda l: self.height(l, self.p))

    def direct_count(self, H):
        total = self.baseline(H)
        l = 1
        while self.height(l, 4*self.M*l-self.p) <= H:
            m = self.M*l
            for sign in (-1, 1):
                k = 1
                while self.height(l, 4*m*k+sign*self.p) <= H:
                    total += 1
                    k += 1
            l += 1
        return total

    def inverse_count(self, H):
        total = self.baseline(H)
        T = math.log(H)
        # Exact monotone endpoint, independent of the real-valued proposal.
        limit = self.endpoint(H, lambda l: self.height(l, 4*self.M*l-self.p))
        for l in range(1, limit+1):
            m, R = self.M*l, self.R(l)
            beta_approx = math.log(R) + math.log(2)
            t = 1 + T/beta_approx
            for sign in (-1, 1):
                k = max(0, math.floor((t-sign*self.p)/(4*m)))
                # Real-valued estimates are only proposals. Exact integer
                # comparisons decide both sides of each actual threshold.
                while k > 0 and self.height(l, 4*m*k+sign*self.p) > H:
                    k -= 1
                while self.height(l, 4*m*(k+1)+sign*self.p) <= H:
                    k += 1
                check(k == 0 or self.height(l, 4*m*k+sign*self.p) <= H,
                      'lower endpoint check failed')
                check(self.height(l, 4*m*(k+1)+sign*self.p) > H,
                      'upper endpoint check failed')
                total += k
        return total


def exact_boundary_checks():
    out = []
    # M=8 is only an analytic count model. M=105 is the genuine progression
    # pc/gcd(c,delta) for the auxiliary A=3,p=3 data; neither is a padded native
    # port instance. The analytic count proof applies to both pair models.
    for A, p, M, fixtures in [
        (3, 3, 8, [(1,1,-1),(1,1,1),(2,1,-1),(2,2,1),(3,1,-1),(3,2,1)]),
        (3, 3, 105, [(1,1,-1),(1,1,1)]),
    ]:
        model = ExactPellModel(A,p,M)
        for l,k,sign in fixtures:
            h = model.height(l,4*M*l*k+sign*p)
            counts = []
            for delta in (-1,0,1):
                H = h+delta
                direct = model.direct_count(H)
                inverse = model.inverse_count(H)
                check(direct == inverse, f'exact boundary mismatch: {A,p,M,l,k,sign,delta}')
                counts.append(direct)
            check(counts[1] > counts[0], 'known Pell height did not create a jump')
            check(counts[2] == counts[1], 'unexpected adjacent positive integer height')
            out.append({'A':A,'p':p,'M':M,'l':l,'k':k,'sign':sign,
                        'height_bits':h.bit_length(),'counts_below_at_above':counts})
    return out


def model_count(X, perturbed):
    # Exact integer energies. The bounded parity term deliberately exercises
    # floor-phase perturbations rather than silently deleting them.
    total = 0
    L = math.isqrt(X)+4
    for l in range(1,L+1):
        slope = l*l+3*l if perturbed else l*l
        for sign in (-1,1):
            shift = (sign*2-1)*l if perturbed else 0
            def energy(k):
                return slope*k+shift+(k%2 if perturbed else 0)
            k = max(0,(X-shift)//slope)
            while k > 0 and energy(k) > X:
                k -= 1
            while energy(k+1) <= X:
                k += 1
            total += k
    return total


def numeric_model_checks():
    z = ZETA_HALF
    rows = []
    for perturbed in (False,True):
        # Exact sums: sum l^-2=zeta(2); sum 1/[l(l+3)]=H_3/3=11/18.
        kappa = Decimal(11)/9 if perturbed else 2*ZETA_TWO
        for X in (10**4,10**6,10**8,10**10):
            count = model_count(X,perturbed)
            sqrtX = Decimal(X).sqrt()
            secondary = (count-kappa*X)/sqrtX
            thirdX = Decimal(X) ** (Decimal(1)/3)
            remainder = (count-kappa*X-2*z*sqrtX)/thirdX
            rows.append({'model':'perturbed_exact_integer' if perturbed else 'quadratic_exact_integer',
                         'X':X,'count':count,
                         'secondary_normalized':format(secondary,'.15g'),
                         'predicted_secondary':format(2*z,'.15g'),
                         'remainder_over_X_third':format(remainder,'.15g')})
    return rows


def phase_and_hyperbola_checks():
    checks = 0
    mutations_detected = 0
    for X in list(range(1,301))+[999,1000,1001,9999,10000,10001]:
        L = max(1,round(X**(1/3)))
        for sign in (-1,1):
            def E(l,k):
                return (l*l+3*l)*k+(sign*2-1)*l+k%2
            def row(l):
                k=max(0,(X-(sign*2-1)*l)//(l*l+3*l))
                while k and E(l,k)>X: k-=1
                while E(l,k+1)<=X: k+=1
                return k
            def col(k):
                l=0
                while E(l+1,k)<=X: l+=1
                return l
            K=row(L)
            direct=sum(row(l) for l in range(1,math.isqrt(X)+5))
            split=sum(row(l) for l in range(1,L+1))+sum(col(k) for k in range(1,K+1))-L*K
            check(split==direct, 'exact cutoff hyperbola identity failed')
            checks+=1
            if K and split+L*K!=direct:
                mutations_detected+=1
    check(mutations_detected>0,'rectangle-omission mutation was not detected')
    # Removing the phase changes at least one exact count near low boundaries.
    examples=0
    for X in range(1,100):
        exact=model_count(X,True)
        phase_dropped=0
        for l in range(1,math.isqrt(X)+5):
            for sign in (-1,1):
                phase_dropped += max(0,(X-(sign*2-1)*l)//(l*l+3*l))
        examples += exact != phase_dropped
    check(examples>0,'phase-dropping mutation was not detected')
    return {'exact_hyperbola_identities':checks,
            'rectangle_omission_mutation_failures':mutations_detected,
            'phase_drop_mutation_failures':examples}


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--write',action='store_true')
    args=parser.parse_args()
    getcontext().prec=60
    result={'status':'PASS','residual_decimal_precision':60,
            'exact_pell_boundaries':exact_boundary_checks(),
            'hyperbola_and_mutation_checks':phase_and_hyperbola_checks(),
            'exact_integer_asymptotic_models':numeric_model_checks(),
            'evidence_boundary':'Finite supporting checks, not a proof of the native classification or an asymptotic theorem. Every model count above is an integer-exact count; displayed normalized residuals use Decimal and precomputed zeta constants; no third-party runtime dependency.'}
    encoded=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.write:
        RECEIPT.write_text(encoded)
        print('PASS: wrote',RECEIPT.name)
    else:
        check(RECEIPT.read_text()==encoded,'saved receipt mismatch; no files modified')
        print('PASS: matched read-only receipt')
    print('Exact Pell thresholds:',3*len(result['exact_pell_boundaries']))
    print('Exact hyperbola identities:',result['hyperbola_and_mutation_checks']['exact_hyperbola_identities'])
    print('Exact asymptotic model counts:',len(result['exact_integer_asymptotic_models']))


if __name__=='__main__':
    main()
