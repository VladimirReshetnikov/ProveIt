#!/usr/bin/env python3
"""Exact certificates for the half-order alphabet threshold.

Only Python's standard library is required. Assertions use rational or integer
arithmetic, never floating-point sign tests. This is not a proof-assistant file.
"""
from fractions import Fraction as Q
from math import isqrt
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parents[1]
checks = 0

def check(condition: bool, label: str) -> None:
    global checks
    if not condition:
        raise AssertionError(label)
    checks += 1

def add(a, b):
    c = [Q(0)] * max(len(a), len(b))
    for i, v in enumerate(a): c[i] += v
    for i, v in enumerate(b): c[i] += v
    return c

def mul(a, b):
    c = [Q(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b): c[i+j] += x*y
    return c

def sqrt_interval(x: Q, digits: int = 75):
    if x < 0: raise ValueError('Square-root input must be nonnegative')
    scale = 10**digits
    n = isqrt((x.numerator * scale**2) // x.denominator)
    lo, hi = Q(n, scale), Q(n+1, scale)
    check(lo*lo <= x < hi*hi, 'outward square-root enclosure')
    return lo, hi

def root_sum(s: Q):
    a = sqrt_interval((81+17*s)/98)
    b = sqrt_interval((1-s)/98)
    return a[0]+17*b[0], a[1]+17*b[1]

def interval_mul(a, b):
    corners = [a[i]*b[j] for i in (0,1) for j in (0,1)]
    return min(corners), max(corners)

def polynomial_interval(coeffs, interval):
    result = (Q(0),Q(0))
    for a in reversed(coeffs):
        z = interval_mul(result, interval)
        result = z[0]+a, z[1]+a
    return result

def cubic(k: int, y: Q) -> Q:
    K = k-1
    return y**3 - 3*y*y - 3*K*y + K

def isolate_maximum(k: int, steps: int = 300):
    # Unique relevant root is above max(1,sqrt(K)); k itself is not
    # necessarily below it, so start at sqrt(K) rounded upwards only
    # if the cubic is still negative.
    K = k-1
    lo = Q(1)
    hi = Q(2*K+10)
    check(cubic(k, lo)<0<cubic(k,hi), 'root bracket')
    for _ in range(steps):
        mid = (lo+hi)/2
        if cubic(k,mid)<0: lo=mid
        else: hi=mid
    check(lo>1 and lo*lo>K and cubic(k,lo)<0<cubic(k,hi),
          'optimizer root isolated in its uniqueness domain')
    return lo, hi

def threshold_poly(K: int, n: int):
    # (y^2+K)^2 - (n-2) K y (y-1)^2
    return [Q(K*K), -Q((n-2)*K), Q(2*K*(n-1)),
            -Q((n-2)*K), Q(1)]

def main():
    K=16
    lhs=add(mul([K,0,1],[K,0,1]),[0,-K,2*K,-K])
    rhs=add(add(mul([-1,-8,1],[-1,-8,1]),
                [128,-32,2]),[127])
    check(lhs==rhs, 'seventeen-symbol sum-of-squares identity')
    check(127>0, 'strict positivity of certificate constant')
    R = Q((9+17)*(9**3+17), (9**2+17)**2)
    tau=(R-1)/(2*R-1)
    check(R==Q(4849,2401), 'rational eighteen-symbol R')
    check(tau==Q(2448,7297), 'rational leverage')
    check(3*tau-1==Q(47,7297)>0, 'strict positive curvature')
    check(Q(81,98)+17*Q(1,98)==1, 'probability normalization')
    # T''(0)=6 g(0)[2 g'(0)^2+g(0)g''(0)].
    # g=A/sqrt(98), A(0)=26, A'(0)=-68/9,
    # A''(0)=-289/(4*729)-17/4.
    A, Ap, App = Q(26), -Q(68,9), -Q(289,2916)-Q(17,4)
    # Since 98^(3/2)=686 sqrt(2), coefficient of sqrt(2) is /1372.
    second_coeff=6*A*(2*Ap*Ap+A*App)/1372
    check(second_coeff==Q(10387,83349)>0, 'exact second derivative')
    h=Q(1,1000)
    minus,zero,plus=root_sum(-h),root_sum(Q(0)),root_sum(h)
    lo=plus[0]**3+minus[0]**3-2*zero[1]**3
    hi=plus[1]**3+minus[1]**3-2*zero[0]**3
    lower,upper=Q(88119833628,10**18),Q(88119833629,10**18)
    check(lower<lo<hi<upper, 'finite Jensen deficit enclosure')
    # Binary equality has an independent polynomial square certificate.
    check(threshold_poly(1,10)==mul([1,-4,1],[1,-4,1]),
          'binary ten-factor equality certificate')
    table=[]
    for k,N in [(2,10),(3,6),(4,5),(5,4),(7,3),(8,3),(10,3),
                (16,3),(17,3),(18,2),(32,2),(64,2),(128,2),(256,2)]:
        interval=isolate_maximum(k)
        for n,expected in [(N,True),(N+1,False)]:
            if k==2 and n==10:
                # The square certificate above proves nonnegativity globally.
                continue
            v=polynomial_interval(threshold_poly(k-1,n),interval)
            check(v[0]>0 if expected else v[1]<0,
                  f'exact concavity decision k={k}, n={n}')
        table.append({'k':k,'largest_concave_n_at_half_order':N,
                      'optimizer_y_lower':str(interval[0]),
                      'optimizer_y_upper':str(interval[1])})
    result={'status':'PASS: all exact arithmetic assertions passed',
            'assertions':checks,'R_witness':str(R),'tau_witness':str(tau),
            'positive_curvature_excess':str(3*tau-1),
            'second_derivative':'(10387/83349)*sqrt(2)',
            'Jensen_h':str(h),'Jensen_gap_lower':str(lower),
            'Jensen_gap_upper':str(upper),'half_order_certificates':table,
            'scope':'Finite certificates, not a formal verification of the analytic theorems.'}
    out=ROOT/'verification'/'exact_certificates.json'
    out.parent.mkdir(exist_ok=True)
    out.write_text(json.dumps(result,indent=2)+'\n')
    print(result['status'])
    print('Exact assertions:', checks)
    print('Finite Jensen gap:', lower, '< Delta <', upper)
    print('Certified half-order alphabet/dimension pairs:',len(table))
    print('Written:',out.relative_to(ROOT))

if __name__=='__main__': main()
