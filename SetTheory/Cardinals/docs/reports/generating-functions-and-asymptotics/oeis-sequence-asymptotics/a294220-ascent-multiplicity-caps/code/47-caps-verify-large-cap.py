#!/usr/bin/env python3
"""High-precision numerical checks; analytic proof does not depend on them."""
import json
import mpmath as mp
mp.mp.dps = 70
A = mp.pi**2/6
D = 9/mp.pi**4

def E(b,v):
    term = total = mp.mpf(1)
    for k in range(1,b+1):
        term *= v/k
        total += term
    return total

def critical(b):
    def fn(v):
        if v == 0: return mp.mpf(1)
        z = E(b,v)
        if z == 1: return mp.mpf(1)
        return mp.log(z)/(z-1)
    return mp.quad(fn,[0,1,b/2,b,2*b,mp.inf])

def linear_integral(b):
    def fn(v):
        if v == 0: return mp.mpf(0)
        # R/e^v is a lower incomplete-gamma ratio, avoiding tail cancellation.
        Q = mp.gammainc(b+1,0,v)/mp.factorial(b)
        if v < mp.mpf('1e-20'): return mp.exp(v)*Q/2
        z = mp.exp(-v)
        return Q*z*(v+mp.expm1(-v))/(-mp.expm1(-v))**2
    return mp.quad(fn,[0,1,b/2,b,2*b,mp.inf])

out = {}
for b in [3,4,8,12,20,30,50]:
    T = critical(b)
    L = (b+1)*(mp.zeta(b+2)-1)
    M = mp.mpf(b+1)/2**(b+2)
    H = T-A-L
    bound = 160*mp.mpf(b)**mp.mpf('2.5')*(mp.mpf(4)/9)**b
    assert 0 < H < bound
    numerical_L = linear_integral(b)
    assert abs(numerical_L-L) < mp.mpf('1e-55')
    gap = 1/A-1/T
    leading_gap = D*(b+1)/2**b
    assert leading_gap < gap
    B = -mp.lambertw(-leading_gap*mp.log(2)/(2*D),-1)/mp.log(2)-1
    assert abs(B-b) < mp.mpf('1e-55')
    out[str(b)] = {key:mp.nstr(val,40) for key,val in {
        'T_b':T, 'mu_b':1/T, 'large_cap_leading_ratio':(T-A)/M,
        'linear_variation':L, 'linear_quadrature_difference':numerical_L-L,
        'nonlinear_remainder':H, 'explicit_remainder_bound':bound,
        'growth_gap_over_leading':gap/leading_gap,
        'cap_inverse_at_model_jump':B}.items()}
# Exercise principal-branch inversion of the exact length leading model.
for b in [2,3,4,8]:
    T = critical(b)
    rows=[]
    for L in [100,1000,1000000]:
        n0 = L/mp.lambertw(mp.mpf(L)/(mp.e*T))
        assert abs(n0*mp.log(n0/(mp.e*T))-L) < mp.mpf('1e-55')
        rows.append({'log_target':L,'model_length':mp.nstr(n0,40)})
    out[str(b)+'_length_models']=rows
print(json.dumps(out,indent=2))
