#!/usr/bin/env python3
"""Bounded corroboration for a proved genuine-history dummy-switch theorem.
Reads frozen proof/source data only; imports or executes no predecessor code.
Finite arithmetic records below are not materialized compiler histories.
"""
import argparse
import hashlib
import json
import math
from pathlib import Path

PINS = {
 'pell_kernel_half_binomial42.md':'0df596859d84aa1cf1d4636457937274e8fdac0c1f8da3196962d911be232992',
 '../../1980/FIXED_RAW_UNIVERSAL_75_PROOF.md':'e381124c969087ffa867448177a9df693d81e7bd85dd3a8489d443220fba053d',
 'complete83_independent_gamma_scout.json':'ed570bc9e96d59e88ec6b6c1302ac177eb6704cfcd85fe39a3346798e89f5e20',
 'complete83_independent_gamma_scout.md':'bdbcc3be5396bced89373da5ffb30f0f3f113f7e8e7ebe65e4f7b730264f1b41',
 'complete83_gamma_native_ternary_exclusion.md':'6eee2ade562b73c264358f3e051efda02e832c102d43f79ba3ade9e9d68ff77b',
 'complete75_half_binomial_compiler.md':'68edf3bc40238ccf47b023d7358e4be62664a2d78a60b6fae19de14b67208117',
 'complete75_bounded_projection_elimination99.md':'381dfecd4b608069a67a43f163d1c1c2b9ff4fcd4ed4d9409e03f45d1fbc24af',
 '../../1980/EXPLORATION_FIVE_ADIC_DUMMY_CONTROL.md':'44ed02164f61e410bb377b52aa292abf476e025eeea1052784f30d654a0522fa',
 'complete80_first_index_deletion_collapse.md':'a6fb0955f6a19a7564a3070cbf5bdc4e76a6a39a572b46a4d8f656ae9113a575',
}

def need(ok, message):
    if not ok:
        raise ValueError(message)

def v3(n):
    need(n != 0, 'valuation at zero')
    n = abs(n)
    k = 0
    while n % 3 == 0:
        n //= 3
        k += 1
    return k

def pairs(items):
    result = {}
    for k, v in items:
        need(k not in result, 'duplicate JSON key')
        result[k] = v
    return result

def bad_constant(s):
    raise ValueError('nonfinite JSON constant '+s)

def read_json(path):
    return json.loads(path.read_text(), object_pairs_hook=pairs, parse_constant=bad_constant)

def exact(a, b):
    if type(a) is not type(b):
        return False
    if isinstance(a, dict):
        return a.keys() == b.keys() and all(exact(a[k], b[k]) for k in a)
    if isinstance(a, list):
        return len(a) == len(b) and all(exact(x, y) for x, y in zip(a, b))
    return a == b

def low_subset(d, N, target):
    B, M, T = 2**d, d*N, N//5
    inverse = {}
    w = 1
    for j in range(T):
        need((w-1) % (5*d) == 0, 'subgroup coset')
        t = ((w-1)//(5*d)) % T
        need(t not in inverse, 'subgroup collision')
        inverse[t] = j
        w = w*pow(B,4,M) % M
    eps = int(target % 5 == 0)
    k = (target-eps*B) % (5*d)
    need(0 < k < T and k % 5 != 0, 'subset cardinality')
    s = ((target-eps*B-k)//(5*d)) % T
    t0 = (s-k*(k-1)//2)*pow(k,-1,T) % T
    slots = sorted(4*inverse[(t0+j) % T] for j in range(k))
    if eps:
        slots.append(1)
        slots.sort()
    need(len(slots) == len(set(slots)), 'duplicate low slot')
    need(sum(pow(B,i,M) for i in slots) % M == target % M, 'subset target')
    return slots

def verify(root):
    for name, digest in PINS.items():
        need(hashlib.sha256((root/name).read_bytes()).hexdigest() == digest, 'pin '+name)
    source = read_json(root/'complete83_independent_gamma_scout.json')
    # The unchanged source is authenticated, not regenerated here.
    need(isinstance(source, dict), 'source data')
    affine = []
    for j in range(1, 25):
        q, D, Z, F, Mmask, b = 2**(4+j % 5), 3*j+1, j-3, 5-j, 7*j, 2**(j % 6+1)
        old = (q*q-Z-q*F)*(q*q-1)+Mmask
        new = (q*q-(Z+b)-q*(F+D*b))*(q*q-1)+Mmask
        change = -b*(q*q-1)*(1+q*D)
        need(new-old == change, 'exact packing difference')
        affine.append({'j':j,'difference':change})
    subsets = []
    orbits = []
    for d, N, h in [(1,125,5),(5,625,5),(25,3125,25)]:
        B, M, L = 2**d, d*N, 4*N//5
        need(pow(B,L,M) == 1, '5-adic switch return')
        need(L+2+h < N and L+3 < N, 'nonwrapping upper slots')
        need(v3(pow(B,L)-1) == 1, 'exact ternary switch valuation')
        for target in [0,1,2,4,5,17,M//2,M-1]:
            slots = low_subset(d,N,target)
            need(max(slots)+h < N and max(slots)+1 < N, 'nonwrapping low slots')
            need(L not in slots and L+2 not in slots, 'high switch slots outside old control set')
            subsets.append({'d':d,'N':N,'h':h,'target':target,'slots':slots})
        for vg in range(1,7):
            for unit in [1,2,4,5]:
                Gamma = 3**vg*unit
                s, modulus = vg+1, 3**(vg+2)
                A = (-2*Gamma*(pow(B,L,modulus)-1)) % modulus
                D2 = A*pow(B,2,modulus) % modulus
                need(v3(A) == s and (D2-A) % modulus == 0, 'equal leading switches')
                for r0 in [0,1,2,3,17,modulus//3-1]:
                    R0 = 2*r0+1
                    r_values = [((R0+a-1)*pow(2,-1,modulus)) % modulus for a in [0,A,A+D2]]
                    digits = [(r//(3**s)) % 3 for r in r_values]
                    need(sorted(digits) == [0,1,2], 'ternary digit coverage')
                    orbits.append({'d':d,'N':N,'v3_Gamma':vg,'unit':unit,'r_residue':r0,
                                   'digit_position':s,'three_digits':digits})
    native = []
    for R in range(3,516,4):
        r = (R-1)//2
        x = pow(2,R,9)
        G = sum(math.comb(2*r,r+j)*pow(x,j,9) for j in range(r+1)) % 9
        a = (x+1)*G*pow(2,-1,9) % 9
        n, digits = r, []
        while n:
            digits.append(n % 3)
            n //= 3
        if 2 in digits:
            need(a == 0, 'native tail digit-two implication')
            need(((a+1)*(a+3)) % 9 == 3, 'discriminant valuation one')
        native.append({'R':R,'r_ternary_lsf':digits,'a_mod9':a,'contains_two':2 in digits})
    margins = []
    for b in [5,25,125]:
        radix = 2**b
        bound = radix//4+7
        need(2*bound < radix-1, 'upper-dummy raw margin')
        margins.append({'b':b,'coefficient_bound':bound,'twice_bound_below_radix_minus_one':True})
    ranks = []
    for u in [1,5,9,13,101]:
        p,n = 55*u,40*u
        need(2*n-p-1 == 25*u-1 > 0, 'first-index obstruction')
        ranks.append({'u':u,'p':p,'n':n,'retained_rank_discrepancy':25*u-1})
    return {'status':'PASS','pins':dict(PINS),
            'scope':'Unchanged83 source. General genuine-history theorem is proved in the note. All finite records are arithmetic corroboration, not instantiated compiler histories or full Pell zeros.',
            'packing_difference_checks':affine,'five_adic_subset_checks':subsets,
            'ternary_switch_orbits':orbits,'native_formula_checks':native,
            'upper_dummy_margin_checks':margins,'factorial_rank_checks':ranks,
            'summary':{'packing_checks':len(affine),'subsets':len(subsets),'switch_orbits':len(orbits),
                       'native_formula_samples':len(native),'digit_two_samples':sum(j['contains_two'] for j in native),
                       'new_conclusion':'Every accepted input admits genuine witnesses with a_R=0 mod9 and v3(m)<=1; ordinary-input language remains unresolved.'}}

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--root',type=Path,default=Path(__file__).resolve().parent)
    g=p.add_mutually_exclusive_group(required=True)
    g.add_argument('--output',type=Path)
    g.add_argument('--expect',type=Path)
    args=p.parse_args()
    receipt=verify(args.root.resolve())
    if args.output is not None:
        args.output.write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
    else:
        need(exact(receipt,read_json(args.expect)), 'exact receipt mismatch')
    print('PASS: native ternary escape bounded checks')

if __name__ == '__main__':
    main()
