#!/usr/bin/env python3
"""Fresh finite checks for a genuine-history existence theorem.
Only authenticated predecessor data are read; no predecessor code is run.
All computed examples are formula, congruence or grid samples, not histories.
"""
import argparse
import hashlib
import json
import math
from pathlib import Path

PINS = {
 'complete83_gamma_native_ternary_escape.py':'16c79b5e437ee66a3d42adad3ddb5ce780eaa73df809938749ef9da8071124ea',
 'complete83_gamma_native_ternary_escape.json':'6db086cce06c4207b2d76b5e58c464227005eac08bb8310752bc5fdf816668dc',
 'complete83_gamma_native_ternary_escape.md':'251565e157201575a352d6ad94fe46bc6d2c9812949762247fe9aab2b5743116',
 'complete83_gamma_native_prime_scaling.md':'25a5ea05edca5a94527eeda9c7744e50a045f22deff9616774074c136eefa69a',
 'complete83_independent_gamma_scout.json':'ed570bc9e96d59e88ec6b6c1302ac177eb6704cfcd85fe39a3346798e89f5e20',
 'complete83_independent_gamma_scout.md':'bdbcc3be5396bced89373da5ffb30f0f3f113f7e8e7ebe65e4f7b730264f1b41',
 'complete83_gamma_native_ternary_exclusion.md':'6eee2ade562b73c264358f3e051efda02e832c102d43f79ba3ade9e9d68ff77b',
 'complete75_half_binomial_compiler.md':'68edf3bc40238ccf47b023d7358e4be62664a2d78a60b6fae19de14b67208117',
 '../../1980/EXPLORATION_FIVE_ADIC_DUMMY_CONTROL.md':'44ed02164f61e410bb377b52aa292abf476e025eeea1052784f30d654a0522fa',
 'pell_kernel_half_binomial42.md':'0df596859d84aa1cf1d4636457937274e8fdac0c1f8da3196962d911be232992',
 '../../1980/FIXED_RAW_UNIVERSAL_75_PROOF.md':'e381124c969087ffa867448177a9df693d81e7bd85dd3a8489d443220fba053d',
 'complete75_normalized_strong87.md':'9c1cfa3ccd5a71c127c8e6aa341fad6e857788d708129e04ea177dbbcdccfb3b',
}

def need(ok, message):
    if not ok:
        raise ValueError(message)

def pairs(rows):
    result = {}
    for k, v in rows:
        need(k not in result, 'duplicate JSON key')
        result[k] = v
    return result

def bad_constant(value):
    raise ValueError('nonfinite JSON '+value)

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

def valuation(n, p):
    need(n != 0, 'valuation at zero')
    n, v = abs(n), 0
    while n % p == 0:
        n //= p
        v += 1
    return v

def prime(n):
    return n >= 2 and all(n % j for j in range(2, math.isqrt(n)+1))

def order_two(p):
    need(prime(p) and p > 2, 'odd prime')
    x = 1
    for k in range(1, p):
        x = x*2 % p
        if x == 1:
            return k
    raise ValueError('missing order')

def native_mod(R, modulus):
    """Exact integer binomial recurrence, reduced after each tail term."""
    need(R >= 3 and R % 2 == 1 and modulus % 2 == 1, 'native domain')
    r, x = (R-1)//2, pow(2, R, modulus)
    c = math.comb(2*r, r)
    coefficient, power, total = c, 1, 0
    for j in range(r+1):
        total = (total+coefficient*power) % modulus
        if j < r:
            numerator = coefficient*(r-j)
            need(numerator % (r+j+1) == 0, 'binomial exact division')
            coefficient = numerator//(r+j+1)
            power = power*x % modulus
    return (x+1)*total*pow(2, -1, modulus) % modulus

def central_mod(R, p):
    """Independent prime-field digit product."""
    n, k, out = R-1, (R-1)//2, 1
    while n or k:
        a, b = n % p, k % p
        if b > a:
            return 0
        out = out*math.comb(a, b) % p
        n, k = n//p, k//p
    return out

def has_digit(n, p, digit):
    while n:
        if n % p == digit:
            return True
        n //= p
    return False

def geometric_sum(base, n, modulus):
    """Return (base**n, sum_{j<n}base**j), with no inverse of base-1."""
    power, total, block_power, block_total = 1, 0, base % modulus, 1
    while n:
        if n & 1:
            total = (total+power*block_total) % modulus
            power = power*block_power % modulus
        block_total = block_total*(1+block_power) % modulus
        block_power = block_power*block_power % modulus
        n //= 2
    return power, total

def return_valuation(d, L, p):
    v = 0
    while pow(2, d*L, p**(v+1)) == 1:
        v += 1
        need(v < 100, 'bounded valuation diagnostic')
    return v

def crt(rows):
    value, modulus = 0, 1
    for residue, p in rows:
        value += modulus*((residue-value)*pow(modulus, -1, p) % p)
        modulus *= p
    return value, modulus

def verify(root):
    for name, digest in PINS.items():
        need(hashlib.sha256((root/name).read_bytes()).hexdigest() == digest, 'pin '+name)
    need(isinstance(read_json(root/'complete83_independent_gamma_scout.json'), dict), 'source JSON')
    orders = [{'prime':p, 'order':order_two(p)} for p in [3,5,11,13,31,251,601,1801,4051]]
    need([r['order'] for r in orders] == [2,4,10,12,5,50,25,25,50], 'exact orders')
    factors = []
    for E, minus, plus in [(5,[31],[3,11]), (25,[31,601,1801],[3,11,251,4051])]:
        need(math.prod(minus) == 2**E-1 and math.prod(plus) == 2**E+1, 'factor products')
        factors.append({'E':E, 'minus':minus, 'plus':plus})
    plus_cases = []
    for E in [5,25,125]:
        M = 2**E+1
        need(valuation(M,3) == 1, 'plus LTE')
        for cofactor in [3,7,11,15,19]:
            R = E*cofactor
            a = native_mod(R,M)
            delta = (a+1)*(a+3) % M
            need(a == 0 and math.gcd(delta,M) == 3, 'canonical plus factor')
            need(math.gcd(delta,M//3) == 1, 'removed entire 3 part')
            plus_cases.append({'E':E,'R':R,'a_mod_plus':a,'delta_mod_plus':delta,'gcd':3})
    combined = []
    for E, primes in [(5,[31]),(25,[31,601,1801])]:
        count = 0
        for cofactor in range(3,2000,4):
            R = E*cofactor
            if not has_digit((R-1)//2,3,2) or any(central_mod(R,p) for p in primes):
                continue
            M = 2**(2*E)-1
            a = native_mod(R,3*M)
            delta = (a+1)*(a+3)
            need(a % 9 == 0 and math.gcd(delta,M) == 3 and math.gcd(delta,M//3) == 1,
                 'combined formula example')
            prime_rows = []
            for p in primes:
                direct = native_mod(R,p)
                need(direct == pow(4,-1,p) and delta % p == 65*pow(16,-1,p) % p,
                     'one-base native branch')
                need(math.comb(R-1,(R-1)//2) % p == 0, 'independent central carry')
                prime_rows.append({'p':p,'a_mod_p':direct,'delta_mod_p':delta % p})
            combined.append({'E':E,'R':R,'a_mod_3M':a,'gcd_delta_M':3,'prime_rows':prime_rows})
            count += 1
            if count == 4:
                break
        need(count == 4, 'four finite examples per E')
    geometry, orbits = [], []
    for E, primes in [(5,[3,31]),(25,[3,31,601,1801])]:
        d, h, Q = 5, E//5, 3*(2**E-1)
        Htime = 25
        while Htime <= 5*(2*Q-3) or h*Htime <= 25*d:
            Htime *= 5
        N, Dslot = h*Htime, 2*h
        L, last = 4*N//5, (Q-2)*Dslot
        need(last+h < N//5 and last+L+h < N and last+L+1 < N and last < L, 'grid margins')
        need(pow(2,d*L,d*N) == 1, 'five-adic return')
        need(all(pow(2,d*Dslot,p) == 1 for p in primes), 'common prime return')
        geometry.append({'E':E,'d':d,'h':h,'Q':Q,'Htime':Htime,'N':N,'L':L,'last_source':last})
        for case in range(12):
            Gamma = (2*case+1)*math.prod(p**(1+(case+j) % 4) for j,p in enumerate(primes))
            rbase = 17+case*10007
            constraints, local = [], []
            for p in primes:
                s = valuation(Gamma,p)+return_valuation(d,L,p)
                modulus = p**(s+1)
                G = Gamma*(pow(2,d*L,modulus)-1) % modulus
                need(G % p**s == 0 and G//p**s % p != 0, 'leading movable valuation')
                target = p-1
                residue = ((rbase//p**s)-target)*pow(G//p**s,-1,p) % p
                constraints.append((residue,p))
                local.append((p,s,modulus,G,target))
            k, radical = crt(constraints)
            need(0 <= k < radical <= Q, 'finite prefix exists')
            records = []
            for p,s,modulus,G,target in local:
                ratio = pow(2,d*Dslot,modulus)
                _, weight = geometric_sum(ratio,k,modulus)
                selected = (rbase-G*weight) % modulus
                need(selected//p**s == target and selected % p**s == rbase % p**s,
                     'exact prefix preserves lower digits and sets target')
                records.append({'p':p,'s':s,'target':target,'selected_residue':selected})
            orbits.append({'E':E,'case':case,'Gamma':Gamma,'rbase':rbase,'prefix':k,'radical':radical,'digits':records})
    for base in [1,2,7,19]:
        for n in range(16):
            power,total = geometric_sum(base,n,997)
            need(power == pow(base,n,997) and total == sum(pow(base,j,997) for j in range(n)) % 997,
                 'independent finite geometric check')
    return {'schema':'native-finite-prime-avoidance-v1','pins':PINS,
            'scope':'Formula/congruence/grid corroboration only; no full compiler history or Pell zero materialized.',
            'prime_orders':orders,'factorizations':factors,'plus_formula_cases':plus_cases,
            'combined_formula_cases':combined,'finite_grid_geometry':geometry,'simultaneous_digit_orbits':orbits,
            'totals':{'orders':len(orders),'plus_cases':len(plus_cases),'combined_cases':len(combined),
                      'grids':len(geometry),'orbits':len(orbits),'geometric_checks':64}}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root',type=Path,default=Path(__file__).resolve().parent)
    parser.add_argument('--output',type=Path)
    parser.add_argument('--expect',type=Path)
    args = parser.parse_args()
    need(not (args.output and args.expect), 'choose output or expect')
    result = verify(args.root)
    if args.expect:
        need(exact(result,read_json(args.expect)), 'type-exact receipt mismatch')
    if args.output:
        args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'status':'PASS','totals':result['totals']},sort_keys=True))

if __name__ == '__main__':
    main()
