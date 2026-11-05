#!/usr/bin/env python3
"""Independent reconstruction from pinned literal tiles, not the builder.

Finite checks do not replace the universal decoding and compiler proofs.
"""
from pathlib import Path
from hashlib import sha1, sha256
from math import gcd, isqrt, lcm
import gzip
import json
import random

HERE = Path(__file__).resolve().parent

def check(ok, label):
    if not ok:
        raise ValueError(label)

def factor(n):
    out = {}
    p = 2
    while p*p <= n:
        while n % p == 0:
            out[p] = out.get(p, 0)+1
            n //= p
        p += 1
    if n > 1:
        out[n] = 1
    return out

def isprime(n):
    return n > 1 and all(n % a for a in range(2, isqrt(n)+1))

def main():
    pins = json.loads((HERE/'SOURCE_PINS.json').read_text())
    for entry in pins['files']:
        raw = (HERE/entry['local']).read_bytes()
        check(sha256(raw).hexdigest() == entry['sha256'], 'source SHA256')
        check(sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()
              == entry['git_blob_sha1'], 'source git blob')
    raw = (HERE/'source/coefficients__wang943_tiles.json').read_bytes()
    check(sha256(raw).hexdigest() ==
          '66b55f1d11fca9fefc93b12fcfc8b4cabb75b08e9fd03311f9e894a1c5e5e81f',
          'tile list identity')
    tiles = json.loads(raw)
    check(len(tiles) == 943, 'tile count')
    machine_rows = []
    machine_raw = (HERE/'source/k215.tm').read_bytes()
    check(sha256(machine_raw).hexdigest() ==
          'fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090',
          'literal machine hash')
    for line in machine_raw.decode('ascii').splitlines():
        if line and not line.startswith('#'):
            q,b,v,direction,target = line.split()
            machine_rows.append([int(q),int(b),int(v),{'L':-1,'R':1}[direction],int(target)])
    check(machine_rows == json.loads((HERE/'k215_transitions.json').read_text())['transitions']
          and len(machine_rows) == 430, 'literal transition binding')
    codes = [sum(x << k for x,k in zip(t,(0,8,17,25))) + (127 << 34)
             for t in tiles]
    check(all(0 < v < 1 << 41 for v in codes), 'code range')
    coefficients = {i:1+1024*((1 << 41)-v) for i,v in enumerate(codes)}
    bit_positions = [list(range(8))+[34], list(range(8,17))+[35],
                     list(range(17,25))+[36], list(range(25,34))+[37]]
    for start, positions in zip((1023,1013,1003,983), bit_positions):
        for j,p in enumerate(positions):
            coefficients[start+j] = 1 << (p+10)
    for anchor,p in zip((1095,2195,3296),(38,39,40)):
        coefficients[anchor] = 1 << (p+10)
    coefficients[1063] = coefficients[1064] = 0
    support = set(coefficients)
    mu = (1 << 51)-2
    check(len(support) == 986, 'support cardinality')
    check([n for n in range(944) if n & 1022 == 0] == [0,1], 'selector lemma')
    mutations = 0
    for i,v in enumerate(codes):
        check(coefficients[i]+(v << 10) == (1 << 51)+1, 'canonical clause value')
        for j in range(41):
            check((coefficients[i]+((v ^ (1 << j)) << 10)) & mu,
                  'one-bit erroneous copy')
            mutations += 1
    # Independent exhaustive finite models of the general complement lemma.
    models = 0
    for m in range(1,9):
        limit = 1 << m
        for v in range(limit):
            for w in range(limit):
                check(((limit-v+w) % limit == 0) == (v == w),
                      'finite complement model')
                models += 1
    dc_digits = {e:1 for e in (30,62,1100,2201)}
    for e,c in coefficients.items():
        for t in (4393,5495):
            if c:
                dc_digits[t-e] = dc_digits.get(t-e,0)+c
    targets = [(1013+j,{983+j},set(),{1013+j}) for j in range(10)]
    targets += [(1065+j,{1003+j},{1023+j},set()) for j in range(9)]
    targets += [(2195,{1095},set(),{2195}), (3296,{1095},set(),{3296})]
    checks = 0
    for t,a,c,y in targets:
        for e in support:
            check(dc_digits.get(t-e,0) == int(e in a), 'current overlap')
            check(int(e+42 == t) == int(e in c), 'spatial overlap')
            check(int(e == t) == int(e in y), 'temporal overlap')
            checks += 3
    for t in (4393,5495):
        for e in support:
            check(dc_digits.get(t-e,0) == coefficients[e], 'clause basis')
            check(e+42 != t, 'spatial clause isolation')
            checks += 2
    check({(4393-e)%8807 for e in support}.isdisjoint(
          {(5495-e)%8807 for e in support}), 'clean clause band')
    check({(2195-e)%8807 for e in support} &
          {(3296-e)%8807 for e in support} == {0}, 'anchor alignment')
    check(max(dc_digits)+max(support) == 8791, 'zero padding start')
    rho = 1 << 67
    d = 590069
    base = 1 << d
    DC = sum(c << (67*e) for e,c in dc_digits.items())
    DR = 1 << (67*42)
    MC = base-1-sum(1 << (67*e) for e in support if e != 1)-(2 << (67*1063))
    MF = 4+sum(mu << (67*t) for t in (4393,5495))
    MF += sum(1 << (67*t) for t,*_ in targets)
    MF += sum(((1 << 65)-1) << (67*e) for e in range(8792,8805))
    MF += ((1 << 19)-1) << (67*8805)
    check(0 < DC < base and 0 < MC < base-1 and 0 < MF < base-1,
          'native coefficient bounds')
    check(MC % 4 == 2 and MF % 8 == 4, 'native congruences')
    check(MC.bit_count()+MF.bit_count() == d and MF.bit_count() == 986,
          'mask population')
    mass = 988*(2*sum(coefficients.values())+6)
    threshold = max(4*mass+8, 2*mu+4, 2*((1 << 65)-1)+4, 16)
    check(threshold < rho and threshold >= (1 << 66), 'strict radix bound')
    ports = {'beta':base-1, 'K':DC+base*DR, 'MC':MC, 'MF_source':MF+base-1}
    binding = json.loads((HERE/'COEFFICIENT_BINDING.json').read_text())
    for entry in binding['materialization']['files']:
        packed = (HERE/entry['file']).read_bytes()
        raw = gzip.decompress(packed)
        check(int.from_bytes(raw,'little') == ports[entry['port']], 'literal port')
        check(sha256(raw).hexdigest() == entry['sha256'], 'port checksum')
        check(sha256(packed).hexdigest() == entry['gzip_sha256'], 'gzip checksum')
    lam = 581197
    step = lam-1
    check(factor(d) == {67:1,8807:1} and isprime(lam), 'controller primes')
    orders = {67:66,8807:4403,lam:581196}
    for p,o in orders.items():
        check(pow(2,d*o,p) == 1, 'claimed order')
        check(all(pow(2,d*(o//r),p) != 1 for r in factor(o)), 'minimal order')
        check(step % o == 0, 'step divisibility')
        check((base*base-1) % p != 0, 'quadratic controller unit')
        check((1+base*DC+base*base*(DR+1)) % p != 0, 'bracket controller unit')
    check(lcm(66,4403) == 290598 and pow(2,d*step,d) == 1, 'period modulo d')
    lift = pow(2,d*step,lam*lam)
    check(lift == 182964883980 and lift % lam == 1 and lift != 1, 'lifting valuation')
    baseline_checks = {}
    degree_checks = {}
    def trim(a):
        while len(a)>1 and a[-1] == 0:
            a.pop()
        return a
    def polynomial_op(a,b,op,p):
        if op == '*':
            c=[0]*(len(a)+len(b)-1)
            for k,x in enumerate(a):
                for l,y in enumerate(b):
                    c[k+l]=(c[k+l]+x*y)%p
            return trim(c)
        c=[0]*max(len(a),len(b))
        for k,x in enumerate(a):
            c[k]=x
        for k,y in enumerate(b):
            c[k]=(c[k]+(y if op == '+' else -y))%p
        return trim(c)
    for name,count in [('product67',67),('retained16_system59',59)]:
        old = json.loads((HERE/'source'/('baseline__'+name+'.json')).read_text())
        new = json.loads((HERE/(name+'.json')).read_text())
        check(old['source'] == new['source'], 'unchanged arithmetic source')
        check(len(new['source']) == count, 'arithmetic gate count')
        baseline_checks[name] = count
        records=[]
        for p in (1000000007,1000000009):
            values={w:[0,(i+1)%p] for i,w in enumerate(new['witnesses'])}
            for leaf,port in new['coefficient_binding']['aliases'].items():
                values[leaf]=[ports[port]%p]
            def get(x):
                return [x%p] if isinstance(x,int) else values[x]
            for register,op,a,b in new['source']:
                values[register]=polynomial_op(get(a),get(b),op,p)
            if name == 'product67':
                actual=[len(values[new['output']])-1]
                expected=[155]
                leading=[values[new['output']][-1]]
            else:
                residuals=[polynomial_op(get(a),get(b),'-',p) for a,b in new['comparisons']]
                actual=[len(r)-1 for r in residuals]
                expected=[22,18,24,7,2,22,6]
                leading=[r[-1] for r in residuals]
            check(actual == expected, 'actual-tuple modular degree lower bound')
            records.append(dict(modulus=p,projected_degrees=actual,leading_coefficients=leading))
        degree_checks[name]=records
    receipt = dict(status='PASS', source_files=len(pins['files']),
                   native_basis_checks=checks, one_bit_mutations=mutations,
                   exhaustive_small_complement_models=models,
                   b=67,L=8807,d=d,mask_population=986,mass=mass,
                   strict_carry_threshold=threshold,radix=rho,
                   controller_prime=lam,controller_lift=lift,
                   raw_bytes=sum(x['raw_bytes'] for x in binding['materialization']['files']),
                   unchanged_baseline_operations=baseline_checks,
                   literal_transition_rows=430,
                   actual_tuple_modular_degree_lower_bounds=degree_checks,
                   scope='Independent finite arithmetic audit; universal proof in PROOF.md.')
    (HERE/'INDEPENDENT_AUDIT.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__ == '__main__':
    main()
