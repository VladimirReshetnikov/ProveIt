#!/usr/bin/env python3
"""Build the complete Wang943/529/12031 coefficient tuple.

The tile language and exponent positions are from ProveIt's package 19
(ae3007ca4467011e0e051c84acb4a1dd13971b0e).  This adaptation removes the
power-of-five rounding by the fixed-factor padding proof in this delivery.
No dependency outside Python's standard library is required.

Finite tests check the literal recipe, geometry and arithmetic certificates.
They do not check an infinite computation or replace the compiler proof.
"""
from pathlib import Path
from hashlib import sha256
from math import gcd, isqrt, lcm
import gzip
import json

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'coefficients'
PIN = 'ae3007ca4467011e0e051c84acb4a1dd13971b0e'
MACHINE_SHA = 'fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090'
B_BITS, CELL = 529, 12031
D_BITS = B_BITS * CELL
PADDING_PRIME = 452453
STEP = 452452
T1, T2, SHIFT = 7631, 8733, 5497
ANCHORS = (1095, 1096, 2195, 3296)
OFFSETS = (1023, 1013, 1003, 983)
BARE = (30, 5517, 1100, 2200)


def require(value, message):
    if not value:
        raise ValueError(message)


def digest(data):
    return sha256(data).hexdigest()


def factor(n):
    out = []
    p = 2
    while p * p <= n:
        if n % p == 0:
            out.append(p)
            while n % p == 0:
                n //= p
        p += 1
    if n > 1:
        out.append(n)
    return out


def prime(n):
    return n >= 2 and all(n % j for j in range(2, isqrt(n) + 1))


def order(a, modulus, phi):
    result = phi
    for p in factor(phi):
        while result % p == 0 and pow(a, result // p, modulus) == 1:
            result //= p
    require(pow(a, result, modulus) == 1, 'bad multiplicative order')
    require(all(pow(a, result // p, modulus) != 1 for p in factor(result)),
            'order certificate is not minimal')
    return result


def machine_and_tiles():
    source = (ROOT / 'upstream/k215.tm').read_bytes()
    require(digest(source) == MACHINE_SHA, 'machine differs from the literal K215 pin')
    rows = []
    for line in source.decode().splitlines():
        if line and not line.startswith('#'):
            q, bit, written, move, target = line.split()
            rows.append((int(q), int(bit), int(written), move, int(target)))
    require(len(rows) == 430 and len({(q, b) for q, b, *_ in rows}) == 430,
            'machine must have 430 distinct actions')
    require(all(m in ('L', 'R') for _, _, _, m, _ in rows), 'unexpected movement')
    right = sorted({t for _, _, _, m, t in rows if m == 'R'})
    left = sorted({t for _, _, _, m, t in rows if m == 'L'})
    sr = {q: 6 + j for j, q in enumerate(right)}
    sl = {q: 6 + len(right) + j for j, q in enumerate(left)}
    def head(q, b):
        return 2 * (q + 1) + b
    O, HB, PL, PQ, PR, BAD = range(6)
    L, Q, R, V, H = 434, 435, 436, 437, 438
    groups = {
        'working': [(O, head(q,b), sr[t], v) if m == 'R'
                    else (sl[t], head(q,b), O, v) for q,b,v,m,t in rows],
        'halt': [(O, head(215,b), O, head(215,b)) for b in (0,1)],
        'headless': [(O,b,O,b) for b in (0,1)],
        'arrive_right': [(sr[q],b,O,head(q,b)) for q in right for b in (0,1)],
        'arrive_left': [(O,b,sl[q],head(q,b)) for q in left for b in (0,1)],
        'finish': [(O,c,O,H) for c in (0,1,head(215,0),head(215,1))],
        'phase': [(PL,L,PL,0),(PL,Q,PQ,1),(PQ,R,PR,head(93,0)),(PR,R,PR,0)],
        'horizontal': [(HB,H,HB,p) for p in (L,Q,R)],
        'vertical': [(a,V,b,V) for a in (O,HB,PR) for b in (O,HB,PL)],
        'forbidden': [(BAD,0,O,0)]
    }
    flat = [t for group in groups.values() for t in group]
    require(len(flat) == len(set(flat)) == 943, 'tile enumeration mismatch')
    start, forbidden = (PL,Q,PQ,1), (BAD,0,O,0)
    tiles = [start, forbidden] + sorted(set(flat) - {start, forbidden})
    inherited = json.loads((ROOT / 'upstream/wang943_tiles.json').read_text())
    require([list(t) for t in tiles] == inherited, 'tiles differ from package 19')
    return tiles, {k: len(v) for k, v in groups.items()}


def recipe():
    tiles, counts = machine_and_tiles()
    A = 1024
    copies = {(s,j): OFFSETS[s] + j for s in range(4) for j in range(10)}
    coefficients = {
        i: 1 + sum((((edge+512) >> j) & 1) * A**(1+10*s+j)
                   for s,edge in enumerate(tile) for j in range(10))
           + sum(A**j for j in range(41,45))
        for i,tile in enumerate(tiles)
    }
    coefficients.update({e: A**(1+10*s+j) for (s,j),e in copies.items()})
    coefficients.update({e: A**(41+j) for j,e in enumerate(ANCHORS)})
    coefficients.update({1063: 0, 1064: 0})
    support = set(coefficients)
    mu = A-2 + sum((A-3)*A**j for j in range(1,45)) + ((1<<78)-1)*(1<<450)
    dc = {e: 1 for e in BARE}
    for e,c in coefficients.items():
        if c:
            for band in (T1,T2):
                dc[band-e] = dc.get(band-e,0) + c
    targets = [(copies[1,j], {copies[3,j]}, set(), {copies[1,j]}) for j in range(10)]
    targets += [(SHIFT+copies[0,j], {copies[2,j]}, {copies[0,j]}, set()) for j in range(10)]
    targets += [(2195,{1095},set(),{2195}),(3296,{1096},set(),{3296})]
    return tiles, counts, copies, coefficients, support, mu, dc, targets


def check_geometry(data):
    _, counts, copies, ce, support, mu, dc, targets = data
    checks = 0
    for target, at0, at1, at2 in targets:
        for e in support:
            require(dc.get(target-e,0) == int(e in at0), 'DC target contamination')
            require(int(e+SHIFT == target) == int(e in at1), 'DR target contamination')
            require(int(e == target) == int(e in at2), 'temporal target contamination')
            checks += 3
    for band in (T1,T2):
        for e in support:
            require(dc.get(band-e,0) == ce[e], 'clause target contamination')
            require(e+SHIFT != band, 'DR contaminates a clause')
            checks += 2
    expanded = support | {1064}
    require({(T1-e)%CELL for e in expanded}.isdisjoint({(T2-e)%CELL for e in expanded}),
            'two rotated clause bands can be dirty simultaneously')
    anchors = {(2195-e)%CELL for e in support} & {(3296-e)%CELL for e in support}
    require(anchors == {0}, 'anchor alignment is not unique')
    require(min(dc) > 0 and max(dc)+max(support) < CELL, 'DC cell overflow')
    require(SHIFT+max(support) < CELL, 'DR cell overflow')
    require(T1 > max(support) and T2 > max(support), 'negative reflected support')
    require(len(support) == 2*mu.bit_count()+len(targets)+1 == 989,
            'mask population identity fails')
    mass = (len(support)+2)*(2*sum(ce.values())+6)
    threshold = max(4*mass+8, 2*mu+4, 16)
    require(1<<B_BITS >= threshold, 'insufficient radix carry bound')
    require(1<<(B_BITS-2) < threshold, 'claimed minimum odd bit count is wrong')
    require(B_BITS%2 == CELL%2 == 1, 'radices must have odd exponents')
    return dict(status='PASS', basis_convolution_checks=checks, tile_group_counts=counts,
                support_size=len(support), mu_population=mu.bit_count(),
                threshold_bits=threshold.bit_length(), carry_mass_bits=mass.bit_length(),
                max_unshifted_exponent=max(dc)+max(support), anchor_intersection=[0],
                rotation_hit_sets_disjoint=True)


def check_padding(dc):
    require(D_BITS == 23**2 * 53 * 227, 'bad factorization of d')
    require(all(prime(p) for p in (23,53,227,PADDING_PRIME)), 'primality certificate failed')
    orders = {str(p): order(pow(2,D_BITS,p),p,phi)
              for p,phi in ((529,506),(53,52),(227,226),(PADDING_PRIME,PADDING_PRIME-1))}
    td = lcm(*(orders[str(p)] for p in (529,53,227)))
    require(td == 64636 and STEP == lcm(td,orders[str(PADDING_PRIME)]), 'bad common period')
    require(STEP == PADDING_PRIME-1, 'step must leave a fixed positive fraction of cells free')
    require(pow(2,D_BITS*STEP,D_BITS) == 1, 'period does not fix d')
    valuation_witness = pow(2,D_BITS*STEP,PADDING_PRIME**2)
    require(valuation_witness % PADDING_PRIME == 1 and valuation_witness != 1,
            'padding valuation must be exactly one')
    rows = []
    for p in (23,53,227,PADDING_PRIME):
        rho, B = pow(2,B_BITS,p), pow(2,D_BITS,p)
        DC = sum((c%p)*pow(rho,e,p) for e,c in dc.items())%p
        DR = pow(rho,SHIFT,p)
        q_factor = (B*B-1)%p
        bracket = (1+B*DC+B*B*(DR+1))%p
        require(q_factor != 0 and bracket != 0, 'dummy-control coefficient is not a unit')
        rows.append(dict(prime=p,B=B,DC=DC,DR=DR,q_squared_minus_one=q_factor,bracket=bracket))
    return dict(status='PASS', d_factorization={'23':2,'53':1,'227':1},
                multiplicative_orders=orders, order_mod_d=td,
                padding_prime=PADDING_PRIME, step=STEP, valuation=1,
                B_power_step_mod_prime_squared=valuation_witness, unit_residues=rows)


def materialize(data):
    _, _, copies, _, support, mu, dc, _ = data
    B = 1 << D_BITS
    DC = sum(c << (B_BITS*e) for e,c in dc.items())
    DR = 1 << (B_BITS*SHIFT)
    MF0 = (mu << (B_BITS*T1)) + (mu << (B_BITS*T2))
    MF0 += sum(1 << (B_BITS*copies[1,j]) for j in range(10))
    MF0 += sum(1 << (B_BITS*(SHIFT+copies[0,j])) for j in range(10))
    MF0 += (1 << (B_BITS*2195)) + (1 << (B_BITS*3296))
    MF_native = MF0+4
    MC = B-1-sum(1 << (B_BITS*e) for e in support if e != 1)-2*(1 << (B_BITS*1063))
    require(0 < MC < B-1 and 0 < MF_native < B-1, 'native mask range failed')
    require(MC%4 == 2 and MF_native%8 == 4, 'native mask residues failed')
    require(MC.bit_count()+MF_native.bit_count() == D_BITS, 'materialized population failed')
    values = {'beta': B-1, 'K0': DC+B*DR, 'MC': MC, 'MF': MF_native+B-1}
    OUT.mkdir(parents=True,exist_ok=True)
    records = []
    for port,value in values.items():
        raw = value.to_bytes((value.bit_length()+7)//8,'little')
        compressed = gzip.compress(raw,compresslevel=9,mtime=0)
        (OUT/(port+'.bin.gz')).write_bytes(compressed)
        require(int.from_bytes(gzip.decompress(compressed),'little') == value,'binary round trip failed')
        records.append(dict(port=port,file=port+'.bin.gz',encoding='minimal unsigned little-endian, gzip',
                            bits=value.bit_length(),bytes=len(raw),gzip_bytes=len(compressed),sha256=digest(raw),
                            gzip_sha256=digest(compressed)))
    return records, dict(native_low_population=MC.bit_count(),native_high_population=MF_native.bit_count(),
                         native_low_mod4=MC%4,native_high_mod8=MF_native%8)


def main():
    data = recipe()
    geometry = check_geometry(data)
    padding = check_padding(data[-2])
    files, mask_checks = materialize(data)
    manifest = dict(instance='wang943-minodd-529x12031',source_commit=PIN,tiles=943,
                    radix_bits=B_BITS,cell_length=CELL,d=D_BITS,B='2^6364399',
                    ports={'beta':'B-1','K0':'DC+B*DR','MC':'native low mask',
                           'MF':'native high mask + B - 1'},
                    files=files,geometry=geometry,padding=padding,mask_checks=mask_checks,
                    scope='Exact materialization and finite audits; semantic correctness is an ordinary mathematical proof.')
    (OUT/'COEFFICIENT_BINDING.json').write_text(json.dumps(manifest,indent=2)+'\n')
    print(json.dumps(dict(status='PASS',instance=manifest['instance'],d=D_BITS,
                         total_raw_bytes=sum(f['bytes'] for f in files),
                         total_gzip_bytes=sum(f['gzip_bytes'] for f in files),
                         files=files,geometry=geometry,padding=padding),indent=2))


if __name__ == '__main__':
    main()
