#!/usr/bin/env python3
"""Mixed-radix Wang943 tuple with arbitrary-odd-factor rank control.

Standard library only. The finite checks certify the stated literal layout,
arithmetic bounds, and modular hypotheses; they are not a proof assistant
certificate of the inherited native compiler or of the K215 endpoint.
"""
from pathlib import Path
from hashlib import sha256
from math import gcd, isqrt, lcm
import gzip
import json

ROOT = Path(__file__).resolve().parent
PIN = '8c6eec9d19ef80538c8e61ff6e0180040583446a'
BITS, CELL = 121, 8801
D = BITS * CELL
T1, T2, H = 4393, 5495, 42
LAM, STEP = 2341, 2340
OFFSETS = (1023, 1013, 1003, 983)
ANCHORS = (1095, 1096, 2195, 3296)


def require(x, message):
    if not x:
        raise ValueError(message)


def factor(n):
    result = {}
    p = 2
    while p * p <= n:
        while n % p == 0:
            result[p] = result.get(p, 0) + 1
            n //= p
        p += 1
    if n > 1:
        result[n] = result.get(n, 0) + 1
    return result


def prime(n):
    return n >= 2 and all(n % p for p in range(2, isqrt(n) + 1))


def order(a, modulus):
    require(gcd(a, modulus) == 1, 'order needs a unit')
    phi = modulus
    for p in factor(modulus):
        phi = phi // p * (p - 1)
    n = phi
    for p in factor(phi):
        while n % p == 0 and pow(a, n // p, modulus) == 1:
            n //= p
    require(pow(a, n, modulus) == 1, 'order upper bound failed')
    require(all(pow(a, n // p, modulus) != 1 for p in factor(n)),
            'order minimality failed')
    return n


def reconstruct_tiles():
    for name, expected in (
        ('k215_transitions.json', '880741dcb49494aab7c1f7d7e453764d573f9704882502b5849f1e3a84b81755'),
        ('wang943_tiles.json', '66b55f1d11fca9fefc93b12fcfc8b4cabb75b08e9fd03311f9e894a1c5e5e81f'),
    ):
        require(sha256((ROOT / 'upstream' / name).read_bytes()).hexdigest() == expected,
                'literal source pin changed: ' + name)
    rows = json.loads((ROOT / 'upstream/k215_transitions.json').read_text())['transitions']
    require(len(rows) == 430 and len({(q, b) for q, b, *_ in rows}) == 430,
            '430 literal actions required')
    require(all(q in range(215) and b in (0, 1) and v in (0, 1)
                and m in (-1, 1) and t in range(216) for q, b, v, m, t in rows),
            'bad action domain')
    right = sorted({t for q, b, v, m, t in rows if m == 1})
    left = sorted({t for q, b, v, m, t in rows if m == -1})
    rr = {q: j + 6 for j, q in enumerate(right)}
    ll = {q: j + 6 + len(right) for j, q in enumerate(left)}
    hd = lambda q, b: 2 * (q + 1) + b
    groups = {
        'transitions': [(0, hd(q, b), rr[t], v) if m == 1
                        else (ll[t], hd(q, b), 0, v) for q, b, v, m, t in rows],
        'halt': [(0, hd(215, b), 0, hd(215, b)) for b in (0, 1)],
        'unchanged': [(0, b, 0, b) for b in (0, 1)],
        'arrive_right': [(rr[q], b, 0, hd(q, b)) for q in right for b in (0, 1)],
        'arrive_left': [(0, b, ll[q], hd(q, b)) for q in left for b in (0, 1)],
        'finish': [(0, c, 0, 438) for c in (0, 1, hd(215, 0), hd(215, 1))],
        'initialize': [(2, 434, 2, 0), (2, 435, 3, 1),
                       (3, 436, 4, hd(93, 0)), (4, 436, 4, 0)],
        'reset': [(1, 438, 1, c) for c in (434, 435, 436)],
        'seam': [(a, 437, b, 437) for a in (0, 1, 4) for b in (0, 1, 2)],
        'forbidden': [(5, 0, 0, 0)],
    }
    flat = [t for group in groups.values() for t in group]
    require(len(flat) == len(set(flat)) == 943, 'wrong tile language')
    start, forbidden = (2, 435, 3, 1), (5, 0, 0, 0)
    tiles = [start, forbidden] + sorted(set(flat) - {start, forbidden})
    require([list(t) for t in tiles] == json.loads(
        (ROOT / 'upstream/wang943_tiles.json').read_text()), 'tile order differs')
    return tiles, {name: len(value) for name, value in groups.items()}


def recipe():
    tiles, groups = reconstruct_tiles()
    weights = [1 << (10 + 2 * j) for j in range(44)]
    ce = {i: 1 + sum(weights[10 * t + j] for t, x in enumerate(tile)
                    for j in range(10) if (x + 512) >> j & 1)
          + sum(weights[40:]) for i, tile in enumerate(tiles)}
    ce.update({offset + j: weights[10 * t + j]
               for t, offset in enumerate(OFFSETS) for j in range(10)})
    ce.update({e: weights[40 + j] for j, e in enumerate(ANCHORS)})
    ce.update({1063: 0, 1064: 0})
    E = set(ce)
    mu = 1022 + sum(weights)
    dc = {e: 1 for e in (30, 62, 1100, 2200)}
    for e, c in ce.items():
        if c:
            for T in (T1, T2):
                dc[T - e] = dc.get(T - e, 0) + c
    targets = [(1013 + j, {983 + j}, set(), {1013 + j}) for j in range(10)]
    targets += [(1065 + j, {1003 + j}, {1023 + j}, set()) for j in range(10)]
    targets += [(2195, {1095}, set(), {2195}), (3296, {1096}, set(), {3296})]
    pads = {8792 + j: (1 << 119) - 1 for j in range(7)}
    pads[8799] = (1 << 27) - 1
    return tiles, groups, ce, E, mu, dc, targets, pads


def check_geometry(data):
    tiles, groups, ce, E, mu, dc, targets, pads = data
    checks = 0
    for t, at0, at1, at2 in targets:
        for e in E:
            require(dc.get(t - e, 0) == int(e in at0), 'DC overlap contaminated')
            require(int(e + H == t) == int(e in at1), 'DR overlap contaminated')
            require(int(e == t) == int(e in at2), 'temporal overlap contaminated')
            checks += 3
    for T in (T1, T2):
        for e in E:
            require(dc.get(T - e, 0) == ce[e], 'clause contaminated')
            require(e + H != T, 'DR reaches clause')
            checks += 2
    require({(T1-e) % CELL for e in E}.isdisjoint({(T2-e) % CELL for e in E}),
            'no clean clause band')
    require({(2195-e) % CELL for e in E} & {(3296-e) % CELL for e in E} == {0},
            'anchor alignment not unique')
    mass = (len(E) + 2) * (2 * sum(ce.values()) + 6)
    threshold = max(4 * mass + 8, 2 * mu + 4, 16)
    require(threshold < 1 << BITS, 'uniform carry bound failed')
    require(threshold >= 1 << (BITS - 2), '121 is not the least odd width')
    maximum = max(max(dc) + max(E), H + max(E), max(E))
    require(maximum == 8791 and min(pads) > maximum, 'padding is not external')
    require(max(pads) < CELL and 2 * max(pads.values()) + 4 < 1 << BITS,
            'padding mask exceeds cell bound')
    require(2 * mu.bit_count() + len(targets) + 1
            + sum(x.bit_count() for x in pads.values()) == len(E) == 989,
            'population balance failed')
    require([n for n in range(944) if n & 1022 == 0] == [0, 1],
            'low selector-count decoder failed')
    for n in (0, 1):
        for tile_bit in (0, 1):
            require([c for c in (0, 1) if (n * tile_bit + c) & 1 == 0]
                    == [n * tile_bit], 'Boolean copy decoder failed')
    for i, tile in enumerate(tiles):
        clause = ce[i] + sum(ce[OFFSETS[t] + j] for t, x in enumerate(tile)
                             for j in range(10) if (x + 512) >> j & 1)
        clause += sum(ce[e] for e in ANCHORS)
        require(clause & mu == 0, 'one-tile clause completeness failed')
    return dict(status='PASS', native_basis_checks=checks, tile_groups=groups,
                support_size=len(E), clause_mask_population=mu.bit_count(),
                external_padding_population=sum(x.bit_count() for x in pads.values()),
                maximum_unshifted_exponent=maximum, mass_bits=mass.bit_length(),
                threshold_bits=threshold.bit_length(), threshold=str(threshold),
                clean_clause_bands=True, unique_anchor_alignment=True,
                one_tile_clause_checks=len(tiles), selector_counts_checked=944)


def check_padding(dc):
    require(D == 11**2 * 13 * 677 and prime(LAM), 'factorization/primality failed')
    require(gcd(D, LAM) == 1 and STEP == LAM - 1, 'bad padding prime')
    orders = {str(m): order(pow(2, D, m), m) for m in (121, 13, 677, LAM)}
    require(orders == {'121': 10, '13': 12, '677': 52, str(LAM): 60},
            'unexpected multiplicative orders')
    require(lcm(orders['121'], orders['13'], orders['677']) == 780,
            'bad fixed-factor order')
    require(all(STEP % v == 0 for v in orders.values()), 'step is not a common period')
    require(pow(2, D * STEP, D) == 1, 'step does not fix d')
    witness = pow(2, D * STEP, LAM**2)
    require(witness == 2556373 and witness % LAM == 1 and witness != 1,
            'valuation one failed')
    rows = []
    for p in (11, 13, 677, LAM):
        rho, B = pow(2, BITS, p), pow(2, D, p)
        DC = sum((c % p) * pow(rho, e, p) for e, c in dc.items()) % p
        DR = pow(rho, H, p)
        qfactor = (B * B - 1) % p
        bracket = (1 + B * DC + B * B * (DR + 1)) % p
        require(qfactor and bracket, 'actual-rank multiplier is not a unit')
        rows.append(dict(prime=p, B=B, DC=DC, DR=DR,
                         q_squared_minus_one=qfactor, bracket=bracket))
    return dict(status='PASS', d_factors={'11': 2, '13': 1, '677': 1},
                orders=orders, order_mod_d=780, padding_prime=LAM, step=STEP,
                valuation=1, valuation_witness=witness, unit_residues=rows)


def materialize(data):
    _, _, _, E, mu, dc, targets, pads = data
    B = 1 << D
    DC = sum(c << (BITS * e) for e, c in dc.items())
    DR = 1 << (BITS * H)
    MF0 = 4 + (mu << (BITS * T1)) + (mu << (BITS * T2))
    MF0 += sum(1 << (BITS * t) for t, *_ in targets)
    MF0 += sum(c << (BITS * e) for e, c in pads.items())
    MC = B - 1 - sum(1 << (BITS * e) for e in E if e != 1) - (2 << (BITS * 1063))
    require(0 < MC < B - 1 and 0 < MF0 < B - 1 and DC < B,
            'coefficient ranges failed')
    require(MC % 4 == 2 and MF0 % 8 == 4, 'low congruences failed')
    require(MC.bit_count() + MF0.bit_count() == D and MF0.bit_count() == 989,
            'actual coefficient population balance failed')
    ports = dict(beta=B-1, K=DC+B*DR, MC=MC, MF_source=MF0+B-1)
    out = ROOT / 'payloads'
    out.mkdir(exist_ok=True)
    files = []
    for name, value in ports.items():
        raw = value.to_bytes((value.bit_length() + 7) // 8, 'little')
        compressed = gzip.compress(raw, mtime=0)
        require(int.from_bytes(gzip.decompress(compressed), 'little') == value,
                'payload round trip failed')
        (out / (name + '.bin')).write_bytes(raw)
        (out / (name + '.bin.gz')).write_bytes(compressed)
        files.append(dict(port=name, file='payloads/' + name + '.bin.gz',
                          bit_length=value.bit_length(), raw_bytes=len(raw),
                          gzip_bytes=len(compressed), sha256=sha256(raw).hexdigest(),
                          gzip_sha256=sha256(compressed).hexdigest()))
    return files, dict(MC_population=MC.bit_count(), MF_native_population=MF0.bit_count(),
                       MC_mod4=MC % 4, MF_native_mod8=MF0 % 8)


def main():
    data = recipe()
    geometry = check_geometry(data)
    padding = check_padding(data[5])
    files, masks = materialize(data)
    binding = dict(instance='wang943-mixed-121x8801', source_commit=PIN,
                   b=BITS, L=CELL, d=D, B='2^1064921', rho='2^121',
                   T1=T1, T2=T2, spatial_transport=H,
                   ports={'Bm1': 'beta', 'Kconstant': 'K', 'MC': 'MC', 'MF': 'MF_source'},
                   warning='MF_source is already shifted by B-1. Rebind all four ports together.',
                   geometry=geometry, padding=padding, mask_checks=masks, files=files,
                   total_raw_bytes=sum(f['raw_bytes'] for f in files),
                   total_gzip_bytes=sum(f['gzip_bytes'] for f in files),
                   ordinary_mathematical_adapter=True, new_formal_certificate=False,
                   scope='Finite exact checks, not an end-to-end proof of compiler semantics.')
    (ROOT / 'COEFFICIENT_BINDING.json').write_text(json.dumps(binding, indent=2) + '\n')
    print(json.dumps(binding, indent=2))


if __name__ == '__main__':
    main()

