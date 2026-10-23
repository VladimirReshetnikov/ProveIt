#!/usr/bin/env python3
"""Independent audit of the nonzero-word native coefficient instance.

This auditor never imports the builder. It reads the pinned tile-list data and
the delivered literal integers, rederives the tuple, and exhausts every scalar
basis identity needed by the inherited native compiler. It does not certify
the inherited unbounded compiler or K215 calibration.
"""
from pathlib import Path
from collections import Counter
from hashlib import sha256
from math import gcd, isqrt, lcm
import gzip
import json
import sys


def require(ok, msg):
    if not ok:
        raise ValueError(msg)


def factor(n):
    r = {}
    p = 2
    while p * p <= n:
        while n % p == 0:
            r[p] = r.get(p, 0) + 1
            n //= p
        p += 1
    if n > 1:
        r[n] = 1
    return r


def certified_order(a, m):
    phi = m
    for p in factor(m):
        phi = phi // p * (p - 1)
    r = phi
    for p in factor(phi):
        while r % p == 0 and pow(a, r // p, m) == 1:
            r //= p
    require(pow(a, r, m) == 1, 'failed order')
    require(all(pow(a, r // p, m) != 1 for p in factor(r)), 'nonminimal order')
    return r


def audit(directory):
    binding = json.loads((directory / 'COEFFICIENT_BINDING.json').read_text())
    raw_tiles = (directory / 'wang943_tiles.json').read_bytes()
    tiles = json.loads(raw_tiles)
    canonical_tiles = json.dumps(tiles, separators=(',', ':')).encode() + b'\n'
    require(sha256(canonical_tiles).hexdigest() ==
            '66b55f1d11fca9fefc93b12fcfc8b4cabb75b08e9fd03311f9e894a1c5e5e81f',
            'tile language changed')
    require(len(tiles) == 943 and len(set(map(tuple, tiles))) == 943, 'tile count')
    require(tiles[0] == [2, 435, 3, 1], 'Start ordering')
    require(tiles[1] == [5, 0, 0, 0], 'Forbidden ordering')

    widths = (8, 9, 8, 9)
    starts = (0, 8, 17, 25)
    offsets = (1023, 1013, 1003, 983)
    anchors = (1022, 1042, 2107)
    b, cell = 107, 6385
    d, lam, step = b * cell, 135257, 135256
    T1, T2, shift = 3202, 4268, 50
    weights = [2 ** (10 + 2 * i) for i in range(37)]
    require(d == 683195 and factor(d) == {5: 1, 107: 1, 1277: 1}, 'base')
    require(factor(lam) == {lam: 1}, 'padding prime')

    ce = {}
    for i, tile in enumerate(tiles):
        value = 1 + sum(weights[34:])
        for slot, label in enumerate(tile):
            code = label + 1
            require(1 <= code < 2 ** widths[slot], 'nonzero word capacity')
            for j in range(widths[slot]):
                if code & (1 << j):
                    value += weights[starts[slot] + j]
        ce[i] = value
    for slot in range(4):
        for j in range(widths[slot]):
            key = offsets[slot] + j
            require(key not in ce, 'overlapping copy support')
            ce[key] = weights[starts[slot] + j]
    for j, key in enumerate(anchors):
        require(key not in ce, 'overlapping anchor support')
        ce[key] = weights[34 + j]
    for key in (1063, 1064):
        require(key not in ce, 'overlapping dummy support')
        ce[key] = 0
    E = set(ce)
    require(len(E) == 982 and max(E) == 2107, 'native support')
    mu = 1022 + sum(weights)
    require(mu.bit_count() == 46, 'clause mask population')
    require([n for n in range(944) if n & 1022 == 0] == [0, 1], 'selector mask')
    require([(x, y) for x in (0, 1) for y in (0, 1) if (x + y) % 2 == 0]
            == [(0, 0), (1, 1)], 'bitwise equality')

    dc = Counter({s: 1 for s in (30, 70, 20, 1085)})
    for e, coefficient in ce.items():
        for t in (T1, T2):
            dc[t - e] += coefficient
    dc = {e: c for e, c in dc.items() if c}
    targets = []
    for j in range(9):
        targets.append((1013 + j, 983 + j, None, 1013 + j))
    for j in range(8):
        targets.append((1073 + j, 1003 + j, 1023 + j, None))
    targets.extend([(1042, 1022, None, 1042), (2107, 1022, None, 2107)])
    basis_checks = 0
    for target, current, spatial, temporal in targets:
        for e in E:
            require(dc.get(target - e, 0) == (e == current), 'current target contamination')
            require((e + shift == target) == (e == spatial), 'spatial target contamination')
            require((e == target) == (e == temporal), 'temporal target contamination')
            basis_checks += 3
    for target in (T1, T2):
        for e in E:
            require(dc.get(target - e, 0) == ce[e], 'clause target contamination')
            require(e + shift != target, 'spatial clause contamination')
            basis_checks += 2
    require(basis_checks == 59902, 'basis count')
    require({(T1 - e) % cell for e in E}.isdisjoint({(T2 - e) % cell for e in E}),
            'both clause bands may be dirty')
    require({(1042 - e) % cell for e in E} & {(2107 - e) % cell for e in E} == {0},
            'anchor ambiguity')
    require([(a, c) for a in E for c in E if c - a == 1065] == [(1042, 2107)],
            'nonunique noncircular anchor difference')
    require(2 * max(E) < cell, 'circular wrap risk')
    require(min(dc) > 0 and max(dc) + max(E) == 6375, 'field bounds')

    padding = {e: (1 << 105) - 1 for e in range(6376, 6384)}
    padding[6384] = (1 << 30) - 1
    require(sum(x.bit_count() for x in padding.values()) == 870, 'padding population')
    require(min(padding) > max(dc) + max(E), 'padding current contamination')
    require(min(padding) > max(E) + shift, 'padding spatial contamination')
    require(max(padding) < cell, 'padding outside cell')
    mass = (len(E) + 2) * (2 * sum(ce.values()) + 6)
    threshold = max(4 * mass + 8, 2 * mu + 4, 2 * max(padding.values()) + 4, 16)
    require(threshold < 1 << b, 'uniform carry bound')

    B = 1 << d
    DC = sum(c << (b * e) for e, c in dc.items())
    DR = 1 << (b * shift)
    MC = B - 1 - sum(1 << (b * e) for e in E if e != 1) - (2 << (b * 1063))
    MF_native = 4 + (mu << (b * T1)) + (mu << (b * T2))
    MF_native += sum(1 << (b * t) for t, *_ in targets)
    MF_native += sum(c << (b * e) for e, c in padding.items())
    require(0 < DC < B and 0 < MC < B - 1 and 0 < MF_native < B - 1, 'port bounds')
    require(MC.bit_count() + MF_native.bit_count() == d, 'population balance')
    require(MF_native.bit_count() == 982, 'high population')
    require(MC % 4 == 2 and MF_native % 8 == 4, 'low congruences')
    ports = {'beta': B - 1, 'K': DC + B * DR, 'MC': MC, 'MF_source': MF_native + B - 1}
    port_checks = []
    for name, value in ports.items():
        raw = (directory / 'coefficients' / (name + '.bin')).read_bytes()
        packed = gzip.decompress((directory / 'coefficients' / (name + '.bin.gz')).read_bytes())
        require(raw == packed, 'raw/gzip mismatch')
        require(int.from_bytes(raw, 'little') == value, 'literal port mismatch: ' + name)
        require(len(raw) == (value.bit_length() + 7) // 8, 'nonminimal port representation')
        record = next(r for r in binding['materialization']['files'] if r['port'] == name)
        require(sha256(raw).hexdigest() == record['sha256'], 'binding digest')
        port_checks.append({'port': name, 'bits': value.bit_length(), 'bytes': len(raw),
                            'sha256': sha256(raw).hexdigest()})

    moduli = (5, 107, 1277, lam)
    orders = {p: certified_order(B % p, p) for p in moduli}
    require(lcm(*(orders[p] for p in moduli[:-1])) == 67628, 'period modulo d')
    require(all(step % order == 0 for order in orders.values()), 'padding period')
    require(pow(B, step, d) == 1, 'period modulo actual d')
    lifted = pow(B, step, lam * lam)
    require(lifted != 1 and lifted % lam == 1, 'lifting valuation')
    rows = []
    for p in moduli:
        bb, cc, rr = B % p, DC % p, DR % p
        qfactor = (bb * bb - 1) % p
        bracket = (1 + bb * cc + bb * bb * (rr + 1)) % p
        require(qfactor != 0 and bracket != 0, 'rank-control multiplier nonunit')
        rows.append({'prime': p, 'B': bb, 'DC': cc, 'DR': rr,
                     'B_squared_minus_one': qfactor, 'bracket': bracket})
    require(rows == binding['padding_controller']['unit_residues'], 'unit certificate mismatch')

    return {'status': 'PASS', 'scope': 'Independent literal reconstruction and exact finite interface audit; inherited universal theorems reviewed separately, not kernel checked.',
            'tile_language_unchanged': True, 'nonzero_codes_checked': 4 * len(tiles),
            'support_size': len(E), 'basis_convolution_checks': basis_checks,
            'clause_rotation_intersection_empty': True, 'anchor_rotation_intersection': [0],
            'maximum_unshifted_exponent': 6375, 'padding_population': 870,
            'mass_bits': mass.bit_length(), 'carry_threshold_bits': threshold.bit_length(),
            'radix_bits': b, 'base_exponent': d, 'ports': port_checks,
            'raw_bytes_total': sum(r['bytes'] for r in port_checks),
            'multiplicative_orders': orders, 'lifted_power': lifted,
            'controller_units': rows}


if __name__ == '__main__':
    path = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(__file__).resolve().parent
    result = audit(path)
    target = Path(sys.argv[2]) if len(sys.argv) > 2 else Path(__file__).with_name('NONZERO_COEFFICIENTS_INDEPENDENT_AUDIT.json')
    target.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))
