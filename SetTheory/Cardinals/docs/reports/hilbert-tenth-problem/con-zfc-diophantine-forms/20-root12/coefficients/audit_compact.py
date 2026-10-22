"""Independent audit of the frozen T4-4094 coefficient tuple.

Reads literal transition and tile data; does not import the construction code.
Pass --materialize only after reviewing COEFFICIENT_PROOF.md. Binary files are
unsigned, minimal-width, big-endian, with zero padding in the first byte.
"""
import argparse
import hashlib
import itertools
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def require(test, why):
    if not test:
        raise AssertionError(why)


def build():
    source = ROOT / "sources/k215_transitions.json"
    require(hashlib.sha256(source.read_bytes()).hexdigest() ==
            '880741dcb49494aab7c1f7d7e453764d573f9704882502b5849f1e3a84b81755',
            "pinned transition input")
    rows = json.loads(source.read_text())["transitions"]
    delta = {(q, bit): (write, move, target) for q, bit, write, move, target in rows}
    delta.update({(215, bit): (bit, 0, 215) for bit in (0, 1)})
    incoming = {q: [] for q in range(216)}
    for q, bit, write, move, target in rows:
        incoming[target].append((move, write))
    start, excluded = (434, 435, 436, 1), (438, 0, 0, 438)
    phases = {434, 435, 436}

    def state(x):
        return x//2-1 if 2 <= x < 434 else 0 if x == 435 else None

    def tape(x):
        return x % 2 if x < 434 else 0

    def old_valid(tile):
        l, c, r, n = tile
        if sum(state(x) is not None for x in (l, c, r)) > 1:
            return False
        if (c == 437) != (n == 437) or c == r == 437 or c == n == 438:
            return False
        if c != 437 and r != 437 and (c == 438) != (r == 438):
            return False
        if c == 437:
            return True
        if c == 438:
            return n in phases
        if c in phases:
            if l == 437 and c != 434 or r == 437 and c != 436:
                return False
            if r != 437 and (c, r) not in {(434, 434), (434, 435), (435, 436), (436, 436)}:
                return False
        q = state(c)
        if q is not None:
            motion = delta[q, tape(c)][1]
            if motion == -1 and l == 437 or motion == 1 and r == 437:
                return False
        if n == 438:
            return q is None or q == 215
        if n in phases or l == 438 or r == 438:
            return False
        written = tape(c) if q is None else delta[q, tape(c)][0]
        arrivals = [delta[state(x), tape(x)][2] for x, motion in ((l, 1), (c, 0), (r, -1))
                    if state(x) is not None and delta[state(x), tape(x)][1] == motion]
        return len(arrivals) <= 1 and (tape(n), state(n)) == (written, arrivals[0] if arrivals else None)

    def edge(x, y):
        if x == 437:
            return y in {0, 434, 438}
        if y == 437:
            return x in {0, 436, 438}
        if x == 438 or y == 438:
            return x == y == 438
        if x in phases or y in phases:
            return (x, y) in {(434, 434), (434, 435), (435, 436), (436, 436)}
        return True

    def additional_filters(tile):
        if tile == excluded:
            return True
        l, c, r, n = tile
        if not edge(l, c) or not edge(c, r) or l == r == 437:
            return False
        if c == 438:
            return (l != 437 or n == 434) and (r != 437 or n == 436)
        if c == 437:
            return True
        if c in phases and n == 438:
            return False
        if c not in phases:
            if l == 437 and (r not in (0, 1) or n not in (0, 438)):
                return False
            if r == 437 and (l not in (0, 1) or n not in (0, 438)):
                return False
        if n == 438 and not all(x in (0, 1, 432, 433, 437) for x in (l, c, r)):
            return False
        for pos, x in enumerate((l, c, r)):
            if 2 <= x < 434:
                if not any(pos - move not in range(3) or tile[pos - move] == write
                           for move, write in incoming[x // 2 - 1]):
                    return False
        return True

    headless = [s for s in range(439) if state(s) is None]
    triples = set(itertools.product(headless, repeat=3))
    for position in range(3):
        for head in (s for s in range(439) if state(s) is not None):
            for rest in itertools.product(headless, repeat=2):
                triple = list(rest)
                triple.insert(position, head)
                triples.add(tuple(triple))
    require(len(triples) == 46980, "one-head triple census")
    accepted = []
    for l, c, r in sorted(triples):
        if (l, c, r) != excluded[:3] and (not edge(l, c) or not edge(c, r) or l == r == 437):
            continue
        for n in range(439):
            tile = (l, c, r, n)
            if additional_filters(tile) and old_valid(tile):
                accepted.append(tile)
    require(start in accepted and excluded in accepted, "distinguished tile validity")
    tiles = [start, excluded] + [t for t in accepted if t not in (start, excluded)]
    delivered = list(map(tuple, json.loads((ROOT / "tiles4094.json").read_text())))
    require(tiles == delivered, "independent filter/order mismatch")
    require(tiles[:2] == [start, excluded] and len(tiles) == 4094, "marked tile census")

    k, a, ell = 4094, 11, 12
    A, b, circumference = 1 << ell, 625, 78125
    d = b * circumference
    copies = [k + 8*a, k + 7*a, k + 6*a, k + 4*a]
    dummy, M = k + 12*a, k + 15*a + 1
    anchors = [M, M+a+1, M+2*a, 2*M+4*a+1]
    emax = max(anchors)
    anchor_shifts = [anchors[2] - anchors[0], anchors[3] - anchors[1]]
    Hc = emax + anchor_shifts[1] + 3*a + 1
    T1, T2 = Hc + 2*emax + a + 1, Hc + 4*emax + a + 5
    bare = [3*a, Hc+a] + anchor_shifts
    support = set(range(k)) | {p+t for p in copies for t in range(a)} | {dummy} | set(anchors)
    require(len(support) == 4143, "support cardinality")
    mu = A - 2 + sum(1 << (ell*j) for j in range(1, 49))
    vector = lambda s: [(s >> t) & 1 for t in range(9)] + [1, 0]
    coeff = {}
    for j, tile in enumerate(tiles):
        exponents = [0] + [1 + a*slot+t for slot, s in enumerate(tile)
                            for t, bit in enumerate(vector(s)) if bit]
        exponents += [45, 46, 47, 48]
        coeff[j] = sum(1 << (ell*t) for t in exponents)
    for slot, p in enumerate(copies):
        for t in range(a):
            coeff[p+t] = 1 << (ell*(1 + a*slot+t))
    for j, p in enumerate(anchors):
        coeff[p] = 1 << (ell*(45+j))
    coeff[dummy] = 0
    require(set(coeff) == support, "clause support")
    require(k+1 < A, "no base-A carry for any Boolean selector subset")
    require(all((n & (A-2) == 0) == (n in (0, 1)) for n in range(k+1)), "selector mask")
    require(all((x+y) % 2 == 0 if x == y else (x+y) % 2 == 1
                for x in (0, 1) for y in (0, 1)), "copy parity")
    require(len({tuple(vector(s)) for s in range(439)}) == 439, "injective payload")
    require(all(vector(s)[9:] == [1, 0] for s in range(439)), "occupancy and guard")
    threshold = 4*(len(support)+2)*(2*sum(coeff.values())+6)+8
    require(max(threshold, 2*mu+4, 16) < 1 << b, "full native mass bound")

    # Check the complete sparse convolution basis at every tested target.
    DC = {x: 1 for x in bare}
    for x, v in coeff.items():
        if v:
            for band in (T1, T2):
                require(band-x not in DC, "unexpected DC coefficient overlap")
                DC[band-x] = v
    targets = []
    for t in range(a):
        targets += [(copies[1]+t, {copies[3]+t}, set(), {copies[1]+t}),
                    (Hc+copies[0]+t, {copies[1]+t}, {copies[0]+t}, set()),
                    (Hc+copies[1]+t, {copies[2]+t}, {copies[1]+t}, set())]
    targets += [(anchors[2], {anchors[0]}, set(), {anchors[2]}),
                (anchors[3], {anchors[1]}, set(), {anchors[3]})]
    basis_checks = 0
    for target, expect0, expect1, expect2 in targets:
        for x in support:
            actual = (DC.get(target-x, 0), int(x+Hc == target), int(x == target))
            require(actual == (int(x in expect0), int(x in expect1), int(x in expect2)),
                    ("target basis", target, x, actual))
            basis_checks += 3
    for band in (T1, T2):
        for x in support:
            require(DC.get(band-x, 0) == coeff[x], "clause coefficient mismatch")
            require(x+Hc != band, "right-neighbor contamination in clause band")
    expanded = support | {dummy+1}
    band_hits = [{(band-x) % circumference for x in expanded} for band in (T1, T2)]
    require(not band_hits[0] & band_hits[1], "all-rotation clean band")
    anchor_hits = [{(anchor-x) % circumference for x in support} for anchor in anchors[2:]]
    require(anchor_hits[0] & anchor_hits[1] == {0}, "all-rotation anchor uniqueness")
    padding_count = len(support) - (2*mu.bit_count()+len(targets)+1)
    pad_start = T2+emax+1
    padding = range(pad_start, pad_start+padding_count)
    require(max(DC)+emax < pad_start and Hc+emax < pad_start, "padding is beyond field support")
    require(padding.stop < circumference and T2+2*emax+2 <= circumference, "cell circumference")
    require(all(0 < x < pad_start for x in bare), "origin has no unshifted field terms")
    dc5 = sum((v % 5)*pow(2, x, 5) for x, v in DC.items()) % 5
    unit = (2*dc5-pow(2, Hc, 5)) % 5
    require(unit == 1, "actual rank coefficient is a five-adic unit")
    return locals()


def materialize(g):
    b, d = g['b'], g['d']
    directory = ROOT / "expanded"
    directory.mkdir(exist_ok=True)

    def sparse_integer(parts, max_bits=d):
        # Values must occupy disjoint binary positions. Overlap is an error,
        # not silently interpreted as OR instead of the specified sum.
        buf = bytearray((max_bits+7)//8)
        for offset, value in parts:
            if not value:
                continue
            index, shift = divmod(offset, 8)
            shifted = value << shift
            width = (shifted.bit_length()+7)//8
            old = int.from_bytes(buf[index:index+width], 'little')
            require(not old & shifted, "binary component overlap during expansion")
            buf[index:index+width] = (old | shifted).to_bytes(width, 'little')
        return int.from_bytes(buf, 'little')

    B = 1 << d
    beta = B-1
    dc = sparse_integer((b*x, v) for x, v in g['DC'].items())
    dr = 1 << (b*g['Hc'])
    K = dc + B*dr
    require(0 < dc < B, "DC range")
    native_parts = [(b*g['T1'], g['mu']), (b*g['T2'], g['mu']), (2, 1)]
    native_parts += [(b*t[0], 1) for t in g['targets']]
    native_parts += [(b*t, 1) for t in g['padding']]
    mf = sparse_integer(native_parts)
    allowed = sparse_integer([(b*x, 1) for x in g['support'] if x != 1] + [(b*g['dummy']+1, 1)])
    mc = beta-allowed
    mf_source = mf+beta
    require(0 < mc < beta and 0 < mf < beta, "mask range")
    require(mc % 4 == 2 and mf % 8 == 4, "mask low residues")
    require(mc.bit_count()+mf.bit_count() == d, "actual binary mask population")
    require(mf.bit_count() == len(g['support']) == 4143, "native MF exact population")
    require((2*dc-dr) % 5 == 1, "actual expanded five-adic unit")
    require(K.bit_length() == b*(g['circumference']+g['Hc'])+1, "actual K length")
    values = {'beta': beta, 'K': K, 'MC': mc, 'MF_source': mf_source}
    files = {}
    for name, value in values.items():
        payload = value.to_bytes((value.bit_length()+7)//8, 'big')
        path = directory / (name + '.bin')
        path.write_bytes(payload)
        loaded = int.from_bytes(path.read_bytes(), 'big')
        require(loaded == value, "binary roundtrip")
        files[name] = {'file': path.name, 'bit_length': value.bit_length(),
                       'bit_population': value.bit_count(), 'size_bytes': len(payload),
                       'sha256': hashlib.sha256(payload).hexdigest()}
    ledger = {'status': 'PASS', 'encoding': 'unsigned minimal-width big-endian binary; leading unused bits are zero',
              'coefficient_order': list(values), 'files': files,
              'native_MF_population': mf.bit_count(), 'native_MC_population': mc.bit_count(),
              'native_mask_population_sum': d, 'native_MF_mod8': mf % 8, 'MC_mod4': mc % 4,
              'DC_mod5': dc % 5, 'DR_mod5': dr % 5, 'two_DC_minus_DR_mod5': (2*dc-dr) % 5,
              'shifted_mask_identity': 'MF_source = native_MF + beta',
              'sum_file_bytes': sum(item['size_bytes'] for item in files.values())}
    (directory / 'MANIFEST.json').write_text(json.dumps(ledger, indent=2)+'\n')
    return ledger


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--materialize', action='store_true')
    args = parser.parse_args()
    g = build()
    receipt = {'status': 'PASS', 'tiles': len(g['tiles']), 'support': len(g['support']),
               'convolution_basis_checks': g['basis_checks'], 'radix_bits': g['b'],
               'cell_radices': g['circumference'], 'cell_bits': g['d'],
               'full_mass_bound_bit_length': g['threshold'].bit_length(),
               'padding_start': g['padding'].start, 'padding_stop': g['padding'].stop,
               'padding_count': len(g['padding']), 'five_adic_unit': g['unit'],
               'scope': 'Independent literal filtering, exact sparse compiler and optional full integer expansion; not a universal formal proof.'}
    if args.materialize:
        receipt['expanded'] = materialize(g)
    (ROOT / 'independent_audit.json').write_text(json.dumps(receipt, indent=2)+'\n')
    print(json.dumps(receipt, indent=2))
