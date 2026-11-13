"""Python test of the block-mask2963 analogue of `Adm942PackingCells.LocalNormalization`.

Usage: py -I -X utf8 -S -B ln_check.py [random_triples]

Same fields as the admissible942 structure, with L = 2963, BN = 2^139261, the
bm2963 kernel and masks (rebuilt by check_recipe.py), cellN with marker 1005.
`low`, `low_origin`, `product` and the mask bounds are exhaustive; `block` is
tested on random admissible triples plus every admissible triple with mc = 0,
each with all 32 settings of (dc, uc, dp, up, dt). Non-admissible triples are
negative controls. Finite evidence only.
"""
import random
import sys

sys.path.insert(0, __import__("pathlib").Path(__file__).resolve().parent.as_posix())
import check_recipe as cr  # noqa: E402

tiles = cr.lean_tiles()
c = cr.coefficients(tiles)
ports, _, MFn = cr.recipe(c)
K, MC = ports["K"], ports["MC"]
HP = MFn
L, RB = 2963, 47
BN = 1 << (RB * L)


def spread(base, bits, x):
    return sum(((x >> i) & 1) << (RB * (base + i)) for i in range(bits))


def cellN(m, d, u):
    w, n, e, s = tiles[m]
    return ((1 << (RB * m)) + spread(942, 9, 511 - s) + spread(960, 9, 511 - n)
            + spread(969, 8, 255 - e) + spread(978, 8, 255 - w) + (d << (RB * 977)) + (u << (RB * 1005)))


_cache = {}


def prod(m, d, u):
    key = (m, d, u)
    if key not in _cache:
        x = K * cellN(m, d, u)
        _cache[key] = (x & (BN - 1), x >> (RB * L))
    return _cache[key]


def lnlD(mc, dc, uc, mp, dp, up, mt, dt, ut):
    return prod(mc, dc, uc)[0] + prod(mp, dp, up)[1] + cellN(mt, dt, ut)


def block(mc, mp, mt, dc, uc, dp, up, dt):
    x = lnlD(mc, dc, uc, mp, dp, up, mt, dt, 1 if mc == 0 else 0)  # Lean ℕ: 1 - mc
    a = cellN(mc, dc, uc) + x < BN
    b = 0 < x
    m1 = x & HP == 0
    m2 = (mc != 0) or (x & (HP - 1) == 0)
    return a and b and m1 and m2


def main():
    n_rand = int(sys.argv[1]) if len(sys.argv) > 1 else 300
    ok = True
    low = all(cellN(m, d, u) & MC == 0 for m in range(942) for d in (0, 1) for u in (0, 1))
    low_origin = all((cellN(0, d, u) - 1) & (MC + 1) == 0 for d in (0, 1) for u in (0, 1))
    product = all(K * cellN(m, d, u) < BN * BN for m in range(942) for d in (0, 1) for u in (0, 1))
    bounds = MC + 1 < BN and 1 <= HP < BN
    print(f"low (exhaustive 3768): {low}; low_origin: {low_origin}; product: {product}; mask bounds: {bounds}")
    ok &= low and low_origin and product and bounds
    west = {}
    north = {}
    for j, (w, n, e, s) in enumerate(tiles):
        west.setdefault(w, []).append(j)
        north.setdefault(n, []).append(j)
    rng = random.Random(2963)
    triples = []
    for mc in range(942):
        e, s = tiles[mc][2], tiles[mc][3]
        mps, mts = west.get(e, []), north.get(s, [])
        if mc == 0:
            triples += [(0, mp, mt) for mp in mps for mt in mts]
    cands = [mc for mc in range(942) if west.get(tiles[mc][2]) and north.get(tiles[mc][3])]
    for _ in range(n_rand):
        mc = rng.choice(cands)
        triples.append((mc, rng.choice(west[tiles[mc][2]]), rng.choice(north[tiles[mc][3]])))
    checks = fails = 0
    for mc, mp, mt in triples:
        for bits in range(32):
            dc, uc, dp, up, dt = [(bits >> i) & 1 for i in range(5)]
            checks += 1
            if not block(mc, mp, mt, dc, uc, dp, up, dt):
                fails += 1
                if fails <= 3:
                    print('  fail', mc, mp, mt, dc, uc, dp, up, dt)
    print(f"block: {checks} checks on {len(triples)} admissible triples ({sum(1 for t in triples if t[0] == 0)} with mc = 0), failures {fails}")
    ok &= fails == 0
    # negative controls: break the east/west or south/north adjacency
    neg = 0
    tried = 0
    for _ in range(60):
        mc = rng.randrange(942)
        mp = rng.randrange(942)
        mt = rng.randrange(942)
        if tiles[mc][2] == tiles[mp][0] and tiles[mc][3] == tiles[mt][1]:
            continue
        tried += 1
        neg += not block(mc, mp, mt, 0, 0, 0, 0, 0)
    print(f"negative controls (non-admissible triples): {neg}/{tried} rejected")
    print("ok" if ok else "FAIL")


if __name__ == "__main__":
    main()
