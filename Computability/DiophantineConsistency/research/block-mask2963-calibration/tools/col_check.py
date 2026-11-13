"""Column-level check of the bm2963 normalized block (the Adm942 direct-column method).

Usage: py -I -X utf8 -S -B col_check.py

For random admissible triples (plus mc = 0 ones) and all 32 dummy/marker
settings, the columns
  col q = colK(cur) q + colK(prev)(L + q) + cell(tmp) q
are computed from the kernel term list without carrying, and compared with the
radix-2^47 digits of lnlD = K*cur % BN + K*prev / BN + tmp. Reports whether
digits equal columns everywhere (no carry at all), the maximal column, and the
maximal predecessor column of a tested high-mask field. Finite evidence only."""
import random, sys, pathlib
sys.path.insert(0, pathlib.Path(__file__).resolve().parent.as_posix())
import ln_check as lc
c = lc.c; tiles = lc.tiles; L = 2963; RB = 47; RHO = 1 << RB
low_terms = [(18, 1), (1005, 1)] + [(1956 - e, v) for e, v in enumerate(c) if v]
def bits(m, d, u):
    w, n, e, s = tiles[m]; b = {m: 1}
    for i in range(9):
        b[942 + i] = ((511 - s) >> i) & 1; b[960 + i] = ((511 - n) >> i) & 1
    for i in range(8):
        b[969 + i] = ((255 - e) >> i) & 1; b[978 + i] = ((255 - w) >> i) & 1
    b[977] = d; b[1005] = u
    return [k for k, v in b.items() if v]
def cols(cur, prev, tmp):
    out = [0] * L
    for f in cur:
        for e, v in low_terms:
            assert f + e < L - 1          # every non-spatial product term stays below field L-1
            out[f + e] += v
    for f in prev:
        out[f + 9] += 1                  # rho^(L+9) * prev, divided by B
    for f in tmp:
        out[f] += 1
    return out
def digits(x):
    s = bin(x)[2:].zfill(RB * L)
    assert len(s) == RB * L
    return [int(s[len(s) - RB * (q + 1):len(s) - RB * q], 2) for q in range(L)]
rng = random.Random(7)
west, north = {}, {}
for j, t in enumerate(tiles):
    west.setdefault(t[0], []).append(j); north.setdefault(t[1], []).append(j)
cands = [m for m in range(942) if west.get(tiles[m][2]) and north.get(tiles[m][3])]
tested = list(range(1, 917)) + list(range(960, 969)) + list(range(987, 995)) + [1005, 1956]
triples = [(0, mp, mt) for mp in west[tiles[0][2]][:5] for mt in north[tiles[0][3]][:5]]
for _ in range(40):
    mc = rng.choice(cands)
    triples.append((mc, rng.choice(west[tiles[mc][2]]), rng.choice(north[tiles[mc][3]])))
mx = mxpre = mxlow = 0; bad = badlow = 0; n = 0; argmx = None; last = 0
for mc, mp, mt in triples:
    for b5 in range(32):
        dc, uc, dp, up, dt = [(b5 >> i) & 1 for i in range(5)]
        ut = 1 if mc == 0 else 0
        out = cols(bits(mc, dc, uc), bits(mp, dp, up), bits(mt, dt, ut))
        x = lc.lnlD(mc, dc, uc, mp, dp, up, mt, dt, ut)
        n += 1
        dg = digits(x)
        bad += dg != out
        badlow += dg[:1957] != out[:1957]
        if max(out) > mx:
            mx = max(out); argmx = out.index(mx)
        mxlow = max(mxlow, max(out[:1957]))
        mxpre = max(mxpre, max(out[p - 1] for p in tested))
        last = max(last, out[L - 1], dg[L - 1])
print(f"{n} blocks on {len(triples)} triples")
print(f"  digits == columns at every field 0..1956 (all tested fields): {badlow == 0}; max column there {mxlow} = {mxlow / RHO:.4f} rho")
print(f"  digits == columns at every field: {bad == 0} (carries occur only above the clause)")
print(f"  max column {mx} = {mx / RHO:.4f} rho at field {argmx} (<= 2^53 = 64 rho: {mx <= 2 ** 53})")
print(f"  max predecessor column of a tested field {mxpre} = {mxpre / RHO:.4f} rho; column and digit of field L-1: {last}")
