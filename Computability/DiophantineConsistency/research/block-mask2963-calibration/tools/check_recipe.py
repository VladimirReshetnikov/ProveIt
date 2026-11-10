"""Independent check of the block-mask2963 coefficient recipe from Lean data.

Usage: py -I -X utf8 -S -B check_recipe.py [DIOPHANTINE_ROOT]

DIOPHANTINE_ROOT defaults to the `Computability/DiophantineConsistency`
directory three levels above this file (its location once copied to
`research/<name>/tools/`).

It rebuilds the 942-row table `WangTiles942.tile` from the Lean data module
`WangTiles942Data.lean` (same parser as
`research/admissible942-calibration/tools/check_recipe.py`), applies the
recipe of `research/low-padding-independent/PROOF.md` §3 as simplified by
`research/block-mask-recipe/NOTE.md`:

  rho = 2^47, L = 2963, B = rho^L, beta = B - 1;
  c_j = selectorWeight(tile j) at index j (j < 942); label copies at
  942/960/969/978 with weights 2^(35+j), 2^(18+j), 2^(27+j), 2^(10+j);
  c_977 = c_1005 = 0 (Boolean dummy and marker are physical, unweighted);
  Es = [0,951) u [960,986) u {1005};
  K = rho^18 + rho^1005 + rho^(L+9) + sum_e c_e rho^(1956-e);
  MC = beta - sum_{e in Es} rho^e;
  MF_source = beta + 4 G_917(rho) + (2^44-2) rho^1956
              + rho^960 G_9(rho) + rho^987 G_8(rho) + rho^1005,

and compares the four integers (minimal unsigned big-endian bytes, gzip) with

* `candidates/one-page-block-mask2963/coefficients/` and its MANIFEST.json;
* package 188's `native/coefficients/` and `native/coefficients.json`;
* the frozen weighted coefficient list `research/low-padding-independent/
  coefficients.json` (all 3297 entries; this identifies the tile table).

It then prints the layout facts used by a Lean port: populations, residues,
coefficient mass and carry bound, reflected-band geometry, local-normalization
column bounds, and the completeness controller residues (Pclp, lambda =
1362521). Finite external evidence for a Lean transcription, not a theorem.
"""
import gzip
import hashlib
import json
import pathlib
import re
import sys
from math import gcd, lcm

HERE = pathlib.Path(__file__).resolve()


def find_root():
    if len(sys.argv) > 1 and pathlib.Path(sys.argv[1]).is_dir():
        return pathlib.Path(sys.argv[1])
    for cand in (HERE.parents[3] if len(HERE.parents) > 3 else None,):
        if cand is not None and (cand / "Lean/DiophantineConsistency/WangTiles942Data.lean").exists():
            return cand
    raise SystemExit("cannot locate Computability/DiophantineConsistency")


ROOT = find_root()
LEAN = ROOT / "Lean/DiophantineConsistency/WangTiles942Data.lean"
CAND = ROOT / "candidates/one-page-block-mask2963"
PKG = ROOT / "con-zfc-diophantine-forms/188-pell-orientation-exact-projection/native"
FROZEN = ROOT / "research/low-padding-independent/coefficients.json"

RHO_BITS, L = 47, 2963
RHO = 1 << RHO_BITS
D = RHO_BITS * L
B = RHO ** L
BETA = B - 1
M = 1 << 44
MU = M - 2
CLAUSE = 1956
DR = 9


def lean_tiles():
    """`WangTiles942.tile`, rebuilt from the Lean data (identical to the admissible942 parser)."""
    s = LEAN.read_text(encoding="utf-8")
    arr = s[s.index("def actionCache"):s.index("def actionNat")]
    acts = [(a == "true", b == "true", int(n))
            for a, b, n in re.findall(r"\((true|false), (true|false), (\d+)\)", arr)]
    tl = s[s.index("def targetList"):s.index("def targets ")]
    lists = re.findall(r"\[([\d, ]+)\]", tl)
    T1 = [int(x) for x in lists[0].split(",")]
    T0 = [int(x) for x in lists[1].split(",")]

    def rail(d, q):
        return 205 - 199 * d + sum(1 for a in (T1 if d else T0) if a < q)

    rows = {0: (2, 435, 3, 1)}
    for j, a in enumerate(acts):
        d = int(a[1])
        rows[j + 1] = ((1 - d) * rail(0, a[2]), j + 2, d * rail(1, a[2]), int(a[0]))
    for a in (0, 1):
        for b in (0, 1):
            rows[433 - 2 * a + b] = (0, 432 * a + b, 0, 432 * a + b)
            rows[923 + 2 * a + b] = (0, 432 * a + b, 0, 438)
    for d in (0, 1):
        for q in (T1 if d else T0):
            for b in (0, 1):
                rows[423 + 2 * rail(d, q) + b] = (d * rail(d, q), b, (1 - d) * rail(d, q), 2 * q + b + 2)
    rows.update({927: (2, 434, 2, 0), 928: (3, 436, 4, 4), 929: (4, 436, 4, 0)})
    for t in (434, 435, 436):
        rows[496 + t] = (1, 438, 1, t)
    for a in range(3):
        for b in range(3):
            rows[933 + 3 * a + b] = (a * a, 437, b, 437)
    assert sorted(rows) == list(range(942)), "942 distinct indices"
    return [rows[i] for i in range(942)]


def selector_weight(t):
    w, n, e, s = t
    return 1 + 2 ** 10 * (1 + w + 2 ** 8 * n + 2 ** 17 * e + 2 ** 25 * s)


def G(x, m):
    return sum(x ** j for j in range(m))


def coefficients(tiles):
    """c_e, e = 0..1005 (selectors at index, 2011 label positions/weights)."""
    c = [0] * 3297
    for j, t in enumerate(tiles):
        c[j] = selector_weight(t)
    for j in range(8):
        c[978 + j] = 2 ** (10 + j)   # Lean `CurrentKernel2011`: west
        c[969 + j] = 2 ** (27 + j)   # east
    for j in range(9):
        c[960 + j] = 2 ** (18 + j)   # north
        c[942 + j] = 2 ** (35 + j)   # south
    return c


ES = set(range(951)) | set(range(960, 986)) | {1005}


def recipe(c):
    DC = RHO ** 18 + RHO ** 1005 + sum(v * RHO ** (CLAUSE - e) for e, v in enumerate(c) if v)
    K = DC + B * RHO ** DR
    MC = BETA - sum(RHO ** e for e in ES)
    MFn = 4 * G(RHO, 917) + MU * RHO ** CLAUSE + RHO ** 960 * G(RHO, 9) + RHO ** 987 * G(RHO, 8) + RHO ** 1005
    return {"beta": BETA, "K": K, "MC": MC, "MF_source": MFn + BETA}, DC, MFn


def raw_bytes(v):
    return v.to_bytes((v.bit_length() + 7) // 8, "big")


def sha(b):
    return hashlib.sha256(b).hexdigest()


FILES = {"beta": "beta.bin.gz", "K": "K.bin.gz", "MC": "MC.bin.gz", "MF_source": "MF_source.bin.gz"}


def digits(x, n):
    out = []
    for _ in range(n):
        out.append(x % RHO)
        x //= RHO
    assert x == 0
    return out


def is_prime(n):
    if n < 2:
        return False
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if n % p == 0:
            return n == p
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def factor(n):
    f, p = {}, 2
    while p * p <= n:
        while n % p == 0:
            f[p] = f.get(p, 0) + 1
            n //= p
        p += 1
    if n > 1:
        f[n] = f.get(n, 0) + 1
    return f


def order(a, m):
    """Multiplicative order of a modulo m (gcd(a, m) = 1), via the factored Carmichael-style exponent."""
    fm = factor(m)
    lam = 1
    for p, k in fm.items():
        lam = lcm(lam, (p - 1) * p ** (k - 1))
    o = lam
    for p in factor(lam):
        while o % p == 0 and pow(a, o // p, m) == 1:
            o //= p
    assert pow(a, o, m) == 1
    return o


def main():
    ok = True

    def check(name, cond):
        nonlocal ok
        ok &= bool(cond)
        print(f"  [{'ok' if cond else 'FAIL'}] {name}")

    print(f"root: {ROOT}")
    tiles = lean_tiles()
    c = coefficients(tiles)
    print("1. tile table")
    check("942 Lean rows, tile 0 = (2,435,3,1), tile 941 = (4,437,2,437), tile 928 = (3,436,4,4)",
          len(tiles) == 942 and tiles[0] == (2, 435, 3, 1) and tiles[941] == (4, 437, 2, 437)
          and tiles[928] == (3, 436, 4, 4))
    check("all 942 Lean rows distinct", len(set(tiles)) == 942)
    frozen = json.loads(FROZEN.read_text())
    check("frozen low-padding coefficients.json (3297 entries) == Lean selector weights at index + labels",
          frozen == c)
    check("hence the bm2963 table is WangTiles942.tile in index order (selectorWeight is injective on tiles)",
          len({selector_weight(t) for t in tiles}) == 942 and frozen[:942] == [selector_weight(t) for t in tiles])
    check("c_977 = c_1005 = 0, c zero beyond 985, 976 weighted entries",
          c[977] == c[1005] == 0 and all(v == 0 for v in c[986:]) and sum(1 for v in c if v) == 976)

    print("2. ports")
    ports, DC, MFn = recipe(c)
    cand_manifest = json.loads((CAND / "MANIFEST.json").read_text())["files"]
    pkg_manifest = json.loads((PKG / "coefficients.json").read_text())["ports"]
    pkg_key = {"beta": "beta", "K": "K0", "MC": "MC", "MF_source": "MF"}
    for key, value in ports.items():
        raw = raw_bytes(value)
        fname = FILES[key]
        cand_gz = (CAND / "coefficients" / fname).read_bytes()
        pkg_gz = (PKG / "coefficients" / fname).read_bytes()
        cand_v = int.from_bytes(gzip.decompress(cand_gz), "big")
        pkg_v = int.from_bytes(gzip.decompress(pkg_gz), "big")
        rec = pkg_manifest[pkg_key[key]]
        check(f"{key}: {value.bit_length()} bits, {len(raw)} bytes, raw sha {sha(raw)[:12]}; "
              f"== candidate payload, == package 188 payload, gzip files byte-identical, hashes pinned",
              value == cand_v == pkg_v and cand_gz == pkg_gz
              and cand_manifest["coefficients/" + fname]["sha256"] == sha(cand_gz)
              and rec["raw_sha256"] == sha(raw) and rec["gzip_sha256"] == sha(pkg_gz)
              and rec["bits"] == value.bit_length() and rec["raw_bytes"] == len(raw))
    check("raw bytes total 69685", sum(len(raw_bytes(v)) for v in ports.values()) == 69685)
    beta, K, MC, MF = ports["beta"], ports["K"], ports["MC"], ports["MF_source"]

    print("3. masks")
    pc = lambda x: bin(x).count("1")
    lowd, highd = digits(MC, L), digits(MFn, L)
    check(f"pc(MC) = d - 978 = {D - 978}", pc(MC) == D - 978)
    check("pc(MF_native) = 978 = 917 bit-2 tests + 43 clause bits + 9 + 8 + 1 copy/marker bits",
          pc(MFn) == 978 == 917 + 43 + 9 + 8 + 1)
    check("MC = 2 mod 4, MF_native = 4 mod 8, 0 < MC < beta < MF_source < 2 beta",
          MC % 4 == 2 and MFn % 8 == 4 and 0 < MC < beta < MF < 2 * beta)
    check("MC digits: rho-2 on Es, rho-1 elsewhere",
          all(lowd[e] == (RHO - 2 if e in ES else RHO - 1) for e in range(L)))
    hi_expect = ([4] * 917 + [0] * 43 + [1] * 9 + [0] * 18 + [1] * 8 + [0] * 10 + [1] + [0] * 950
                 + [MU] + [0] * (L - 1957))
    check("MF_native digit list = [4]*917 ++ [0]*43 ++ [1]*9 ++ [0]*18 ++ [1]*8 ++ [0]*10 ++ [1] "
          "++ [0]*950 ++ [mu] ++ [0]*1006 (highest nonzero field 1956)",
          len(hi_expect) == L and highd == hi_expect)

    print("4. kernel")
    terms = [(18, 1), (1005, 1), (L + DR, 1)] + [(CLAUSE - e, v) for e, v in enumerate(c) if v]
    exps = [e for e, _ in terms]
    check("kernel term list reproduces K; exponents pairwise distinct",
          sum(v * RHO ** e for e, v in terms) == K and len(set(exps)) == len(exps))
    mass = sum(v for _, v in terms)
    csum = sum(c)
    print(f"     sum c_e = {csum}, coefficient mass = 3 + sum c_e = {mass}")
    check("sum c_e equals admissible942's (mass 7659829036801887 = 2*3829914518400942 + 3)",
          csum == 3829914518400942 and 2 * csum + 3 == 7659829036801887)
    kmin = next(k for k in range(200) if 2 ** 46 + mass + 1 <= (k + 1) * (RHO - 1))
    print(f"     least k with 2^46 + mass + 1 <= (k+1)(rho-1): {kmin}  (2011/Adm942 use 57)")
    check("the 2011 carry bound 57 still satisfies the CarryInput mass inequality",
          2 ** 46 + mass + 1 <= 58 * (RHO - 1))
    band = sorted(CLAUSE - e for e, v in enumerate(c) if v)
    print(f"     band exponents {band[0]}..{band[-1]}; bare 18, 1005, {L + DR} = L+9")
    check("max product field 1956+1005 = 2961 < L; DR*cell max 9+1005 = 1014",
          CLAUSE + 1005 == 2961 < L)
    check("DC < B, coefficients < rho, and max c_e < M = 2^44", DC < B and max(c) < M)
    # reflected contribution E_h at fields h <= 1005
    E_ok = True
    for h in range(0, 1006):
        idx = [CLAUSE + f - h for f in ES if 0 <= CLAUSE + f - h <= 1005 and c[CLAUSE + f - h]]
        if any(i < 951 or c[i] % 2 for i in idx) or len(idx) != len(set(idx)) or sum(c[i] for i in idx) > M - 1024:
            E_ok = False
        if h <= 970 and idx:
            E_ok = False
    check("E_h (h <= 1005): only label coefficients (index >= 951), each once, even, <= M-1024; zero for h <= 970",
          E_ok)
    lbl = sum(c[942:986])
    check("label sum = M - 1024", lbl == M - 1024)
    check("reset room: (M-1024) + 3 + 2^46 + 57 < rho", (M - 1024) + 3 + 2 ** 46 + 57 < RHO)
    check("clean-clause decoder room with Boolean temporal summand: 942 + 57 + 1 < 1024", 942 + 57 + 1 < 1024)
    # sources of the clause field 1956 and its predecessor
    def sources(h):
        out = []
        for e, v in terms:
            f = h - e
            if f < 0:
                f += L  # previous cell (only the L+9 term reaches back)
                if f < 0:
                    f += L
            if f in ES:
                out.append((e, v, f))
        return out
    s1956 = sources(CLAUSE)
    check("field 1956: exactly the 976 own-cell weighted entries (bare 1938, 951, prev 1947 absent)",
          sorted((CLAUSE - e) for e, _, _ in s1956) == sorted(e for e, v in enumerate(c) if v)
          and all(f == CLAUSE - e for e, _, f in s1956))
    s1955 = sources(CLAUSE - 1)
    extra = [(e, f) for e, v, f in s1955 if e in (18, 1005, L + DR)]
    print(f"     field 1955 bare/spatial sources: {extra}  (bare 1005 on south bit 8 at 950)")
    # column bound for local normalization: Aadj + x950
    # selectors j -> coefficient c_{j+1}, labels each at most once
    aadj_max = max(c[j + 1] for j in range(941)) + sum(c[e + 1] for e in ES if e >= 941 and e + 1 in ES and c[e + 1])
    check(f"Aadj <= 2M-1024 (max {aadj_max}); Aadj + 1 + 128 <= rho", aadj_max <= 2 * M - 1024 and aadj_max + 1 + 128 <= RHO)
    check("columns at the padding fields 1..916 are sums of at most 3 Booleans (bare 18, spatial 9, temporal)",
          all(not any(0 <= CLAUSE + f - h <= 985 and c[CLAUSE + f - h] for f in ES) for h in range(1, 917)))
    check("column L-1 = 2962 vanishes for every Boolean cell (no own/prev/temporal source)",
          not sources(L - 1) and (L - 1) not in ES)
    check("top field 2961 = c_0 * x_1005 only", sorted((e, f) for e, v, f in sources(2961)) == [(CLAUSE, 1005)])
    check("mass < 2^53 (LocalColumns.gs bound)", mass + 2 <= 2 ** 53)

    print("5. alignment geometry")
    # r = 1005 - f from the marker; r > 961 impossible since 961 - r + L > 1005
    rs = sorted({1005 - f for f in ES})
    check("marker preimage gives r = 1005 - f, 0 <= r <= 1005", rs[0] == 0 and rs[-1] == 1005)
    check("for 962 <= r <= 1005 the wrapped preimage L+961-r of target 961 lies outside Es",
          all((961 - r) % L not in ES for r in range(962, 1006)))
    check("r = 20: targets 961/962 read selector 941 and south bit 0 (942); tile 941 complemented south 74 has bit 0 = 0",
          (511 - tiles[941][3]) == 74 and 74 % 2 == 0)
    check("start tile complemented (253,76,252,510), south bits 1..8 set",
          tuple(m - x for m, x in zip((255, 511, 255, 511), tiles[0])) == (253, 76, 252, 510)
          and all((510 >> j) & 1 for j in range(1, 9)))

    print("6. controller (Pclp)")
    lam = 1362521
    kap = lam - 1
    C0 = D * lam
    Bm = pow(2, D, C0)
    rho977 = pow(2, 47 * 977, C0)
    Km = K % C0
    gam = rho977 * (Bm * Bm - 1) * (1 + Bm * (Km + Bm)) % C0
    print(f"     lambda = {lam} prime: {is_prime(lam)}; kappa = {kap} = {factor(kap)}")
    print(f"     d = {D} = {factor(D)}; C0 = d*lambda = {C0}")
    print(f"     B mod C0 = {Bm}; rho^977 mod C0 = {rho977}; K mod C0 = {Km}")
    print(f"     Gamma mod C0 = {gam}; gcd(Gamma, C0) = {gcd(gam, C0)}")
    oG = order(gam, C0)
    oG_parts = (order(gam % 47, 47), order(gam % L, L), order(gam % lam, lam))
    print(f"     ord_C0 Gamma = {oG} (orders mod 47, L, lambda: {oG_parts}); divides lambda-1: {kap % oG == 0}")
    print(f"     lcm(46, L-1, lambda-1) = {lcm(46, L - 1, kap)}")
    print(f"     B^lambda == B (mod C0): {pow(Bm, lam, C0) == Bm}")
    gmod = pow(2, D * kap, C0 * lam)
    v = (gmod - 1) // C0
    print(f"     g = B^kappa mod C0*lambda = {gmod}; (g-1)/C0 mod lambda = {v % lam}, inverse {pow(v % lam, -1, lam) if v % lam else None}")
    print(f"     ord_47 B = {order(Bm % 47, 47)}, ord_L B = {order(Bm % L, L)}, ord_lambda B = {order(Bm % lam, lam)}")
    print(f"     B^2 mod lambda = {Bm * Bm % lam} (must be != 1)")
    H = (1 + Bm * Km + Bm * Bm) % C0
    print(f"     Hs = 1 + B K + B^2 mod (47, L, lambda) = {(H % 47, H % L, H % lam)}")
    lift = pow(2, D * kap, lam * lam)
    print(f"     B^kappa mod lambda^2 = {lift} = 1 + lambda*{(lift - 1) // lam}")
    print(f"     2*C0 = {2 * C0}, lambda^2 = {lam * lam}; 2*C0 > lambda^2: {2 * C0 > lam * lam}")
    check("Pclp: L prime, 47 != L, lambda prime, 68126 | kappa, ord_47 B = 23, ord_L B = 2962",
          is_prime(L) and is_prime(lam) and kap % 68126 == 0
          and order(Bm % 47, 47) == 23 and order(Bm % L, L) == 2962)
    check("Pclp: v_lambda(B^kappa - 1) = 1, H residues (29, 2938, 492699), lift quotient 1079323",
          lift != 1 and (lift - 1) % lam == 0 and (H % 47, H % L, H % lam) == (29, 2938, 492699)
          and (lift - 1) // lam == 1079323)
    check("Gamma is a unit modulo C0", gcd(gam, C0) == 1)
    check("g = B^kappa = 1 + C0*v with v a unit modulo lambda", (gmod - 1) % C0 == 0 and v % lam != 0)

    # Self-test of the controller formulas on the admissible942 tuple, whose
    # residues are Lean numerals in Adm942ControllerData / Adm942ConstructionUnit.
    adm = ROOT / "research/admissible942-calibration/tools/check_recipe.py"
    if adm.exists():
        import importlib.util
        spec = importlib.util.spec_from_file_location("adm942_check_recipe", adm)
        mod = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(mod)
        Ka = mod.recipe(mod.lean_tiles())["K.bin.gz"]
        Da, la = 47 * 4027, 246929
        Ca = Da * la
        Ba = pow(2, Da, Ca)
        ga = pow(2, 47 * 977, Ca) * (Ba * Ba - 1) * (1 + Ba * (Ka % Ca + Ba)) % Ca
        gg = pow(2, Da * (la - 1), Ca * la)
        check("formula self-test on admissible942: B, rho^977, K, Gamma, g, v = Lean numerals "
              "19029934391, 40073055568, 15862373587, 11595945771, 7212347012327222, 154321; ord 740784",
              (Ba, pow(2, 47 * 977, Ca), Ka % Ca, ga, gg, (gg - 1) // Ca % la)
              == (19029934391, 40073055568, 15862373587, 11595945771, 7212347012327222, 154321)
              and order(ga, Ca) == 740784)

    print("ok" if ok else "MISMATCH")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
