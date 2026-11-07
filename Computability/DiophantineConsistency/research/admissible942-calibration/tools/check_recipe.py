"""Independent check of the admissible942 coefficient recipe from Lean data.

Usage: py -I -X utf8 -S -B check_recipe.py

It rebuilds the 942-row table `WangTiles942.tile` from the Lean data module
`WangTiles942Data.lean` (actions, transition targets and the fixed rows),
applies the recipe of `research/admissible942-independent/PROOF.md` §1 and §3
(complemented 34-bit clause fields, label copies at 942/960/969/978, dummy 977,
marker 1005, bands at 1992/2998, D_R = ρ^9), and compares the four integers
with the pinned payloads of `candidates/one-page-admissible942/coefficients/`
(minimal unsigned big-endian bytes, gzip).
This is finite external evidence for a Lean transcription, not a Lean theorem.
"""
import gzip
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[3]
LEAN = ROOT / "Lean/DiophantineConsistency/WangTiles942Data.lean"
PAYLOADS = ROOT / "candidates/one-page-admissible942/coefficients"


def lean_tiles():
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
    assert sorted(rows) == list(range(942))
    return [rows[i] for i in range(942)]


def G(x, m):
    return sum(x ** j for j in range(m))


def recipe(tiles):
    rho_bits, L = 47, 4027
    rho = 1 << rho_bits
    B = rho ** L
    beta = B - 1
    c = {}
    for j, (w, n, p, s) in enumerate(tiles):
        c[j] = 1 + 2 ** 10 * (1 + w + 2 ** 8 * n + 2 ** 17 * p + 2 ** 25 * s)
    for j in range(8):
        c[978 + j] = 2 ** (10 + j)
        c[969 + j] = 2 ** (27 + j)
    for j in range(9):
        c[960 + j] = 2 ** (18 + j)
        c[942 + j] = 2 ** (35 + j)
    Es = (set(range(942)) | set(range(942, 951)) | set(range(960, 969)) | set(range(969, 977))
          | set(range(978, 986)) | {977, 1005})
    assert len(Es) == 978 and set(c) | {977, 1005} == Es
    DC = rho ** 18 + rho ** 1005 + sum(v * (rho ** (1992 - e) + rho ** (2998 - e)) for e, v in c.items())
    K = DC + B * rho ** 9
    MC = beta - sum(rho ** e for e in Es)
    Lam = rho ** 1992 + rho ** 2998
    Ccore = rho ** 960 * G(rho, 9) + rho ** 987 * G(rho, 8) + rho ** 1005
    Z = (rho - 1) * rho ** 4004 * G(rho, 18) + (2 ** 27 - 1) * rho ** 4022
    MFn = 4 + (2 ** 44 - 2) * Lam + Ccore + Z
    return {"beta.bin.gz": beta, "K.bin.gz": K, "MC.bin.gz": MC, "MF_source.bin.gz": MFn + beta}


def payload(name):
    return int.from_bytes(gzip.open(PAYLOADS / name).read(), "big")


def main():
    tiles = lean_tiles()
    ok = len(tiles) == 942 and tiles[0] == (2, 435, 3, 1) and tiles[941] == (4, 437, 2, 437)
    for name, value in recipe(tiles).items():
        same = value == payload(name)
        ok &= same
        print(f"{name}: {value.bit_length()} bits, matches payload: {same}")
    print("ok" if ok else "MISMATCH")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
