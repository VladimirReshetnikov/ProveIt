"""Finite check of the admissible942 Lean transcription of the ports.

Usage: py -I -X utf8 -S -B check_ports.py

`Adm942MaskData` defines the two masks as explicit radix-2^47 digit lists
(`lowList`, `highPrefix ++ replicate 4 0`) and `Adm942Kernel` defines the
kernel as a term sum (`Term = Fin 3 ⊕ (Entry ⊕ Entry)`, selectors at their
index, the 2011 label positions and weights, bands 1992/2998, bare exponents
18, 1005, 4036). This script transcribes those Lean definitions, rebuilds the
four integers and compares them with the recipe of `check_recipe.py` (which
itself reproduces the pinned payloads). It also checks the finite facts the
Lean modules prove: digit populations, residues, the coefficient mass and the
support difference facts. Finite external evidence, not a Lean theorem.
"""
import pathlib
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from check_recipe import lean_tiles, payload, recipe  # noqa: E402

RHO_BITS, L = 47, 4027
RHO = 1 << RHO_BITS


def of_digits(b, ds):
    v = 0
    for x in reversed(ds):
        v = v * b + x
    return v


def low_list(t):
    """`Adm942MaskData.lowList t`."""
    return ([t] * 951 + [t + 1] * 9 + [t] * 26 + [t + 1] * 19 + [t] * 1 + [t + 1] * 3021)


def high_prefix():
    """`Adm942MaskData.highPrefix`."""
    mu = 2 ** 44 - 2
    return ([4] + [0] * 959 + [1] * 9 + [0] * 18 + [1] * 8 + [0] * 10 + [1] + [0] * 986 + [mu]
            + [0] * 1005 + [mu] + [0] * 1005 + [RHO - 1] * 18 + [2 ** 27 - 1])


def pc(n):
    return bin(n).count("1")


def main():
    tiles = lean_tiles()
    ref = recipe(tiles)
    beta = RHO ** L - 1
    ok = ref["beta.bin.gz"] == beta == payload("beta.bin.gz")

    low = low_list(RHO - 2)
    high = high_prefix() + [0] * 4
    ok &= len(low) == L and len(high_prefix()) == 4023 and len(high) == L
    ok &= all(x < RHO for x in low + high)
    MC, MF = of_digits(RHO, low), of_digits(RHO, high)
    ok &= MC == ref["MC.bin.gz"] == payload("MC.bin.gz")
    ok &= MF + beta == ref["MF_source.bin.gz"] == payload("MF_source.bin.gz")
    # the support, as `lowSupport = range 951 ∪ Ico 960 986 ∪ {1005}`
    Es = set(range(951)) | set(range(960, 986)) | {1005}
    ok &= len(Es) == 978 and MC == beta - sum(RHO ** e for e in Es)
    pops = (sum(pc(x) for x in low), sum(pc(x) for x in high))
    ok &= pops == (L * RHO_BITS - 978, 978)
    ok &= MC % 4 == 2 and MF % 8 == 4 and 0 < MC < beta and 0 < MF < beta
    ok &= MF < RHO ** 4023

    # the kernel term sum
    def selector_weight(t):
        w, n, e, s = t
        return 1 + 2 ** 10 * (1 + w + 2 ** 8 * n + 2 ** 17 * e + 2 ** 25 * s)
    entries = [(j, selector_weight(t)) for j, t in enumerate(tiles)]
    entries += [(978 + j, 2 ** (10 + j)) for j in range(8)]   # west
    entries += [(960 + j, 2 ** (18 + j)) for j in range(9)]   # north
    entries += [(969 + j, 2 ** (27 + j)) for j in range(8)]   # east
    entries += [(942 + j, 2 ** (35 + j)) for j in range(9)]   # south
    terms = [(18, 1), (1005, 1), (L + 9, 1)]
    terms += [(1992 - p, w) for p, w in entries] + [(2998 - p, w) for p, w in entries]
    K = sum(c * RHO ** e for e, c in terms)
    ok &= K == ref["K.bin.gz"] == payload("K.bin.gz")
    mass = sum(c for _, c in terms)
    ok &= mass == 7659829036801887
    positions = [p for p, _ in entries]
    ok &= len(set(positions)) == 976 and set(positions) | {977, 1005} == Es
    ok &= max(positions) == 985 and all(p <= 1992 for p in positions)
    exps = [e for e, _ in terms]
    ok &= len(set(exps)) == len(exps) and min(exps[3:]) == 1007 and max(exps) == L + 9
    # support difference facts
    ok &= all(e + 1006 not in Es and e + 1007 not in Es for e in Es)
    ok &= [e for e in Es if e + 1005 in Es] == [0]
    print("low digits", len(low), "high digits", len(high), "populations", pops)
    print("mass", mass, "K bits", K.bit_length())
    print("ok" if ok else "MISMATCH")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
