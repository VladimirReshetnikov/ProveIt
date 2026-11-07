"""Independent check of the source34 ("mixed-parity-unrounded-1064921") recipe.

Usage: py -I -X utf8 -S -B check_recipe.py

It implements the recipe of `source34_coefficients.md` ("Complete bounded
recipe") from the tile rows of the Lean module `Compact44/Compact943Data.lean`,
and compares the four reconstructed integers, plus the two cone ports, with
the source34 gzip payloads bound by
`101-constructive-reductions/integer14/upstream/coefficients/BINDING.json`.
"""
import gzip
import hashlib
import json
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[3]
LEAN = ROOT / "Lean/DiophantineConsistency/Compact44/Compact943Data.lean"
BINDING = ROOT / "con-zfc-diophantine-forms/101-constructive-reductions/integer14/upstream/coefficients/BINDING.json"
PAYLOADS = ROOT / "candidates/valuation-shared-norms/source/inherited/root_fusion/coefficients"


def lean_rows():
    text = LEAN.read_text(encoding="utf-8")
    body = text.split("-- BEGIN PINNED ORDERED ROWS")[1].split("]")[0]
    return [tuple(map(int, m)) for m in re.findall(r"\((\d+), (\d+), (\d+), (\d+)\)", body)]


def raw(value):
    return value.to_bytes((value.bit_length() + 7) // 8, "little")


OFFSETS = [1020, 1000, 980, 960]


def support():
    E = (list(range(0, 943)) + [o + 2 * j for o in OFFSETS for j in range(10)]
         + [1063, 1064, 1095, 1096, 2195, 3296])
    return sorted(E)


def recipe(rows):
    rho_bits, L = 121, 8801
    d = rho_bits * L
    rho = 1 << rho_bits
    B = 1 << d
    E = support()
    assert len(E) == 989 and len(set(E)) == 989 and max(E) == 3296
    W = [1 << (10 + 2 * j) for j in range(44)]
    c = {}
    for i, tile in enumerate(rows):
        v = 1 + W[40] + W[41] + W[42] + W[43]
        for t, x in enumerate(tile):
            for j in range(10):
                if (x + 512) >> j & 1:
                    v += W[10 * t + j]
        c[i] = v
    for t, off in enumerate(OFFSETS):
        for j in range(10):
            c[off + 2 * j] = W[10 * t + j]
    for k, e in enumerate([1095, 1096, 2195, 3296]):
        c[e] = W[40 + k]
    c[1063] = c[1064] = 0
    assert sorted(c) == E
    mu = 1022 + sum(W)
    Z = ((1 << 119) - 1) * sum(rho ** e for e in range(8792, 8799)) + ((1 << 27) - 1) * rho ** 8799
    DC = rho ** 40 + rho ** 41 + rho ** 1100 + rho ** 2200 + sum(
        c[e] * (rho ** (4393 - e) + rho ** (5495 - e)) for e in E)
    DR = rho
    MC = B - 1 - sum(rho ** e for e in E if e != 1) - 2 * rho ** 1063
    MF_native = (4 + mu * (rho ** 4393 + rho ** 5495)
                 + sum(rho ** (1000 + 2 * j) + rho ** (1021 + 2 * j) for j in range(10))
                 + rho ** 2195 + rho ** 3296 + Z)
    return {"beta": B - 1, "K0": DC + B * DR, "MC": MC, "MF": MF_native + B - 1,
            "cone_A": 2 ** 1113, "cone_B": 2 ** 666104}


def main():
    rows = lean_rows()
    binding = json.load(open(BINDING, encoding="utf-8"))["payloads"]
    ok = len(rows) == 943
    for name, value in recipe(rows).items():
        data = raw(value)
        pin = hashlib.sha256(data).hexdigest() == binding[name]["raw_sha256"]
        f = PAYLOADS / binding[name]["file"]
        same = f.exists() and gzip.open(f).read() == data
        ok &= pin and same
        print(f"{name}: {value.bit_length()} bits, sha pin: {pin}, payload file: {same}")
    print("ok" if ok else "MISMATCH")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
