"""Independent check of the wang943-mixed-121x8801 coefficient recipe.

Usage: py -I -X utf8 -S -B check_recipe.py

It implements the recipe of `31-sun10/coefficients/COEFFICIENT_PROOF.md` §1
from the tile rows of the Lean module `Compact44/Compact943Data.lean`, checks
that those rows are the package's `wang943_tiles.json` in order, and compares
the four reconstructed integers with the package's gzip payloads.
"""
import gzip
import json
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[3]
LEAN = ROOT / "Lean/DiophantineConsistency/Compact44/Compact943Data.lean"
PKG = ROOT / "con-zfc-diophantine-forms/31-sun10/coefficients"


def lean_rows():
    text = LEAN.read_text(encoding="utf-8")
    body = text.split("-- BEGIN PINNED ORDERED ROWS")[1].split("]")[0]
    return [tuple(map(int, m)) for m in re.findall(r"\((\d+), (\d+), (\d+), (\d+)\)", body)]


def payload(name):
    return int.from_bytes(gzip.open(PKG / "payloads" / name).read(), "little")


def recipe(rows):
    rho_bits, L = 121, 8801
    d = rho_bits * L
    rho = 1 << rho_bits
    B = 1 << d
    E = (list(range(0, 943)) + list(range(983, 993)) + list(range(1003, 1033))
         + [1063, 1064, 1095, 1096, 2195, 3296])
    assert len(E) == 989 and len(set(E)) == 989
    W = [1 << (10 + 2 * j) for j in range(44)]
    c = {}
    for i, tile in enumerate(rows):
        v = 1 + W[40] + W[41] + W[42] + W[43]
        for t, x in enumerate(tile):
            for j in range(10):
                if (x + 512) >> j & 1:
                    v += W[10 * t + j]
        c[i] = v
    for t, off in enumerate([1023, 1013, 1003, 983]):
        for j in range(10):
            c[off + j] = W[10 * t + j]
    for k, e in enumerate([1095, 1096, 2195, 3296]):
        c[e] = W[40 + k]
    c[1063] = c[1064] = 0
    assert sorted(c) == sorted(E)
    mu = 1022 + sum(W)
    Z = ((1 << 119) - 1) * sum(rho ** e for e in range(8792, 8799)) + ((1 << 27) - 1) * rho ** 8799
    DC = rho ** 30 + rho ** 62 + rho ** 1100 + rho ** 2200 + sum(
        c[e] * (rho ** (4393 - e) + rho ** (5495 - e)) for e in E)
    DR = rho ** 42
    MC = B - 1 - sum(rho ** e for e in E if e != 1) - 2 * rho ** 1063
    MF_native = (4 + mu * (rho ** 4393 + rho ** 5495)
                 + sum(rho ** (1013 + j) + rho ** (1065 + j) for j in range(10))
                 + rho ** 2195 + rho ** 3296 + Z)
    return {"beta.bin.gz": B - 1, "K.bin.gz": DC + B * DR, "MC.bin.gz": MC,
            "MF_source.bin.gz": MF_native + B - 1}


def main():
    rows = lean_rows()
    tiles = [tuple(t) for t in json.load(open(PKG / "upstream/wang943_tiles.json", encoding="utf-8"))]
    ok = len(rows) == 943 and rows == tiles
    print(f"Lean rows = wang943_tiles.json: {ok} ({len(rows)} rows)")
    for name, value in recipe(rows).items():
        same = value == payload(name)
        ok &= same
        print(f"{name}: {value.bit_length()} bits, matches payload: {same}")
    print("ok" if ok else "MISMATCH")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
