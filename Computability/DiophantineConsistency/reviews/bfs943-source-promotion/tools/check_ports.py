#!/usr/bin/env python3
"""Bind the four Lean ports of `IPRATrace75.fixedPorts` to package 163's hashes.

Usage (from anywhere): py -I -X utf8 -B check_ports.py

`DiophantineConsistency.IPRATrace75.fixedPorts` is
`CompactSymbolicPorts.ports betaNat (DirectBFSSymbolicKernel.paramKernel rho)
lowNat highNat = ![β, K0, MC, β + MF_native]`. This script

* requires the Lean definition lines it transcribes to be present verbatim
  (`fixedPorts`, `ports`, `betaNat`, `rho`, `paramKernel`, `value`,
  `selector`, `slots`, `support`, `digit`, `lowNat`, `highNat`,
  `highDigits` and its constants) and pins the SHA-256 of each Lean file;
* parses the 943 BFS rows from `BFS943/DirectBFSSymbolicKernel.lean`;
* rebuilds the four integers and compares their minimal little-endian bytes
  with the `raw_sha256` and bit lengths in the `coefficient_binding` of
  `163-trace-radical/compact/equations/trace75_degree402.json`, and with the
  decompressed retained payloads of `research/indexed-tile-enumeration`.

It is finite external evidence for the transcription, not a Lean theorem
about files.
"""
from hashlib import sha256
from pathlib import Path
import gzip
import json
import re
import sys

if sys.flags.optimize:
    raise SystemExit("optimized Python refused")

D = Path(__file__).resolve().parents[3]          # Computability/DiophantineConsistency
L = D / "Lean/DiophantineConsistency"
GRAPH = D / "con-zfc-diophantine-forms/163-trace-radical/compact/equations/trace75_degree402.json"
PAYLOADS = D / "research/indexed-tile-enumeration/coefficients"

LEAN = {
    "endpoint": L / "BFS943/IPRATrace75.lean",
    "bfs_kernel": L / "BFS943/DirectBFSSymbolicKernel.lean",
    "kernel": L / "Compact44/CompactSymbolicKernel.lean",
    "beta": L / "Compact44/CompactFixedBeta.lean",
    "ports": L / "Compact44/CompactSymbolicPorts.lean",
    "mass": L / "Compact44/CompactCoefficientMass.lean",
    "listmask": L / "Compact44/CompactListMask.lean",
    "mask": L / "Compact44/CompactConcreteMask.lean",
    "high": L / "Compact44/CompactHighPopulation.lean",
}
PINS = {
    "bfs_kernel": "02a242e364fc1653ce05fc07d4fe515cc4e3ce287b76f73ab4ffdf2079f7c800",
    "kernel": "9b2b73430cbf4578ef4b4c7d4658c9526b7ebdc423263470df907a16b454ba55",
    "beta": "bcb892e7ae6b0d3cf329a248ca6b468e36a9a1b582d75cacafb7fd49f89025ea",
    "ports": "0fc8eb4f60e801b38a3a516cd23d9f44c1e9eda62609d34bd76764de7ac51414",
    "mass": "1dad41ebf3fe6c9c68b6f6d76bd6d1a42f318ca75eb6f107d3bcd0407246b592",
    "listmask": "34c4d38c265160155a7fa3f99ea3af692c5f3be10b7b77cac211afc199953d4b",
    "mask": "f93993e8b4badb6518d8ac6e575d406f322d7205b7d95c17c185103510b474c2",
    "high": "b1e962aed2f9fc2b49533a52f3508a84af4d433c4a9fae210540e085056dab1d",
    "endpoint": "6e2379cdc35d00b7705dbe25f3decfd22a7e8327b4322a0a5fff1043de59b4a0",
}

# Verbatim definition text that the computation below transcribes.
NEEDS = {
    "endpoint": [
        "def fixedPorts : Fin 4 → ℕ :=\n"
        "  CompactSymbolicPorts.ports CompactFixedBeta.betaNat\n"
        "    (DirectBFSSymbolicKernel.paramKernel CompactSymbolicKernel.rho)\n"
        "    CompactSymbolicPorts.lowNat CompactSymbolicPorts.highNat\n",
        "def expression : Expr (Fin 10) := Trace75BFSSyntax.literal fixedPorts\n",
    ],
    "ports": [
        "def lowNat : ℕ := Nat.ofDigits (2^67) (CompactListMask.digits (2^67) 8807 1063 CompactConcreteMask.support)\n",
        "def highNat : ℕ := Nat.ofDigits (2^67) CompactHighPopulation.highDigits\n",
        "def ports (β K L H : ℕ) : Fin 4 → ℕ := ![β,K,L,β+H]\n",
    ],
    "beta": ["def betaNat : ℕ := 2^(67*8807)-1\n"],
    "kernel": ["def rho : ℕ := 2^67\n"],
    "bfs_kernel": [
        "def paramKernel (r : ℕ) : ℕ :=\n"
        "  r^30+r^62+r^1100+r^2201 +\n"
        "  (∑ i : Fin 943, CompactCoefficientMass.selector (row i) *\n"
        "     (r^(4393-i.val)+r^(5495-i.val))) +\n"
        "  (∑ i : Fin 41, (2^(10+i.val):ℕ) * (r^(4393-position i)+r^(5495-position i))) +\n"
        "  r^8807*r^42\n",
        "def row (i : Fin 943) : Nat × Nat × Nat × Nat :=\n"
        "  rows.get ⟨i.val, by simpa only [rows_length] using i.isLt⟩\n",
    ],
    "mass": [
        "def value (t : Nat × Nat × Nat × Nat) : Nat :=\n"
        "  t.1 + 2^8*t.2.1 + 2^17*t.2.2.1 + 2^25*t.2.2.2 + 127*2^34\n",
        "def selector (t : Nat × Nat × Nat × Nat) : Nat := 1 + 2^10 * (2^41 - value t)\n",
    ],
    "listmask": [
        "def digit (B special : ℕ) (S : Finset ℕ) (j : ℕ) : ℕ :=\n"
        "  if j=special then B-4 else if j∈S then B-2 else B-1\n",
        "def digits (B len special : ℕ) (S : Finset ℕ) : List ℕ :=\n"
        "  (List.range len).map (digit B special S)\n",
    ],
    "mask": [
        "def support : Finset ℕ :=\n"
        "  ((range 943 ∪ Ico 983 993 ∪ Ico 1003 1012 ∪ Ico 1013 1032 ∪\n"
        "    {1063,1064,1095,2195,3296}) \\ {1})\n",
    ],
    "high": [
        "def mu : ℕ := 2^51-2\n",
        "def padding : ℕ := 2^65-1\n",
        "def lastPadding : ℕ := 2^19-1\n",
        "def highDigits : List ℕ :=\n"
        "  [4] ++ List.replicate 1012 0 ++ List.replicate 10 1 ++\n"
        "  List.replicate 42 0 ++ List.replicate 9 1 ++\n"
        "  List.replicate 1121 0 ++ [1] ++ List.replicate 1100 0 ++ [1] ++\n"
        "  List.replicate 1096 0 ++ [mu] ++ List.replicate 1101 0 ++ [mu] ++\n"
        "  List.replicate 3296 0 ++ List.replicate 13 padding ++ [lastPadding,0]\n",
    ],
}


def need(cond, msg):
    if not cond:
        raise RuntimeError(msg)


def text(key):
    data = LEAN[key].read_bytes()
    need(sha256(data).hexdigest() == PINS[key], f"hash pin {key}: {LEAN[key].name}")
    return data.decode("utf-8")


def raw(n):
    return n.to_bytes((n.bit_length() + 7) // 8, "little")


def main():
    src = {k: text(k) for k in LEAN}
    for k, items in NEEDS.items():
        for s in items:
            need(src[k].count(s) == 1, f"definition text missing in {LEAN[k].name}: {s.splitlines()[0]}")

    # rows of the direct-index BFS kernel
    section = src["bfs_kernel"].split("def rows : List (Nat × Nat × Nat × Nat) := [\n", 1)[1].split("  ]\n", 1)[0]
    rows = []
    for line in section.splitlines():
        m = re.fullmatch(r"  \((\d+), (\d+), (\d+), (\d+)\),", line)
        need(m is not None, "row syntax")
        rows.append(tuple(map(int, m.group(1, 2, 3, 4))))
    need(len(rows) == 943, "row count")
    m = re.search(r"^def slots : List ℕ := \[([0-9,]+)\]$", src["kernel"], re.M)
    need(m is not None, "slots syntax")
    slots = list(map(int, m.group(1).split(",")))
    need(len(slots) == 41 and len(set(slots)) == 41, "slots")

    rho = 2 ** 67
    beta = 2 ** (67 * 8807) - 1

    def value(t):
        return t[0] + 2 ** 8 * t[1] + 2 ** 17 * t[2] + 2 ** 25 * t[3] + 127 * 2 ** 34

    def selector(t):
        v = value(t)
        need(v <= 2 ** 41, "selector truncation")
        return 1 + 2 ** 10 * (2 ** 41 - v)

    def nsub(a, b):
        return a - b if a >= b else 0

    r = rho
    K = (r ** 30 + r ** 62 + r ** 1100 + r ** 2201
         + sum(selector(rows[i]) * (r ** nsub(4393, i) + r ** nsub(5495, i)) for i in range(943))
         + sum(2 ** (10 + i) * (r ** nsub(4393, slots[i]) + r ** nsub(5495, slots[i])) for i in range(41))
         + r ** 8807 * r ** 42)

    support = ((set(range(943)) | set(range(983, 993)) | set(range(1003, 1012)) | set(range(1013, 1032))
                | {1063, 1064, 1095, 2195, 3296}) - {1})

    def of_digits(ds):
        v = 0
        for d in reversed(ds):
            v = v * rho + d
        return v

    low_digits = [rho - 4 if j == 1063 else rho - 2 if j in support else rho - 1 for j in range(8807)]
    mu, pad, last = 2 ** 51 - 2, 2 ** 65 - 1, 2 ** 19 - 1
    rep = lambda n, x: [x] * n
    high_digits = ([4] + rep(1012, 0) + rep(10, 1) + rep(42, 0) + rep(9, 1) + rep(1121, 0) + [1]
                   + rep(1100, 0) + [1] + rep(1096, 0) + [mu] + rep(1101, 0) + [mu] + rep(3296, 0)
                   + rep(13, pad) + [last, 0])
    need(len(high_digits) == 8807 and all(d < rho for d in high_digits + low_digits), "digit lists")
    MC, H = of_digits(low_digits), of_digits(high_digits)
    ports = {"beta": beta, "K0": K, "MC": MC, "MF": beta + H}   # ![β, K, L, β+H]

    binding = json.loads(GRAPH.read_text(encoding="utf-8"))["coefficient_binding"]["ports"]
    out = {}
    for name, n in ports.items():
        b = raw(n)
        h = sha256(b).hexdigest()
        rec = binding[name]
        pay = gzip.decompress((PAYLOADS / rec["file"]).read_bytes())
        ok = h == rec["raw_sha256"] and n.bit_length() == rec["bits"] and b == pay
        out[name] = {"bits": n.bit_length(), "raw_sha256": h, "matches_163_and_payload": ok}
        need(ok, f"port {name} mismatch")
    for k in LEAN:
        text(k)  # re-pin after the computation
    print(json.dumps({"status": "PASS", "ports": out, "rows": len(rows), "slots": len(slots),
                      "scope": "Python transcription of pinned Lean definitions; not a Lean theorem about files"},
                     indent=1, sort_keys=True))


if __name__ == "__main__":
    try:
        main()
    except RuntimeError as e:
        print("FAIL:", e)
        sys.exit(1)
