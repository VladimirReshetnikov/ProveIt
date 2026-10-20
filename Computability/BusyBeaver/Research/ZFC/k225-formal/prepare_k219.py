"""Prepare the 219's Lean inputs and derived generators.

  python prepare_k219.py

1. `lean219/k219_k230labels.tm`: the native table (candidate-k219/k219.native.tm) with the halt
   254 renamed 230 and the two new states 301, 302 renamed into labels the 219 deleted (102, 120),
   so every label is below 256 and the K230 engine labels are unchanged.
   `lean219/labels.json` records the dense (canonical) -> sparse label map.
2. `generate_boot219_lean.py`, a copy of generate_boot221_lean.py for the 219 (312,617 steps,
   gap 144 = 64 + 80, 130 spare blocks).
"""
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
CAND = HERE.parent / "candidate-k219"
OUT = HERE / "lean219"
OUT.mkdir(exist_ok=True)
REN = {254: 230, 301: 102, 302: 120}

native = {}
for line in open(CAND / "k219.native.tm"):
    if line.startswith("#") or not line.strip():
        continue
    q, b, w, d, n = line.split()
    native[int(q), int(b)] = (w, d, int(n))
used = {q for q, _ in native}
assert not (used & {102, 120, 230}), used & {102, 120, 230}
lines = ["#! start 0"]
for (q, b), (w, d, n) in sorted(native.items()):
    lines.append(f"{REN.get(q, q)} {b} {w} {d} {REN.get(n, n)}")
(OUT / "k219_k230labels.tm").write_text("\n".join(lines) + "\n", encoding="utf-8", newline="\n")

canon = json.load(open(CAND / "canonicalization.json"))
c2n = {int(k): int(v) for k, v in canon["canonical_to_native"].items()}
dense = [REN.get(c2n[i], c2n[i]) for i in range(220)]
assert dense[219] == 230 and len(set(dense)) == 220
json.dump({"dense_to_sparse": dense, "renaming": {str(k): v for k, v in REN.items()}},
          open(OUT / "labels.json", "w"), indent=1)

src = (HERE / "generate_boot221_lean.py").read_text(encoding="utf-8")
subs = [
    ('rocq/rocq-extension/inputs/221/table_k230labels.tm', 'lean219/k219_k230labels.tm'),
    ("STEPS = 409835", "STEPS = 312617"),
    ("regs = [0, 0, 0, 3, 0, 0, 3, 0, 0] + [1] * 167", "regs = [0, 0, 0, 3, 0, 0, 3, 0, 0] + [1] * 130"),
    ("right = [False] * 181 + [True] + sepsR(regs)", "right = [False] * 144 + [True] + sepsR(regs)"),
    ("List.replicate 167 1", "List.replicate 130 1"),
    ("List.replicate 181 false", "List.replicate 144 false"),
    ("After 409,835 steps", "After 312,617 steps"),
    ("a gap of 181 blank cells, and 176 register", "a gap of 144 blank cells, and 139 register"),
    ("then 167 spare", "then 130 spare"),
    ("table221.length = 229", "table219.length = TLEN"),
    ("221", "219"),
]
for a, b in subs:
    assert a in src, a
    src = src.replace(a, b)
tlen = max(REN.get(q, q) for q in used) + 1
src = src.replace("TLEN", str(tlen))
(HERE / "generate_boot219_lean.py").write_text(src, encoding="utf-8", newline="\n")
print("labels: max sparse", tlen - 1, "; wrote lean219/ and generate_boot219_lean.py")
