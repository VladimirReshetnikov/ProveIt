"""Prepare the 218's Lean inputs and derived generators (Source 144, candidate-k218).

  python prepare_k218.py

The 218 keeps the 219's calculus, engine rows and program: its 4,744-leaf source relates to
dag219 by an offset certificate with no offsets, so `L2Q.dag219_seed_iff` is reused unchanged.
This script writes

1. `lean218/k218_k230labels.tm` (native table, halt 254 -> 230, new states 301, 302 -> the
   freed labels 102, 120, as for the 219) and `lean218/labels.json` (dense -> sparse);
2. `generate_boot218_lean.py` (312,909 steps, gap 144, 130 spare blocks),
   `generate_source218_lean.py` (p218 against dag219), `generate_sites218_lean.py` and
   `generate_dense218_lean.py`, by checked substitutions in the 221/219 generators.
"""
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
CAND = HERE.parent / "candidate-k218"
OUT = HERE / "lean218"
OUT.mkdir(exist_ok=True)
REN = {254: 230, 301: 102, 302: 120}

native = {}
for line in open(CAND / "k218.native.tm"):
    if line.startswith("#") or not line.strip():
        continue
    q, b, w, d, n = line.split()
    native[int(q), int(b)] = (w, d, int(n))
used = {q for q, _ in native}
assert not (used & {102, 120, 230}), used & {102, 120, 230}
assert len(used) == 218
lines = ["#! start 0"]
for (q, b), (w, d, n) in sorted(native.items()):
    lines.append(f"{REN.get(q, q)} {b} {w} {d} {REN.get(n, n)}")
(OUT / "k218_k230labels.tm").write_text("\n".join(lines) + "\n", encoding="utf-8", newline="\n")

canon = json.load(open(CAND / "canonicalization.json"))
c2n = {int(k): int(v) for k, v in canon["canonical_to_native"].items()}
dense = [REN.get(c2n[i], c2n[i]) for i in range(219)]
assert dense[218] == 230 and len(set(dense)) == 219
json.dump({"dense_to_sparse": dense, "renaming": {str(k): v for k, v in REN.items()}},
          open(OUT / "labels.json", "w", newline="\n"), indent=1)
st = canon["startup"]
assert st["steps"] == 312909 and st["extra_gap"] == 80 and len(st["spares"]) == 130
assert st["logical_registers"] == [3, 0, 0, 0, 3, 0, 0, 0, 0] and st["native_state"] == 84


def derive(src, dst, subs):
    t = (HERE / src).read_text(encoding="utf-8")
    for a, b in subs:
        assert a in t, (src, a)
        t = t.replace(a, b)
    (HERE / dst).write_text(t, encoding="utf-8", newline="\n")
    print("wrote", dst)


tlen = max(REN.get(q, q) for q in used) + 1
derive("generate_boot221_lean.py", "generate_boot218_lean.py", [
    ('rocq/rocq-extension/inputs/221/table_k230labels.tm', 'lean218/k218_k230labels.tm'),
    ("STEPS = 409835", "STEPS = 312909"),
    ("regs = [0, 0, 0, 3, 0, 0, 3, 0, 0] + [1] * 167", "regs = [0, 0, 0, 3, 0, 0, 3, 0, 0] + [1] * 130"),
    ("right = [False] * 181 + [True] + sepsR(regs)", "right = [False] * 144 + [True] + sepsR(regs)"),
    ("List.replicate 167 1", "List.replicate 130 1"),
    ("List.replicate 181 false", "List.replicate 144 false"),
    ("After 409,835 steps", "After 312,909 steps"),
    ("a gap of 181 blank cells, and 176 register", "a gap of 144 blank cells, and 139 register"),
    ("then 167 spare", "then 130 spare"),
    ("table221.length = 229", f"table218.length = {tlen}"),
    ("221", "218"),
])

derive("generate_source219_lean.py", "generate_source218_lean.py", [
    ('"Computability/BusyBeaver/Research/ZFC/candidate-k219/sites219.json"',
     '"Computability/BusyBeaver/Research/ZFC/candidate-k218/sites218.json"'),
    ("candidate-k219/sites219.json", "candidate-k218/sites218.json"),
    ("SITES219", "SITES218"),
    ("KSource219", "KSource218"),
    ("p219", "p218"),
    ("t219", "t218"),
    ("the 219's", "the 218's"),
    ("generate_source219_lean.py", "generate_source218_lean.py"),
])

derive("generate_sites221_lean.py", "generate_sites218_lean.py", [
    ('HERE.parent / "candidate-k221" / "sites_logical.json"', 'HERE.parent / "candidate-k218" / "sites218.json"'),
    ("221", "218"),
])

derive("generate_dense219_lean.py", "generate_dense218_lean.py", [
    ('HERE.parent / "candidate-k219" / "k219.tm"', 'HERE.parent / "candidate-k218" / "k218.tm"'),
    ('HERE / "lean219" / "labels.json"', 'HERE / "lean218" / "labels.json"'),
    ("for q in range(219) for b in (0, 1)", "for q in range(218) for b in (0, 1)"),
    ("len(labels) == 220 and labels[219] == 230 and len(set(labels)) == 220",
     "len(labels) == 219 and labels[218] == 230 and len(set(labels)) == 219"),
    ("for q in range(219))", "for q in range(218))"),
    ("labels[:219]", "labels[:218]"),
    ("states `0 .. 218`, target `219` halts", "states `0 .. 217`, target `218` halts"),
    ("states 0..218, target 219 = halt", "states 0..217, target 218 = halt"),
    ("`next = 219` halts", "`next = 218` halts"),
    ("rows219.getD q.val ((false, true, 219), (false, true, 219))", "rows219.getD q.val ((false, true, 218), (false, true, 218))"),
    ("x.2.2 < 219", "x.2.2 < 218"),
    ("rows219.length = 219", "rows219.length = 218"),
    ("all 219 states", "all 218 states"),
    ("Source 140's", "Source 144's"),
    ("lean219", "lean218"),
    ("219", "218"),
])
# the label map has 219 entries: 218 working states and the halt
g = HERE / "generate_dense218_lean.py"
t = g.read_text(encoding="utf-8")
a = "len(labels) == 218 and labels[218] == 230 and len(set(labels)) == 218"
assert t.count(a) == 1
g.write_text(t.replace(a, "len(labels) == 219 and labels[218] == 230 and len(set(labels)) == 219"),
             encoding="utf-8", newline="\n")
print("labels: max sparse", tlen - 1)
