"""Prepare the 217's Lean inputs and derived generators (candidate-k217, Source 152).

  python prepare_k217.py

The 217 runs the dominated program of Source 149 (`dagDom`, make_dagdom.py; its calculus is
`KCodeDom.CDom`, equivalent to C222), so its program layer is new; its engine rows are the
219's (K230's register rows and the increment bypass `198/0 → 1 L 40`). This script writes

1. `lean217/k217_k230labels.tm` (native table, halt 254 -> 230, new states 301, 302 -> the
   freed labels 102, 120, as for the 219) and `lean217/labels.json` (dense -> sparse);
2. `generate_boot217_lean.py` (312,617 steps, gap 144, 130 spare blocks, as for the 219),
   `generate_source217_lean.py` (p217 against dagDom), `generate_sites217_lean.py` and
   `generate_dense217_lean.py`, by checked substitutions in the 221/219 generators.
"""
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
CAND = HERE.parent / "candidate-k217"
OUT = HERE / "lean217"
OUT.mkdir(exist_ok=True)
REN = {254: 230, 301: 102, 302: 120}

native = {}
for line in open(CAND / "k217.native.tm"):
    if line.startswith("#") or not line.strip():
        continue
    q, b, w, d, n = line.split()
    native[int(q), int(b)] = (w, d, int(n))
used = {q for q, _ in native}
assert not (used & {102, 120, 230}), used & {102, 120, 230}
assert len(used) == 217
lines = ["#! start 0"]
for (q, b), (w, d, n) in sorted(native.items()):
    lines.append(f"{REN.get(q, q)} {b} {w} {d} {REN.get(n, n)}")
(OUT / "k217_k230labels.tm").write_text("\n".join(lines) + "\n", encoding="utf-8", newline="\n")

canon = json.load(open(CAND / "canonicalization.json"))
assert canon["working_states"] == 217 and canon["halt"] == 217 and canon["start"] == 0
c2n = {int(c): int(n) for n, c in canon["native_to_canonical"].items()}
dense = [REN.get(c2n[i], c2n[i]) for i in range(218)]
assert dense[217] == 230 and dense[0] == 0 and len(set(dense)) == 218
json.dump({"dense_to_sparse": dense, "renaming": {str(k): v for k, v in REN.items()}},
          open(OUT / "labels.json", "w", newline="\n"), indent=1)


def derive(src, dst, subs):
    t = (HERE / src).read_text(encoding="utf-8")
    for a, b in subs:
        assert a in t, (src, a)
        t = t.replace(a, b)
    (HERE / dst).write_text(t, encoding="utf-8", newline="\n")
    print("wrote", dst)


tlen = max(REN.get(q, q) for q in used) + 1
derive("generate_boot221_lean.py", "generate_boot217_lean.py", [
    ('rocq/rocq-extension/inputs/221/table_k230labels.tm', 'lean217/k217_k230labels.tm'),
    ("STEPS = 409835", "STEPS = 312617"),
    ("regs = [0, 0, 0, 3, 0, 0, 3, 0, 0] + [1] * 167", "regs = [0, 0, 0, 3, 0, 0, 3, 0, 0] + [1] * 130"),
    ("right = [False] * 181 + [True] + sepsR(regs)", "right = [False] * 144 + [True] + sepsR(regs)"),
    ("List.replicate 167 1", "List.replicate 130 1"),
    ("List.replicate 181 false", "List.replicate 144 false"),
    ("After 409,835 steps", "After 312,617 steps"),
    ("a gap of 181 blank cells, and 176 register", "a gap of 144 blank cells, and 139 register"),
    ("then 167 spare", "then 130 spare"),
    ("table221.length = 229", f"table217.length = {tlen}"),
    ("221", "217"),
])

derive("generate_source219_lean.py", "generate_source217_lean.py", [
    ('"Computability/BusyBeaver/Research/ZFC/candidate-k219/sites219.json"',
     '"Computability/BusyBeaver/Research/ZFC/candidate-k217/sites217.json"'),
    ("candidate-k219/sites219.json", "candidate-k217/sites217.json"),
    ("SITES219", "SITES217"),
    ("import BusyBeaver.ZFC.Dag219", "import BusyBeaver.ZFC.DagDom"),
    ("Dag219.dag219", "DagDom.dagDom"),
    ("pathDag219", "pathDagDom"),
    ("dag219", "dagDom"),
    ("Dag219.seed_iff", "L2Dom.dagDom_seed_iff"),
    ("KSource219", "KSource217"),
    ("KEndpoint219", "KEndpoint217"),
    ("the 219-state machine", "the 217-state machine"),
    ("p219", "p217"),
    ("t219", "t217"),
    ("the 219's", "the 217's"),
    ("generate_source219_lean.py", "generate_source217_lean.py"),
])

derive("generate_sites221_lean.py", "generate_sites217_lean.py", [
    ('HERE.parent / "candidate-k221" / "sites_logical.json"', 'HERE.parent / "candidate-k217" / "sites217.json"'),
    ("221", "217"),
])

derive("generate_dense219_lean.py", "generate_dense217_lean.py", [
    ('HERE.parent / "candidate-k219" / "k219.tm"', 'HERE.parent / "candidate-k217" / "k217.tm"'),
    ('HERE / "lean219" / "labels.json"', 'HERE / "lean217" / "labels.json"'),
    ("for q in range(219) for b in (0, 1)", "for q in range(217) for b in (0, 1)"),
    ("len(labels) == 220 and labels[219] == 230 and len(set(labels)) == 220",
     "len(labels) == 218 and labels[217] == 230 and len(set(labels)) == 218"),
    ("for q in range(219))", "for q in range(217))"),
    ("labels[:219]", "labels[:217]"),
    ("states `0 .. 218`, target `219` halts", "states `0 .. 216`, target `217` halts"),
    ("states 0..218, target 219 = halt", "states 0..216, target 217 = halt"),
    ("`next = 219` halts", "`next = 217` halts"),
    ("rows219.getD q.val ((false, true, 219), (false, true, 219))", "rows219.getD q.val ((false, true, 217), (false, true, 217))"),
    ("x.2.2 < 219", "x.2.2 < 217"),
    ("rows219.length = 219", "rows219.length = 217"),
    ("all 219 states", "all 217 states"),
    ("Source 140's", "Source 152's"),
    ("lean219", "lean217"),
    ("219", "217"),
])
tg = HERE / "generate_tables_lean.py"
t = tg.read_text(encoding="utf-8")
if '"217":' not in t:
    a = '''            "labels 102, 120, as for the 219); 230 is terminal."),
}'''
    assert t.count(a) == 1
    t = t.replace(a, '''            "labels 102, 120, as for the 219); 230 is terminal."),
    "217": ("The 217-state machine's table in K230 labels (`lean217/k217_k230labels.tm`: Source 152's\\n"
            "native table with halt 254 renamed 230 and the states 301, 302 renamed into the freed\\n"
            "labels 102, 120, as for the 219); 230 is terminal."),
}''')
    tg.write_text(t, encoding="utf-8", newline="\n")
print("labels: max sparse", tlen - 1)
