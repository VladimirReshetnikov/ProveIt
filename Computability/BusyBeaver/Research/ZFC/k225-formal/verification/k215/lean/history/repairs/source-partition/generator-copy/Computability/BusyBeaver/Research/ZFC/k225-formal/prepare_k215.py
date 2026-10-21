"""Prepare the 215's Lean inputs and derived generators (candidate-k215).

  python prepare_k215.py

The 215 runs Source 159's command-permuted program on Source 149's dominated AX (`dagPerm`,
make_dagperm.py; enumerator `EnumPerm`); its engine rows are the 219's. Its blank startup is new:
95,714 steps to the root with `nextproof = 4` and every other register zero, 65 zero cells
between the PC marker and the register header (one more than `KSim.D0`; the candidate's
"header 57, gap 1" counts from the head at -8) and 40 spare blocks. This script writes

1. `lean215/k215_k230labels.tm` (native table, halt 254 -> 230, new states 301, 302 -> the
   freed labels 102, 120, as for the 219) and `lean215/labels.json` (dense -> sparse);
2. `generate_boot215_lean.py`, `generate_source215_lean.py` (p215 against dagPerm),
   `generate_sites215_lean.py` and `generate_dense215_lean.py`, by checked substitutions in the
   221/219 generators.
"""
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
CAND = HERE.parent / "candidate-k215"
OUT = HERE / "lean215"
OUT.mkdir(exist_ok=True)
REN = {254: 230, 301: 102, 302: 120}

native = {}
for line in open(CAND / "k215.native.tm"):
    if line.startswith("#") or not line.strip():
        continue
    q, b, w, d, n = line.split()
    native[int(q), int(b)] = (w, d, int(n))
used = {q for q, _ in native}
assert not (used & {102, 120, 230}), used & {102, 120, 230}
assert len(used) == 215
lines = ["#! start 0"]
for (q, b), (w, d, n) in sorted(native.items()):
    lines.append(f"{REN.get(q, q)} {b} {w} {d} {REN.get(n, n)}")
(OUT / "k215_k230labels.tm").write_text("\n".join(lines) + "\n", encoding="utf-8", newline="\n")

canon = json.load(open(CAND / "canonicalization.json"))
c2n = {int(c): int(n) for c, n in canon["canonical_to_native"].items()}
dense = [REN.get(c2n[i], c2n[i]) for i in range(216)]
assert dense[215] == 230 and dense[0] == 0 and len(set(dense)) == 216, dense[:3]
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
derive("generate_boot221_lean.py", "generate_boot215_lean.py", [
    ('rocq/rocq-extension/inputs/221/table_k230labels.tm', 'lean215/k215_k230labels.tm'),
    ("STEPS = 409835", "STEPS = 95714"),
    ("regs = [0, 0, 0, 3, 0, 0, 3, 0, 0] + [1] * 167", "regs = [0, 0, 0, 0, 0, 0, 4, 0, 0] + [1] * 40"),
    ("right = [False] * 181 + [True] + sepsR(regs)", "right = [False] * 65 + [True] + sepsR(regs)"),
    ("[0, 0, 0, 3, 0, 0, 3, 0, 0]", "[0, 0, 0, 0, 0, 0, 4, 0, 0]"),
    ("(`nextproof = 3`, `param1 = 3`)", "(`nextproof = 4`, all other registers zero)"),
    ("for 409,835 steps", "for 95,714 steps"),
    ("and K230's boot tape to the right", "and the 215's boot tape to the right"),
    ("List.replicate 167 1", "List.replicate 40 1"),
    ("List.replicate 181 false", "List.replicate 65 false"),
    ("After 409,835 steps", "After 95,714 steps"),
    ("a gap of 181 blank cells, and 176 register", "a gap of 65 blank cells, and 49 register"),
    ("then 167 spare", "then 40 spare"),
    ("table221.length = 229", f"table215.length = {tlen}"),
    ("221", "215"),
])

derive("generate_source219_lean.py", "generate_source215_lean.py", [
    ('"Computability/BusyBeaver/Research/ZFC/candidate-k219/sites219.json"',
     '"Computability/BusyBeaver/Research/ZFC/candidate-k215/sites215.json"'),
    ("candidate-k219/sites219.json", "candidate-k215/sites215.json"),
    ("SITES219", "SITES215"),
    ("import BusyBeaver.ZFC.Dag219", "import BusyBeaver.ZFC.DagPerm"),
    ("Dag219.dag219", "DagPerm.dagPerm"),
    ("pathDag219", "pathDagPerm"),
    ("dag219", "dagPerm"),
    ("Dag219.seed_iff", "L2Perm.dagPerm_seed_iff"),
    ("KSource219", "KSource215"),
    ("KEndpoint219", "KEndpoint215"),
    ("the 219-state machine", "the 215-state machine"),
    ("p219", "p215"),
    ("t219", "t215"),
    ("the 219's", "the 215's"),
    ("generate_source219_lean.py", "generate_source215_lean.py"),
    ('from generate_source225_lean import dag, program, literal_tree, cert_block  # noqa: E402', 'from generate_source225_lean import dag, program, literal_tree, cert_block  # noqa: E402\nfrom partition_source215_lean import write_partition  # noqa: E402'),
    ('TARGET.write_text(out, encoding="utf-8", newline="\\n")', 'write_partition(TARGET, out)'),
])

derive("generate_sites221_lean.py", "generate_sites215_lean.py", [
    ('HERE.parent / "candidate-k221" / "sites_logical.json"', 'HERE.parent / "candidate-k215" / "sites215.json"'),
    ("221", "215"),
])

derive("generate_dense219_lean.py", "generate_dense215_lean.py", [
    ('HERE.parent / "candidate-k219" / "k219.tm"', 'HERE.parent / "candidate-k215" / "k215.tm"'),
    ('HERE / "lean219" / "labels.json"', 'HERE / "lean215" / "labels.json"'),
    ("for q in range(219) for b in (0, 1)", "for q in range(215) for b in (0, 1)"),
    ("len(labels) == 220 and labels[219] == 230 and len(set(labels)) == 220",
     "len(labels) == 216 and labels[215] == 230 and len(set(labels)) == 216"),
    ("for q in range(219))", "for q in range(215))"),
    ("labels[:219]", "labels[:215]"),
    ("states `0 .. 218`, target `219` halts", "states `0 .. 214`, target `215` halts"),
    ("states 0..218, target 219 = halt", "states 0..214, target 215 = halt"),
    ("`next = 219` halts", "`next = 215` halts"),
    ("rows219.getD q.val ((false, true, 219), (false, true, 219))", "rows219.getD q.val ((false, true, 215), (false, true, 215))"),
    ("x.2.2 < 219", "x.2.2 < 215"),
    ("rows219.length = 219", "rows219.length = 215"),
    ("all 219 states", "all 215 states"),
    ("Source 140's", "the 215's"),
    ("lean219", "lean215"),
    ("219", "215"),
])

tg = HERE / "generate_tables_lean.py"
t = tg.read_text(encoding="utf-8")
if '"215":' not in t:
    a = '''    "217": ('''
    assert t.count(a) == 1
    t = t.replace(a, '''    "215": ("The 215-state machine's table in K230 labels (`lean215/k215_k230labels.tm`: the 215's\\n"
            "native table with halt 254 renamed 230 and the states 301, 302 renamed into the freed\\n"
            "labels 102, 120, as for the 219); 230 is terminal."),
''' + a)
    tg.write_text(t, encoding="utf-8", newline="\n")
print("labels: max sparse", tlen - 1)
