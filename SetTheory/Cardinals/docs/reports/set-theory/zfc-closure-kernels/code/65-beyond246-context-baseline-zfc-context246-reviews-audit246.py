#!/usr/bin/env python3
"""Independent finite/support audit of the 246-state specialization.

Arguments: path to the extracted prefix250 independent-audit package.
This script imports its audited induction engine as an explicit dependency,
replaces the table in memory, and checks every unbounded register contract
and every guarded instruction against the changed literal table.  No
inherited source or result file is changed.
"""
from collections import Counter
from hashlib import sha256
from pathlib import Path
import json
import sys

if not __debug__:
    raise SystemExit("Run with Python assertions enabled.")

prior = Path(sys.argv[1]).resolve()
sys.path.insert(0, str(prior / "code"))
import rebuild_machines as inherited
import affine_engine as affine
import check_macro_inductions as induction
import check_instructions as instruction

baseline = inherited.build()
table = {k: v for k, v in baseline.items() if k[0] not in {0, 1, 3, 97}}
table[60, 0] = (0, "R", 20)
table[255, 0] = (1, "L", 255)
states = {q for q, _ in table}
assert len(states) == 246 and len(table) == 492
assert set(table) == {(q, b) for q in states for b in (0, 1)}
assert {q for _, _, q in table.values()} - states == {254}
assert [(k, v) for k, v in table.items() if v[2] == 254] == [((77, 1), (1, "R", 254))]
assert baseline[0, 1] == table[20, 1] == (0, "L", 2)
assert baseline[97, 1] == table[255, 1] == (1, "L", 131)
assert [(k, v) for k, v in baseline.items() if v[2] == 0] == [((60, 0), (0, "R", 0))]
assert [(k, v) for k, v in baseline.items() if v[2] == 97] == [((255, 0), (1, "L", 97))]

class LoggedTable(dict):
    def __init__(self, values):
        super().__init__(values)
        self.reads = Counter()

    def __getitem__(self, key):
        self.reads[key] += 1
        return super().__getitem__(key)

macro_table = LoggedTable(table)
induction.TABLE = macro_table
induction.prove_blocks()
identity = induction.prove_word_identity()
macro_proofs = induction.prove_macros()
mark_proofs = induction.prove_marks()
assert len(induction.BLOCK_PROOFS) == 4
assert len(macro_proofs) == 3 and len(mark_proofs) == 9
assert all(p["status"] == "PASS" for p in macro_proofs + mark_proofs)

literal_table = LoggedTable({(str(q), b): (w, d, str(t)) for (q, b), (w, d, t) in table.items()})
cases = 0
minimum = 10**9
maximum = 0
rules_total = Counter()
sites = inherited.program_sites()
for pc, op, logical in sites:
    r = inherited.PHYSICAL[logical] if op in ("CI", "CD") else logical
    for zero in ((True, False) if op == "CD" else (None,)):
        branch = (r, zero) if op == "CD" else None
        if op == "CI" or (op == "CD" and not zero):
            successor = instruction.increment(pc)
        elif op == "CD":
            successor = instruction.increment(instruction.strip(pc, "0", 1))
        elif op == "CB":
            successor = instruction.increment(instruction.strip(pc, "0", r))
        elif op == "CC":
            successor = instruction.strip(pc, "1", r)
        else:
            successor = ""
        effect = ("inc", r) if op == "CI" else (("dec", r) if op == "CD" and not zero else None)
        extra = int(op == "CD" and not zero)
        if successor is None:
            right = [("r", 0, 1, 41 + extra), ("b", 1), ("box", ("plain", effect))]
        else:
            right = [("b", int(b)) for b in successor] + [
                ("r", 0, 1, 40 + extra - len(successor)), ("b", 1), ("box", ("plain", effect))]
        rules, literal = affine.run(literal_table, pc, branch,
            affine.canon([("b", 1)], right), halt=op == "CH", fuel=1000)
        cases += 1
        minimum = min(minimum, literal)
        maximum = max(maximum, sum(rules.values()))
        rules_total.update(rules)
assert cases == 8391 and minimum > 0

def sparse_boot(steps):
    q, h, ones = 95, 0, set()
    changed = Counter()
    for _ in range(steps):
        assert q != 254
        key = q, int(h in ones)
        if key in {(60, 0), (255, 0)}:
            changed[key] += 1
        w, d, q = table[key]
        if w:
            ones.add(h)
        else:
            ones.discard(h)
        h += 1 if d == "R" else -1
    return q, h, ones, changed

def dense_boot(steps):
    # The fixed interval is independently checked at every step.
    offset = 200000
    bits = bytearray(400001)
    q, p = 95, offset
    for _ in range(steps):
        assert q != 254 and 0 <= p < len(bits)
        w, d, q = table[q, bits[p]]
        bits[p] = w
        p += {"L": -1, "R": 1}[d]
    return q, p - offset, {i - offset for i, b in enumerate(bits) if b}

steps = 410735
q, h, ones, changed = sparse_boot(steps)
assert dense_boot(steps) == (q, h, ones)
assert (q, h) == (96, -5)
assert min(ones) == h - 1
right = sorted(x for x in ones if x >= h)
header = right[0]
assert header == 176
p = header + 1
values = []
while p <= max(ones):
    assert p not in ones and p + 1 in ones
    p += 1
    length = 0
    while p in ones:
        p += 1
        length += 1
    values.append(length - 1)
assert values[:9] == [0, 0, 0, 3, 0, 0, 3, 0, 0]
assert values[9:] == [1] * 167
paint = {h - 1, header}
p = header + 1
for v in values:
    paint.update(range(p + 1, p + v + 2))
    p += v + 2
assert ones == paint
logical = [values[inherited.PHYSICAL[i]] for i in range(9)]
assert logical == [3, 0, 0, 0, 3, 0, 0, 0, 0]

old_text = inherited.encode(table, 95)
order = [95] + sorted(states - {95})
renumber = {q: i for i, q in enumerate(order)} | {254: 246}
canonical = {(renumber[q], b): (w, d, renumber[t]) for (q, b), (w, d, t) in table.items()}
canonical_text = inherited.encode(canonical, 0)

output = dict(
    status="PASS",
    claim_scope="Ordinary symbolic-induction proof audit; no new Lean/Rocq kernel endpoint.",
    working_states=246,
    binary_transitions=492,
    halt_transitions=1,
    start_old=95,
    start_canonical=0,
    deleted_from_prefix250=[0, 1, 3, 97],
    changed_surviving_rows=[[[60, 0], [0, "R", 20]], [[255, 0], [1, "L", 255]]],
    original_label_sha256=sha256(old_text.encode("ascii")).hexdigest(),
    canonical_sha256=sha256(canonical_text.encode("ascii")).hexdigest(),
    block_inductions=list(induction.BLOCK_PROOFS.values()),
    word_identity=identity,
    register_macro_inductions=macro_proofs,
    marking_inductions=mark_proofs,
    macro_rows_consulted=[[list(k), v] for k, v in sorted(macro_table.reads.items())],
    guarded_instruction_cases=cases,
    decoder_nodes=6459,
    decoder_leaves=len(sites),
    minimum_literal_steps=minimum,
    maximum_rules=maximum,
    instruction_rule_totals=dict(rules_total),
    instruction_rows_consulted=[[list(k), v] for k, v in sorted(literal_table.reads.items())],
    bootstrap=dict(steps=steps, state=q, head=h, header=header, distance=header-h,
        pc=[], physical=values[:9], logical=logical, spares=values[9:],
        one_count=len(ones), all_one_positions=sorted(ones),
        independent_dense_and_sparse_agree=True,
        changed_row_visits=[[list(k), v] for k, v in sorted(changed.items())]),
    exact_safe_root="DirtyProgram254.six_nonformula_path_iff 3 0 3 0 0 0",
    proof_boundary="All local box contracts are rerun on the changed literal table; all guards freshly parse full Prog254.v. Global composition and Con bridge are ordinary mathematical arguments using identified inherited results.",
)
destination = Path(__file__).resolve().with_name("audit246-results.json")
destination.write_text(json.dumps(output, indent=2) + "\n")
print(json.dumps({k:v for k,v in output.items() if k not in {
    "block_inductions", "register_macro_inductions", "marking_inductions", "macro_rows_consulted",
    "instruction_rows_consulted", "instruction_rule_totals", "bootstrap"}}, indent=2))
print(json.dumps({"bootstrap": {k:v for k,v in output["bootstrap"].items() if k not in {"all_one_positions", "spares"}},
    "spare_count":len(values)-9, "result":str(destination)}, indent=2))
