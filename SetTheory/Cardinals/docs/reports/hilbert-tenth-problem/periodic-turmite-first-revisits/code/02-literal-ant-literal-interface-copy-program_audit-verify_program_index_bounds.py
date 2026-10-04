#!/usr/bin/env python3
"""Independent finite grammar audit; never expands physical instruction rows.

The endpoint checks below are exhaustive checks of arithmetic grammar intervals,
not random samples. The accompanying proof explains why each decoder's branch
and affine output are constant/affine throughout its checked intervals.
Only this directory receives output. Production files are read-only inputs.
"""
import collections
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
CA = HERE.parent.parent / "ca"
source = (CA / "physical_program.py").read_bytes()
program_bytes = (CA / "physical_program.json").read_bytes()
dag_bytes = (CA / "fixed_ca_cell.json").read_bytes()
p = json.loads(program_bytes)
dag = json.loads(dag_bytes)
ns = {"__name__": "independent_audit_target", "__file__": str(CA / "physical_program.py")}
exec(compile(source, str(CA / "physical_program.py"), "exec"), ns)
target_instruction = ns["instruction"]

# This independent literal list is checked against the source's construction.
swap = [
    ("DUP", 0), ("DUP", 2), ("DUP", 1), ("DUP", 3),
    ("NAND", 2), ("DUP", 2), ("NAND", 1), ("NAND", 2),
    ("NAND", 1), ("DUP", 1), ("DUP", 0), ("DUP", 2),
    ("NAND", 1), ("DUP", 1), ("NAND", 0), ("NAND", 1),
    ("NAND", 0), ("DUP", 1), ("DUP", 3), ("NAND", 2),
    ("DUP", 2), ("NAND", 1), ("NAND", 2), ("NAND", 1),
]
assert ns["SWAP"] == swap
delta = 0
swap_stages = []
for op, j in swap:
    # Check the smallest allowed residual width r=2; all constraints only
    # become weaker as r increases. The logical operations stay in the pair.
    assert 0 <= j < 2 + delta - (op == "NAND")
    c = delta - j - (op == "NAND")
    assert 2 + c > 0
    swap_stages.append({"op": op, "j": j, "delta": delta, "length_constant": c})
    delta += 1 if op == "DUP" else -1
assert delta == 0
assert len(swap) == 24
assert sum(s["length_constant"] for s in swap_stages) == 14
assert max(s["delta"] + (s["op"] == "DUP") for s in swap_stages) == 4
assert sum(s["op"] == "DUP" for s in swap_stages) == 12
assert sum(s["delta"] - s["j"] - 1 for s in swap_stages if s["op"] == "DUP") == -7
assert sum(s["delta"] - s["j"] - 2 for s in swap_stages if s["op"] == "NAND") == -3
assert min(s["j"] for s in swap_stages) == 0
assert max(s["delta"] - (1 if s["op"] == "DUP" else 2) for s in swap_stages) == 2

# Four-bit truth planes cover every assignment (a,b), independently of suffix.
w = [0b1100, 0b1010]
for op, j in swap:
    if op == "DUP":
        w[j:j+1] = [w[j], w[j]]
    else:
        w[j:j+2] = [15 ^ (w[j] & w[j+1])]
assert w == [0b1010, 0b1100]

def copy_count(r):
    assert r >= 1
    return collections.Counter(DUP=12*r-11, NAND=12*r-12,
                               MOVE_RIGHT=6*r*r-6, MOVE_LEFT=6*r*r+3*r-9)

def copy_len(r):
    return 12*r*r + 27*r - 38

def cp(r, t):
    return 12*t*(2*r-t) + 26*t

def measure(n):
    """Independent exact row count and exact min/max left pair indices."""
    typ = n["type"]
    if typ == "ROW":
        return collections.Counter({n["op"]: 1}), n["i"], n["i"]
    if typ == "RANGE":
        rr = range(n["start"], n["stop"], n["step"])
        assert len(rr) > 0
        return collections.Counter({n["op"]: len(rr)}), min(rr[0], rr[-1]), max(rr[0], rr[-1])
    if typ == "COPY":
        m, i = n["m"], n["i"]
        assert m >= 1 and 0 <= i < m
        return copy_count(m-i), i, (m-1 if i == m-1 else m+3)
    if typ == "GATE":
        m, u, v = n["m"], n["u"], n["v"]
        assert 0 <= u < m and 0 <= v < m
        counts = copy_count(m-u) + copy_count(m+1-v)
        counts["NAND"] += 1
        return counts, min(u, v), m+4
    raise AssertionError(typ)

# Independently reconstruct the intended grammar from its raw DAG and constants.
assert dag["input_count"] == 24
assert len(dag["complemented_phi_outputs"]) == 24
expected = []
for j in range(1, 24):
    expected.append(dict(type="RANGE", op="MOVE_LEFT", start=40*j-1,
                         stop=j-1, step=-1, purpose="gather_input"))
for j, (u, v) in enumerate(dag["nand_gates"]):
    assert 0 <= u < 24+j and 0 <= v < 24+j
    expected.append(dict(type="GATE", m=24+j, u=u, v=v))
base_output = 24 + len(dag["nand_gates"])
width = base_output
for port in dag["complemented_phi_outputs"] + [dag["halt_wire"]]:
    assert 0 <= port < base_output
    expected.append(dict(type="COPY", m=width, i=port))
    width += 1
observer_node = len(expected)
expected.append(dict(type="ROW", op="DUP", i=width-1, purpose="halt_observer_copy"))
for j in range(24):
    expected.append(dict(type="RANGE", op="MOVE_LEFT", start=base_output+j-1,
                         stop=j-1, step=-1, purpose="gather_outputs"))
for j in range(23, 0, -1):
    expected.append(dict(type="RANGE", op="MOVE_RIGHT", start=j,
                         stop=40*j, step=1, purpose="scatter_outputs"))
assert expected == p["nodes"]

prefix = [0]
totals = collections.Counter()
groups = {}
bounds = []
copy_rs = set()
compiler_peak = 24
for j, n in enumerate(expected):
    counts, lo, hi = measure(n)
    L = sum(counts.values())
    assert L > 0 and L == ns["length"](n)
    assert 0 <= lo <= hi < p["active_columns"] - 1
    totals.update(counts)
    prefix.append(prefix[-1] + L)
    category = n.get("purpose", n["type"])
    g = groups.setdefault(category, dict(nodes=0, rows=0, pair_min=lo, pair_max=hi))
    g["nodes"] += 1
    g["rows"] += L
    g["pair_min"] = min(g["pair_min"], lo)
    g["pair_max"] = max(g["pair_max"], hi)
    if n["type"] == "GATE":
        copy_rs.update([n["m"]-n["u"], n["m"]+1-n["v"]])
        compiler_peak = max(compiler_peak, n["m"]+6)
    elif n["type"] == "COPY":
        copy_rs.add(n["m"]-n["i"])
        compiler_peak = max(compiler_peak, n["m"]+(1 if n["i"] == n["m"]-1 else 5))
    bounds.append(dict(node=j, type=n["type"], row_start=prefix[-2], row_stop=prefix[-1],
                       rows=L, pair_min=lo, pair_max=hi))
assert prefix == p["prefix_rows"]
assert prefix[-1] == p["program_rows"]
assert prefix[observer_node] == p["observer_row_index"]
assert width-1 == p["observer_column_index"]
assert compiler_peak <= p["maximum_live_compiler_word"] <= p["active_columns"]

# Replace only the in-memory recursion dispatcher to observe the production
# decoder's chosen immediate child and residual. The source files are unchanged.
def capture(n, k):
    return n, k

ns["instruction"] = capture
row_intervals = 0
for j, n in enumerate(expected):
    for k in (prefix[j], prefix[j+1]-1):
        assert ns["row_at"](p, k) == (n, k-prefix[j])
    row_intervals += 1

gate_intervals = 0
for n in expected:
    if n["type"] != "GATE":
        continue
    a = dict(type="COPY", m=n["m"], i=n["u"])
    b = dict(type="COPY", m=n["m"]+1, i=n["v"])
    la, lb = copy_len(n["m"]-n["u"]), copy_len(n["m"]+1-n["v"])
    for offset, child, L in ((0, a, la), (la, b, lb)):
        for local in (0, L-1):
            assert target_instruction(n, offset+local) == (child, local)
        gate_intervals += 1
    assert target_instruction(n, la+lb) == ("NAND", n["m"])
    gate_intervals += 1

copy_intervals = 0
for r in sorted(copy_rs):
    node = dict(type="COPY", m=r, i=0)
    assert ns["length"](node) == copy_len(r) == r + cp(r, r-1)
    for k in (0, r-1):
        assert target_instruction(node, k) == (dict(type="WORD", op="DUP", m=r, i=0), k)
    copy_intervals += 1
    for t in range(r-1):
        begin, end = cp(r, t), cp(r, t+1)
        assert ns["copyswapprefix"](r, 0, t) == begin
        assert end-begin == 24*(r-t)+14 > 0
        for k in (begin, end-1):
            assert target_instruction(node, r+k) == (dict(type="SWAP", m=r+1, i=1+t), k-begin)
        copy_intervals += 1
    assert ns["copyswapprefix"](r, 0, r-1) == cp(r, r-1)

swap_intervals = 0
word_intervals = 0
for r in range(2, max(copy_rs)+1):
    node = dict(type="SWAP", m=r, i=0)
    offset = 0
    assert ns["length"](node) == 24*r+14
    for s in swap_stages:
        m, i, op = r+s["delta"], s["j"], s["op"]
        L = r+s["length_constant"]
        child = dict(type="WORD", op=op, m=m, i=i)
        assert ns["length"](child) == L
        for local in (0, L-1):
            assert target_instruction(node, offset+local) == (child, local)
        offset += L
        swap_intervals += 1
        # WORD's at most two affine intervals, fully bounded by their endpoints.
        if op == "DUP":
            if L > 1:
                assert target_instruction(child, 0) == ("MOVE_RIGHT", m-1)
                assert target_instruction(child, L-2) == ("MOVE_RIGHT", i+1)
                word_intervals += 1
            assert target_instruction(child, L-1) == ("DUP", i)
        else:
            assert target_instruction(child, 0) == ("NAND", i)
            if L > 1:
                assert target_instruction(child, 1) == ("MOVE_LEFT", i+1)
                assert target_instruction(child, L-1) == ("MOVE_LEFT", m-2)
                word_intervals += 1
        word_intervals += 1
    assert offset == 24*r+14
ns["instruction"] = target_instruction

assert all(p[k] == v for k, v in ns["make_program"]().items())
assert p["NAND_DAG_sha256"] == hashlib.sha256(dag_bytes).hexdigest()
assert p["source_sha256"] == hashlib.sha256(source).hexdigest()
assert p["tile_slots"] == 960 and p["active_columns"] == 958
assert p["CA_macro_width"] == 600*960
assert p["CA_macro_height"] == 400*(prefix[-1]+2)
assert p["rectangular_vertical_period"] == 800*(prefix[-1]+2)
assert ns["row_at"](p, p["observer_row_index"]) == ("DUP", 910)

result = dict(
    status="PASS_INDEPENDENT_EXACT_GRAMMAR_INDEX_AUDIT",
    inputs_sha256={"physical_program.py": hashlib.sha256(source).hexdigest(),
                   "physical_program.json": hashlib.sha256(program_bytes).hexdigest(),
                   "fixed_ca_cell.json": hashlib.sha256(dag_bytes).hexdigest()},
    compressed_nodes=len(expected), program_rows=prefix[-1], physical_pair_rows=dict(totals),
    prefix_entries=len(prefix), prefix_strictly_increasing=True,
    row_at_intervals_checked=row_intervals, gate_intervals_checked=gate_intervals,
    copy_quotient_intervals_checked=copy_intervals, swap_word_intervals_checked=swap_intervals,
    word_affine_intervals_checked=word_intervals,
    distinct_copy_residual_widths=len(copy_rs), maximum_copy_residual_width=max(copy_rs),
    exact_global_pair_left_index_range=[min(b["pair_min"] for b in bounds), max(b["pair_max"] for b in bounds)],
    exact_highest_touched_column=max(b["pair_max"] for b in bounds)+1,
    active_columns=p["active_columns"], highest_active_column=p["active_columns"]-1,
    exact_peak_live_compiler_word=compiler_peak,
    declared_safe_compiler_word_bound=p["maximum_live_compiler_word"],
    observer_row_index=p["observer_row_index"], observer_column_index=p["observer_column_index"],
    groups=groups, bugs_found=[],
    proof_scope="Exact abstract pair-instruction grammar, decoder, Boolean word semantics, and active-column capacity. No literal-color geometry or collision certification; no dense row expansion or random sampling.",
    proof_file="ANALYSIS.md", node_bounds_file="node_bounds.json",
)
(HERE / "receipt.json").write_text(json.dumps(result, indent=2)+"\n")
(HERE / "node_bounds.json").write_text(json.dumps(bounds, indent=2)+"\n")
print(json.dumps(result, indent=2))
