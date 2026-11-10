#!/usr/bin/env python3
"""Transcribe the inert Carrier65 graph to an ArithmeticDAG source draft.

This generator does not run Lean or prove equivalence to the displayed page.
"""
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
GRAPH = HERE.parent / "carrier65-independent" / "INCOMING_CARRIER65.json"
data = json.loads(GRAPH.read_text())
inputs = ["J", "F", "alpha", "z", "f", "i", "T", "s", "w", "n", "eta", "zeta", "y", "gamma"]
ports = ["beta", "K0", "MC", "MF"]
assert data["witnesses"] == inputs and data["fixed_numerals"] == ports
assert data["operations"] == len(data["source"]) == 65
nodes, names = [], {}

def add(name, body):
    assert name not in names
    names[name] = len(nodes)
    nodes.append((name, body))

for i, name in enumerate(inputs):
    add(name, f".input ⟨{i}, by decide⟩")
for i, name in enumerate(ports):
    add(name, f".constant ⟨{i}, by decide⟩")
for n in (1, 3, 4):
    add(n, f".literal {n}")
ops = {"+": "add", "-": "sub", "*": "mul"}
for name, op, a, b in data["source"]:
    assert op in ops and a in names and b in names
    add(name, f".{ops[op]} {names[a]} {names[b]}")
output = names[data["output"]]
assert output == len(nodes) - 1
consumers = []
for ix, (name, body) in enumerate(nodes[:-1]):
    later = [j for j, (_, _, a, b) in enumerate(data["source"], len(inputs) + len(ports) + 3)
             if names[a] == ix or names[b] == ix]
    assert later and min(later) > ix, name
    consumers.append(min(later))
sha = hashlib.sha256(GRAPH.read_bytes()).hexdigest()
lines = ["import DiophantineConsistency.ArithmeticDAG",
         "import DiophantineConsistency.Carrier65", "", "/-!",
         "Source-only candidate: 65 binary gates, with arbitrary input and port values.",
         "The graph transcription and all proof bodies still require review and Lean checking.",
         f"External graph SHA256: {sha}", "-/",
         "namespace DiophantineConsistency.Current14Carrier65DAG", "open ArithmeticDAG", "",
         "def nodes : List (Node 14 4) :=", "  ["]
for j, (name, body) in enumerate(nodes):
    comma = "," if j < len(nodes) - 1 else ""
    lines.append(f"    {body}{comma} -- {j}: {name}")
lines.extend(["  ]", "", f"def output : ℕ := {output}", "",
              "def consumers : List ℕ :=", "  [" + ", ".join(map(str, consumers)) + "]", "",
              f"theorem nodes_length : nodes.length = {len(nodes)} := by decide +kernel", "",
              "theorem topological : Topological nodes := by decide +kernel", "",
              f"private theorem consumer_certificate : ∀ i : Fin {output},",
              "    i.val < consumers.getD i.val 0 ∧",
              f"    consumers.getD i.val 0 ≤ {output} ∧",
              "    i.val ∈ (nodes.getD (consumers.getD i.val 0) (.literal 0)).dependencies :=",
              "  by decide +kernel", "",
              "theorem all_live (i : ℕ) (hi : i < nodes.length) : Reaches nodes output i := by",
              f"  exact reaches_of_consumer_table nodes consumers {output} nodes_length consumer_certificate i hi", "",
              "theorem operation_count : operationCount nodes = 65 := by decide +kernel",
              "theorem addition_count : kindCount nodes 3 = 16 := by decide +kernel",
              "theorem subtraction_count : kindCount nodes 4 = 12 := by decide +kernel",
              "theorem multiplication_count : kindCount nodes 5 = 37 := by decide +kernel", "",
              "theorem live_operation_count : liveOperationCount nodes output = 65 := by",
              "  rw [liveOperationCount_eq nodes output all_live]", "  exact operation_count", "",
              "theorem all_inputs : ∀ i : Fin 14, Node.input i ∈ nodes := by decide +kernel",
              "theorem all_ports : ∀ i : Fin 4, Node.constant i ∈ nodes := by decide +kernel", "",
              "/-- This is the essential bridge from the counted DAG to the maintained polynomial. -/",
              "theorem value_eq_carrier {R : Type*} [CommRing R]",
              "    (p : Fin 4 → R) (v : Fin 14 → R) :",
              "    value nodes output p v = Carrier65.value p v := by",
              "  simp only [value, output, nodes, run, Node.eval, List.getD,",
              "    List.append, Carrier65.value, Carrier65.core, pow_succ, pow_zero,",
              "    one_mul, mul_one, mul_assoc]", "",
              "end DiophantineConsistency.Current14Carrier65DAG", ""])
(HERE / "Current14Carrier65DAG.lean").write_text("\n".join(lines))
print(f"{len(nodes)} nodes, {output} output, {len(consumers)} consumer entries; graph sha256 {sha}")
