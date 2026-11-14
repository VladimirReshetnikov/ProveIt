#!/usr/bin/env python3
"""Check the exact source-graph observation; no physical TM reduction claimed."""
from pathlib import Path
import hashlib
import json
import sys

HERE = Path(__file__).resolve().parent
SOURCE = HERE.parents[1] / "reference" / "pa194" / "construction"
sys.path.insert(0, str(SOURCE))
import compiler as c

if not __debug__:
    raise SystemExit("Run without Python -O: assertions check the finite claim.")

grammar = c.read_grammar(SOURCE / "source" / "pa194.grammar.json")
old_sites, old_instructions, _ = c.source(grammar)
nodes = c.raw_nodes()
nodes["node170"] = ("node28", ("node35", "node169"))
nodes["node166"] = ("node165", ("leaf", "continueTo", 4))
c.raw_nodes = lambda: nodes
new_sites, new_instructions, _ = c.source(grammar)
assert len(old_sites) == len(new_sites) == 3673
assert old_instructions == new_instructions
changed = [i for i, (x, y) in enumerate(zip(old_sites, new_sites))
           if x[1:] != y[1:]]
assert changed == [3660]
assert old_sites[3660][1:] == ("continueTo", 3)
assert new_sites[3660][1:] == ("continueTo", 4)
assert old_instructions[3660] == ("jump", 25)
assert "".join(map(str, old_sites[25][0])) == "100000"
assert "".join(map(str, new_sites[25][0])) == "10000"

receipt = {
    "source_sites": 3673,
    "all_resolved_instructions_identical": True,
    "changed_primitive_operand_sites": changed,
    "old_operand": 3,
    "new_operand": 4,
    "resolved_instruction": ["jump", 25],
    "old_shift_entry_path": "100000",
    "new_shift_entry_path": "10000",
    "source_instruction_sha256": hashlib.sha256(
        json.dumps(old_instructions, separators=(",", ":")).encode()
    ).hexdigest(),
    "scope": "Exact finite source-graph identity. No physical scanner reduction is established.",
}
(HERE / "outer_rotation_retag.json").write_text(json.dumps(receipt, indent=2) + "\n")
print(json.dumps(receipt, indent=2))
