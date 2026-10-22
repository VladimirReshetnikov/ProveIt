#!/usr/bin/env python3
"""Count existing certified decoder-prefix witness lengths, not compiler work."""
import argparse
import collections
import hashlib
import json
import pathlib
import re

if not __debug__:
    raise RuntimeError("Run without -O; this finite audit uses assertions.")

parser = argparse.ArgumentParser()
parser.add_argument("repo", nargs="?", type=pathlib.Path,
                    help="optional ProveIt checkout; defaults to the bundled pinned source")
parser.add_argument("--source", type=pathlib.Path,
                    help="explicit K215Decoder.lean source file")
parser.add_argument("--output", type=pathlib.Path)
args = parser.parse_args()
relative = pathlib.Path("Computability/BusyBeaver/Lean/BusyBeaver/ZFC/K215Decoder.lean")
path = args.source or (args.repo / relative if args.repo is not None else
                      pathlib.Path(__file__).resolve().parent.parent / "baseline/K215Decoder.lean")
source = path.read_text()


def body(name):
    return source.split("def " + name + " :", 1)[1].split("#[", 1)[1].split("\n]", 1)[0]


nodes = []
for line in body("sourceNodes").splitlines():
    line = line.strip().rstrip(",")
    if not line:
        continue
    m = re.fullmatch(r"\.(leaf|fork) (\d+) (\d+)", line)
    assert m, line
    nodes.append((m[1], int(m[2]), int(m[3])))

blocks = []
for line in body("blocks").splitlines():
    line = line.strip().rstrip(",")
    if not line:
        continue
    m = re.fullmatch(r"⟨(\d+), (\d+), \[([^\]]*)\], (\d+)⟩", line)
    assert m, line
    blocks.append((int(m[1]), int(m[2]), int(m[4])))

roles = []
for line in body("roles").splitlines():
    line = line.strip().rstrip(",")
    if not line:
        continue
    m = re.fullmatch(r"⟨(\d+), (\d+), \[([^\]]*)\], (.*)⟩", line)
    assert m, line
    zero, one = m[4].rsplit(", (.", 1)
    one = "(." + one
    edges = []
    for edge in (zero, one):
        internal = re.fullmatch(r"\(\.internal (\d+) (\d+)\)", edge)
        if internal:
            edges.append(("internal", int(internal[1]), int(internal[2])))
        else:
            primitive = re.fullmatch(r"\(\.primitive (\d+) ⟨.*⟩\)", edge)
            assert primitive, edge
            edges.append(("primitive", int(primitive[1]), 0))
    roles.append((int(m[1]), int(m[2]), edges))

leaves = []


def visit(index, word, clock, active):
    assert index not in active, "Cyclic role graph"
    node, state, edges = roles[index]
    tag, left, right = nodes[node]
    assert tag == "fork"
    for bit, edge in enumerate(edges):
        child = (left, right)[bit]
        if edge[0] == "internal":
            target, block = edge[1:]
            assert roles[target][0] == child
            entry, exit_state, steps = blocks[block]
            assert entry == state and exit_state == roles[target][1]
            visit(target, word + str(bit), clock + steps, active | {index})
        else:
            assert edge[1] == child
            tag, opcode, argument = nodes[child]
            assert tag == "leaf"
            leaves.append({"word": word + str(bit), "opcode": opcode,
                           "argument": argument, "entry_state": state,
                           "prefix_steps": clock, "branches": 2 if opcode == 1 else 1})


visit(0, "", 0, set())
histogram = collections.Counter(x["prefix_steps"] for x in leaves)
result = {
    "source": str(relative),
    "source_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
    "nodes": len(nodes), "roles": len(roles), "blocks": len(blocks),
    "leaves": len(leaves), "branches": sum(x["branches"] for x in leaves),
    "sum_prefix_steps_per_leaf": sum(x["prefix_steps"] for x in leaves),
    "sum_prefix_steps_per_branch": sum(x["prefix_steps"] * x["branches"] for x in leaves),
    "sum_prefix_bits_per_branch": sum((len(x["word"]) - 1) * x["branches"] for x in leaves),
    "min_prefix_steps": min(histogram), "max_prefix_steps": max(histogram),
    "prefix_steps_histogram": dict(sorted(histogram.items())),
    "first_leaf": leaves[0],
    "scope": "Finite census of existing exact block-certificate durations. These are physical "
             "decoder-prefix witness lengths, not Lean reduction counts, compile time, "
             "speedup, or new formal checks."
}
output = json.dumps(result, indent=2) + "\n"
if args.output:
    args.output.write_text(output)
print(output, end="")
