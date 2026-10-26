#!/usr/bin/env python3
"""Static cross-check of candidate signatures and exponent-label arithmetic.

This is not a Lean elaboration or a substitute for kernel checking.
"""
from pathlib import Path
import argparse
import hashlib
import json
import re


def require(condition, message):
    if not condition:
        raise ValueError(message)


def public_signatures(text):
    return dict(re.findall(r"^theorem (natural_(?:step|power)_\d+)\b(.*?):=", text,
                           re.M | re.S))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("repo", type=Path)
    parser.add_argument("candidate", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    prefix = Path("Computability/DiophantineConsistency/Lean/DiophantineConsistency")
    result = {"validation": "static only; not Lean compilation", "families": []}
    for module, circuit, expected_length, base in (
        ("GapCircuitSteps66", "GapCircuit66", 484, 20),
        ("SplitCircuitSteps59", "SplitCircuit59", 515, 36),
    ):
        before = (args.repo / prefix / (module + ".lean")).read_text()
        after = (args.candidate / prefix / (module + ".lean")).read_text()
        orig_signatures = public_signatures(before)
        next_signatures = public_signatures(after)
        require(orig_signatures == next_signatures, module + ": public signature changed")
        circuit_text = (args.repo / prefix / (circuit + ".lean")).read_text()
        natural_body = circuit_text.split("def naturalNodes", 1)[1].split("def naturalOutput", 1)[0]
        nodes = re.findall(r"\.(literal|input|constant|add|sub|mul)\b([^\n]*)", natural_body)
        require(len(nodes) == expected_length, circuit + ": unexpected node count")
        label_match = re.search(r"private def naturalPowerLabels : List ℕ :=\s*\[([^]]*)\]", after)
        require(label_match is not None, module + ": missing labels")
        labels = list(map(int, re.findall(r"\d+", label_match[1])))
        require(len(labels) == expected_length, module + ": unexpected label count")
        require(labels[base] == 1, module + ": bad base label")
        steps = 0
        for i, (kind, body) in enumerate(nodes):
            if kind in ("add", "sub", "mul"):
                operands = list(map(int, re.findall(r"\d+", body)))
                require(len(operands) == 2 and max(operands) < i, circuit + ": bad topology")
            if i == base or not labels[i]:
                continue
            require(kind == "mul", module + ": nonmultiplicative power step")
            a, b = operands
            require(labels[a] > 0 and labels[b] > 0 and labels[i] == labels[a] + labels[b],
                    module + f": failed exponent addition at {i}")
            steps += 1
        result["families"].append({
            "module": module,
            "public_signatures_equal": True,
            "public_signature_count": len(orig_signatures),
            "literal_node_count": len(nodes),
            "power_steps_checked_against_literal_nodes": steps,
            "literal_topology_checked": True,
            "candidate_sha256": hashlib.sha256(after.encode()).hexdigest(),
        })
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
