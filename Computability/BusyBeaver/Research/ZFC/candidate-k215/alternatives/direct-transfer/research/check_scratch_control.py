#!/usr/bin/env python3
"""Independent literal-source control audit for archived scratch-biased 215.

Usage: python check_scratch_control.py [CORRECT_SOURCE SCRATCH_BIASED_SOURCE]
With no arguments uses ../source/st215.sites.json and
../inputs/scratch-biased.sites.json, relative to this script.
No supplied checker is imported. The two resolvers use independent
interval and binary-cut constructions.
"""
import hashlib
import json
import sys
from pathlib import Path


def intervals(sites):
    size = len(sites)
    first, last = {}, {}
    for i, (p, _, _) in enumerate(sites):
        for j in range(len(p) + 1):
            first.setdefault(p[:j], i)
            last[p[:j]] = i + 1
    out = []
    for i, (p, op, arg) in enumerate(sites):
        choices = [j for j, b in enumerate(p) if b == ("0" if op in ("CD", "CB") else "1")]
        depth = 1 if op == "CD" else arg if op in ("CB", "CC") else 1
        if len(choices) < depth: target = 0
        else:
            prefix = p[:choices[-depth]]
            target = last[prefix] % size if op in ("CD", "CB") else first[prefix]
        if op == "CH": edges = []
        elif op in ("CB", "CC"): edges = [target]
        elif op == "CD": edges = [target, (i + 1) % size]
        else: edges = [(i + 1) % size]
        out.append((op, arg, edges))
    return out


def binary_cuts(sites):
    leaves = {p: i for i, (p, _, _) in enumerate(sites)}
    depth = max(map(len, leaves))
    def locate(prefix):
        word = prefix + "0" * depth
        for length in range(1, depth + 1):
            if word[:length] in leaves:
                assert "1" not in prefix[length:]
                return leaves[word[:length]]
        raise AssertionError(prefix)
    def inc(p):
        if not p: return ""
        return format((int(p, 2) + 1) % (1 << len(p)), "0" + str(len(p)) + "b")
    def cut(p, bit, n):
        positions = [i for i, v in enumerate(p) if v == bit]
        return p[:positions[-n]] if len(positions) >= n else ""
    out = []
    for p, op, arg in sites:
        if op == "CH": edges = []
        elif op == "CI": edges = [locate(inc(p))]
        elif op == "CD": edges = [locate(inc(cut(p, "0", 1))), locate(inc(p))]
        elif op == "CB": edges = [locate(inc(cut(p, "0", arg)))]
        elif op == "CC": edges = [locate(cut(p, "1", arg))]
        else: raise AssertionError(op)
        out.append((op, arg, edges))
    return out


def run(graph, top, data):
    regs = list(data)
    regs[1] = top
    assert regs[3] == regs[5] == regs[6] == 0
    pc, trace = 4696, []
    for steps in range(2 * top + 30):
        trace.append({"ordinal": pc, "registers": regs.copy()})
        op, arg, edges = graph[pc]
        if op == "CH": return steps, pc, regs, trace
        if op == "CI": regs[arg] += 1; pc = edges[0]
        elif op == "CD":
            b = regs[arg] > 0
            regs[arg] -= int(b)
            pc = edges[int(b)]
        else: pc = edges[0]
    raise AssertionError("Did not halt")


def main():
    packet = Path(__file__).resolve().parent.parent
    if len(sys.argv) == 1:
        files = {"baseline": packet / "source/st215.sites.json",
                 "scratch-biased": packet / "inputs/scratch-biased.sites.json"}
    elif len(sys.argv) == 3:
        files = {"baseline": Path(sys.argv[1]), "scratch-biased": Path(sys.argv[2])}
    else:
        raise SystemExit(__doc__)
    sources = {name: json.loads(path.read_text()) for name, path in files.items()}
    graphs = {name: intervals(src) for name, src in sources.items()}
    for name, src in sources.items(): assert graphs[name] == binary_cuts(src)
    assert sources["baseline"][4696][1:] == ["CC", 3]
    assert graphs["baseline"][4696][2] == [0]
    assert sources["scratch-biased"][4696:4698] == [["100110", "CI", 6], ["100111", "CC", 3]]
    graph = graphs["scratch-biased"]
    assert graph[4697][2] == [23]
    counts = []
    for top in range(32):
        for others in ([1, 0, 0, 0, 0, 0, 0, 0, 0], [17, 0, 91, 0, 23, 0, 0, 45, 61]):
            steps, pc, regs, trace = run(graph, top, others)
            assert (steps, pc) == (2 * top + 15, 4718)
            counts.append({"top": top, "steps": steps, "halt_ordinal": pc})
    _, _, _, witness = run(graph, 0, [1, 0, 0, 0, 0, 0, 0, 0, 0])
    result = {
        "status": "MISDIRECTED_CONTINUATION_AND_UNCONDITIONAL_HALTING_SUFFIX_CONFIRMED",
        "source_hashes": {name: hashlib.sha256(path.read_bytes()).hexdigest() for name, path in files.items()},
        "whole_graph_agreement": {name: len(graph) for name, graph in graphs.items()},
        "baseline_edge": {"ordinal": 4696, "path": sources["baseline"][4696][0], "CC": 3, "target": 0},
        "new_edge": {"ordinal": 4697, "path": "100111", "CC": 3, "target": 23},
        "all_natural_suffix_premise": "At ordinal4696, A=H=X=0, T=t; all other registers arbitrary.",
        "written_induction_result": "CH at ordinal4718 after exactly2t+15 source transitions.",
        "bounded_correspondence_checks": counts,
        "zero_top_exact_trace": witness,
        "scope": "Independent complete source-CFG audit and exact finite suffix witnesses. The all-natural count follows from the written unary-loop proof; full binary runtime is inherited, not rerun here.",
        "checker_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }
    path = Path(__file__).with_name("scratch_control_result.json")
    path.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"status": result["status"], "graph_cases": result["whole_graph_agreement"], "suffix_checks": len(counts), "output": str(path)}, indent=2))


if __name__ == "__main__": main()
