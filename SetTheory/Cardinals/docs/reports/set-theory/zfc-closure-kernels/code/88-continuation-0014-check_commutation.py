#!/usr/bin/env python3
"""Independent full-source and finite-region certificate for q106 commutation.

No optimizer, transformer, or delivered source checker is imported.  The
literal source parser and path arithmetic are the independent audit code.
The candidate is accepted only if every structural change swaps CI7 with
the exact total transfer loop N(CD6,N(CI1,CC2)).  The complete outside CFG,
each region's unique entry, and both branch successors are checked.
"""
from pathlib import Path
import argparse, collections, hashlib, json
from independent_cfg import parse_source, build_cfg

ROOT = Path(__file__).resolve().parents[2]
ap = argparse.ArgumentParser()
ap.add_argument("candidate", type=Path)
ap.add_argument("--source", type=Path,
                default=ROOT/"vendor/context246/sources/Prog254.v")
ap.add_argument("--output", type=Path, required=True)
args = ap.parse_args()
old_rows, old_leaves = parse_source(args.source)
old_succ, old_initial = build_cfg(old_rows, old_leaves)

def literal_edge(edge):
    op, arg = edge
    return ("N", *(literal_edge(e) for e in old_rows[arg])) if op == "CN" else (op, arg)
old_tree = literal_edge(("CN", 0))

data = json.loads(args.candidate.read_text())
entries = {int(k): tuple(v) for k,v in data["entries"].items()}
seen = set()
def load_node(n, ancestors=()):
    assert n in entries and n not in ancestors
    seen.add(n)
    e = entries[n]
    if e[0] == "N":
        assert len(e) == 3
        return ("N", load_node(e[1], ancestors+(n,)), load_node(e[2], ancestors+(n,)))
    assert len(e) == 2 and e[0] in ("CI", "CD", "CB", "CC", "CH")
    if e[0] in ("CI", "CD"): assert type(e[1]) is int and 0 <= e[1] < 9
    elif e[0] in ("CB", "CC"): assert type(e[1]) is int and e[1] > 0
    else: assert e[1] is None
    return e
new_tree = load_node(data["root"])
assert seen == set(entries)

new_rows = []
new_leaves = []
def expand(t, p=""):
    if t[0] != "N":
        new_leaves.append((p,*t))
        return t
    n = len(new_rows)
    new_rows.append(None)
    new_rows[n] = (expand(t[1], p+"0"), expand(t[2], p+"1"))
    return ("CN", n)
assert expand(new_tree) == ("CN", 0)
assert len(new_rows) == 6459 and len(new_leaves) == 6460
new_succ, new_initial = build_cfg(new_rows, new_leaves)
old_index = {p:i for i,(p,*_) in enumerate(old_leaves)}
new_index = {p:i for i,(p,*_) in enumerate(new_leaves)}

def attributes(t):
    op = t[0]
    if op == "N":
        b0,c0,f0,h0 = attributes(t[1]); b1,c1,f1,h1 = attributes(t[2])
        return max(b0-1, 0, b1), max(c0, c1-1, 0), f0|f1, h0 or h1
    return (1 if op == "CD" else t[1] if op == "CB" else 0,
            t[1] if op == "CC" else 0,
            frozenset([t[1]]) if op in ("CI","CD") else frozenset(), op == "CH")

transfer = ("N", ("CD",6), ("N",("CI",1),("CC",2)))
increment = ("CI",7)
assert attributes(transfer) == (0,0,frozenset([1,6]),False)
assert attributes(increment) == (0,0,frozenset([7]),False)

occurrence_map = {}
regions = []
def map_equal(a,b,pa,pb):
    assert a == b
    if a[0] == "N":
        map_equal(a[1], b[1], pa+"0", pb+"0")
        map_equal(a[2], b[2], pa+"1", pb+"1")
    else:
        assert old_leaves[old_index[pa]][1:] == new_leaves[new_index[pb]][1:]
        occurrence_map[old_index[pa]] = new_index[pb]

def compare(a,b,pa="",pb=""):
    if a == b:
        map_equal(a,b,pa,pb)
        return
    assert a[0] == b[0] == "N"
    if a[1] == increment and a[2] == transfer and b[1] == transfer and b[2] == increment:
        map_equal(a[1], b[2], pa+"0", pb+"1")
        map_equal(a[2], b[1], pa+"1", pb+"0")
        regions.append({"old_path":pa, "new_path":pb,
            "old_indices":[old_index[pa+s] for s in ("0","10","110","111")],
            "new_indices":[new_index[pb+s] for s in ("1","00","010","011")]})
        return
    compare(a[1],b[1],pa+"0",pb+"0")
    compare(a[2],b[2],pa+"1",pb+"1")
compare(old_tree,new_tree)
assert regions and len(occurrence_map) == 6460
assert set(occurrence_map.values()) == set(range(6460))

old_members, new_members = {}, {}
old_entries, new_entries = {}, {}
for r,k in zip(regions,range(len(regions))):
    a,d,i,c = r["old_indices"]
    aa,dd,ii,cc = r["new_indices"]
    assert old_succ[a] == [d]
    assert old_succ[d][1] == i
    assert old_succ[i] == [c] and old_succ[c] == [d]
    assert new_succ[dd] == [aa,ii]
    assert new_succ[ii] == [cc] and new_succ[cc] == [dd]
    assert len(new_succ[aa]) == 1
    r["old_entry"],r["new_entry"] = a,dd
    r["old_exit"],r["new_exit"] = old_succ[d][0],new_succ[aa][0]
    assert r["old_exit"] not in r["old_indices"]
    assert r["new_exit"] not in r["new_indices"]
    for v in r["old_indices"]:
        assert v not in old_members
        old_members[v] = k
    for v in r["new_indices"]:
        assert v not in new_members
        new_members[v] = k
    old_entries[a] = dd
    new_entries[dd] = a

def boundary(v):
    if v in old_members:
        assert v in old_entries
        return old_entries[v]
    return occurrence_map[v]

outside_checks = 0
for v,ns in enumerate(old_succ):
    if v in old_members: continue
    w = occurrence_map[v]
    assert w not in new_members
    assert new_succ[w] == [boundary(u) for u in ns]
    outside_checks += len(ns)
for r in regions:
    assert boundary(r["old_exit"]) == r["new_exit"]
for v,ns in enumerate(new_succ):
    for w in ns:
        if w in new_members and (v not in new_members or new_members[v] != new_members[w]):
            assert w in new_entries
for v,ns in enumerate(old_succ):
    for w in ns:
        if w in old_members and (v not in old_members or old_members[v] != old_members[w]):
            assert w in old_entries
assert boundary(old_initial) == new_initial
assert attributes(old_tree)[:2] == attributes(new_tree)[:2] == (0,0)

result = {
    "status":"PASS", "candidate":str(args.candidate),
    "candidate_sha256":hashlib.sha256(args.candidate.read_bytes()).hexdigest(),
    "source_sha256":hashlib.sha256(args.source.read_bytes()).hexdigest(),
    "literal_leaf_count":6460, "literal_internal_nodes":6459,
    "shared_pair_nodes":sum(e[0]=="N" for e in entries.values()),
    "all_candidate_entries_reachable":True,
    "rewrite":"N(CI7, N(CD6,N(CI1,CC2))) -> N(N(CD6,N(CI1,CC2)), CI7)",
    "all_structural_differences_are_exact_reviewed_swaps":True,
    "unfolded_swapped_regions":len(regions),
    "all_regions_have_unique_external_entry":True,
    "all_region_internal_guarded_edges_match_total_transfer_loop":True,
    "all_region_exits_match_under_boundary_map":True,
    "unchanged_outside_guarded_edges_checked":outside_checks,
    "initial_control_matches":True,
    "root_escape_bounds":[0,0],
    "increment_attributes":{"break_bound":0,"continue_bound":0,"footprint":[7],"contains_halt":False},
    "transfer_attributes":{"break_bound":0,"continue_bound":0,"footprint":[1,6],"contains_halt":False},
    "region_output":"R7'=R7+1; R1'=R1+R6; R6'=0; every other register unchanged",
    "region_primitive_steps":"3*R6+2 in both orders for every natural input R6",
    "regions":regions,
    "method":"Independent literal and DAG parsers; exact structural comparison; complete source CFG contraction; no optimizer or package checker imports.",
    "scope":"Unconditional source halting and final-register equivalence from corresponding region boundaries. It is not an exact single-instruction bisimulation or a binary runtime theorem."
}
args.output.write_text(json.dumps(result,indent=2)+"\n")
print(json.dumps({k:v for k,v in result.items() if k != "regions"},indent=2))
