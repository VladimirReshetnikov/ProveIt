#!/usr/bin/env python3
"""Independent literal-source, first-arrival, and exact-rational incidence audit.

The certificate producer and compiler are not imported.  This is a scoped
rigidity result for uniform CI retyping of the existing source-role groups.
"""
from pathlib import Path
from fractions import Fraction
from functools import cache
import argparse, hashlib, json
from independent_cfg import parse_source, build_cfg

ROOT = Path(__file__).resolve().parents[2]
ap = argparse.ArgumentParser()
ap.add_argument("certificate",type=Path,nargs="?",default=ROOT/"experiments/audit_inputs/increment_block_incidence.json")
ap.add_argument("--source", type=Path, default=ROOT/"vendor/context246/sources/Prog254.v")
ap.add_argument("--table", type=Path, default=ROOT/"vendor/context246/machine/zfc_prefix246_old.tm")
ap.add_argument("--output", type=Path, required=True)
args = ap.parse_args()
rows, leaves = parse_source(args.source)
succ, initial = build_cfg(rows, leaves)
pred = [[] for _ in leaves]
for i, ss in enumerate(succ):
    for j in ss: pred[j].append(i)

table = {}
for line in args.table.read_text().splitlines():
    if not line.strip() or line.startswith("#"): continue
    q,b,w,d,t = line.split()
    q,b,w,t = map(int,(q,b,w,t))
    assert b in (0,1) and w in (0,1) and d in ("L","R")
    assert (q,b) not in table
    table[q,b] = (w,1 if d=="R" else -1,t)
assert len(table) == 492

first_arrival_runs = []
@cache
def parent_state(prefix):
    origin = 256
    tape = bytearray(1024)
    tape[origin-1] = 1
    for i,b in enumerate(prefix): tape[origin+i] = int(b)
    h = origin
    q = 96
    low = high = 0
    for steps in range(10000):
        if h == origin+len(prefix):
            first_arrival_runs.append((steps,low,high))
            return q
        assert 0 <= h < len(tape)
        w,d,q = table[q,tape[h]]
        tape[h] = w
        h += d
        low = min(low,h-origin)
        high = max(high,h-origin)
    raise AssertionError(("no first arrival",prefix))

leaf_group = {}
labels = {}
blocks = []
for i,(p,op,arg) in enumerate(leaves):
    if op != "CI": continue
    group = parent_state(p[:-1]), int(p[-1])
    leaf_group[i] = group
    labels.setdefault(group,set()).add(arg)
    if i and leaves[i-1][1] == "CI": blocks[-1].append(i)
    else: blocks.append([i])
assert len(leaf_group) == 2601 and len(blocks) == 1875
for block in blocks:
    assert initial not in block[1:]
    for i,j in zip(block,block[1:]):
        assert succ[i] == [j] and pred[j] == [i]
    assert leaves[succ[block[-1]][0]][1] != "CI"

groups = sorted(labels)
assert len(groups) == 20 and all(len(v)==1 for v in labels.values())
M = [[sum(leaf_group[i]==g for i in block) for g in groups] for block in blocks]
cert = json.loads(args.certificate.read_text())
assert groups == list(map(tuple,cert["groups"]))
assert {str(g):sorted(v) for g,v in labels.items()} == cert["group_labels"]
assert blocks == cert["blocks"]
assert M == cert["incidence"]

# Maintain an independently reduced row basis using exact rational numbers.
# In addition to rank, record an explicit nonzero 19 by 19 minor.
basis = []
pivots = []
selected_rows = []
for index,row in enumerate(M):
    v = list(map(Fraction,row))
    for p,b in zip(pivots,basis):
        f = v[p]
        if f: v = [x-f*y for x,y in zip(v,b)]
    if not any(v): continue
    p = next(i for i,x in enumerate(v) if x)
    f = v[p]
    v = [x/f for x in v]
    basis.append(v)
    pivots.append(p)
    selected_rows.append(index)
assert len(basis) == cert["rank"] == 19

def determinant(A):
    A = [list(map(Fraction,r)) for r in A]
    n = len(A)
    det = Fraction(1)
    for k in range(n):
        p = next((i for i in range(k,n) if A[i][k]),None)
        if p is None: return Fraction(0)
        if p != k:
            A[k],A[p] = A[p],A[k]
            det = -det
        pivot = A[k][k]
        det *= pivot
        for i in range(k+1,n):
            f = A[i][k]/pivot
            for j in range(k+1,n): A[i][j] -= f*A[k][j]
            A[i][k] = 0
    return det

minor = [[M[i][j] for j in pivots] for i in selected_rows]
det = determinant(minor)
assert det
plus = groups.index((114,0))
minus = groups.index((114,1))
null = [int(j==plus)-int(j==minus) for j in range(20)]
assert all(sum(x*y for x,y in zip(row,null)) == 0 for row in M)
assert labels[(114,0)] == labels[(114,1)] == {1}
assert len(groups)-len(basis) == 1

result = {
    "status":"PASS",
    "source_sha256":hashlib.sha256(args.source.read_bytes()).hexdigest(),
    "table_sha256":hashlib.sha256(args.table.read_bytes()).hexdigest(),
    "certificate_sha256":hashlib.sha256(args.certificate.read_bytes()).hexdigest(),
    "increment_occurrences":len(leaf_group),
    "maximal_increment_blocks":len(blocks),
    "interior_increment_occurrences":sum(len(b)-1 for b in blocks),
    "every_block_interior_has_unique_immediate_CI_predecessor":True,
    "physical_source_role_groups":len(groups),
    "groups":[list(g) for g in groups],
    "original_group_labels":[next(iter(labels[g])) for g in groups],
    "independent_literal_first_arrival_runs":len(first_arrival_runs),
    "maximum_first_arrival_steps":max(t for t,lo,hi in first_arrival_runs),
    "first_arrival_head_range":[min(lo for t,lo,hi in first_arrival_runs),max(hi for t,lo,hi in first_arrival_runs)],
    "full_incidence_matrix_matches":True,
    "rank":len(basis), "nullity":1,
    "right_kernel_basis":[null],
    "nonzero_minor":{"rows":selected_rows,"columns":pivots,"matrix":minor,"determinant":str(det)},
    "rigidity":"Every assignment of one CI register label to each existing group that preserves every maximal CI block's total increment vector is the original assignment.",
    "reason":"Each coordinate difference belongs to the one-dimensional kernel. Only the two 114 groups can differ, and their original sum is 2*e1; nonnegative one-hot labels force both to remain e1.",
    "method":"Own literal parser, CFG, dense first-arrival TM interpreter, and exact Fraction elimination; no producer/compiler imports.",
    "scope":"Fixed source topology, fixed row grouping, one increment per occurrence, and equality of each complete CI block's register effect. No lower bound for arbitrary source or binary rewrites."
}
args.output.write_text(json.dumps(result,indent=2)+"\n")
print(json.dumps({k:v for k,v in result.items() if k not in ("groups","original_group_labels","nonzero_minor")},indent=2))
