"""Independent finite checks for the adaptive crossing-block separator."""
from __future__ import annotations

import itertools
import json
import argparse
import random
from pathlib import Path

from adaptive_modes import (Ring, crossing_kernel, padded_restricted_modes,
                            reconstruct, separate, tuple_count)


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def determinant(matrix, ring):
    n = len(matrix)
    if n == 0:
        return ring.one
    value = ring.zero
    for permutation in itertools.permutations(range(n)):
        term = ring.one
        for j in range(n):
            term = ring.mul(term,matrix[j][permutation[j]])
        inversions = sum(permutation[i] > permutation[j] for i in range(n) for j in range(i+1,n))
        value = ring.sub(value,term) if inversions & 1 else ring.add(value,term)
    return value


def verify_determinantal_ideals(matrix, modes, ring):
    m,n = len(matrix),len(matrix[0]) if matrix else 0
    weights = [mode.weight for mode in modes]
    checked = 0
    for k in range(1,min(m,n)+1):
        minimum = ring.precision
        for rows in itertools.combinations(range(m),k):
            for cols in itertools.combinations(range(n),k):
                minor = [[matrix[i][j] for j in cols] for i in rows]
                minimum = min(minimum,ring.valuation(determinant(minor,ring)))
                checked += 1
        expected = min(ring.precision,sum(weights[:k])) if len(weights) >= k else ring.precision
        require(minimum == expected,"determinantal-ideal mismatch")
    return checked


def test_random_matrices():
    rng = random.Random(20261026)
    matrices = minors = 0
    for f in [(0,1),(1,1,1),(1,1,0,1)]:
        for p in [1,2,5,9]:
            ring = Ring(p,f)
            for m,n in [(1,1),(2,3),(3,2),(3,3)]:
                for repetition in range(15):
                    common = rng.randrange(p+1)
                    matrix = [[ring.element(tuple((1 << common)*rng.randrange(1 << p)
                                for _ in range(ring.degree))) for _ in range(n)] for _ in range(m)]
                    if repetition % 5 == 0 and m > 1:
                        matrix[-1] = matrix[0][:]
                    modes = separate(matrix,ring)
                    require(reconstruct(modes,m,n,ring) == matrix,"random reconstruction failed")
                    minors += verify_determinantal_ideals(matrix,modes,ring)
                    matrices += 1
    return {"matrices":matrices,"independent_minors":minors}


def test_crossing_blocks():
    rng = random.Random(619)
    checks = 0
    full_profiles = 0
    for f,zeta in [((0,1),(1,)),((1,1,1),(0,1)),((1,1,0,1),(0,1,0))]:
        for a in range(1,5):
            L = 1 << a
            for i in range(a):
                for orientation in [0,1]:
                    R = 1 << i
                    slots = [orientation*R+(j % R)+2*R*(j//R) for j in range(L//2)]
                    for p in [4,9,17]:
                        ring = Ring(p,f)
                        for rows,columns,label in [
                            (slots,slots,"full"),
                            (slots[::2],slots[::2],"dyadic_sparse"),
                            (sorted(rng.sample(slots,max(1,len(slots)//2))),
                             sorted(rng.sample(slots,max(1,len(slots)//2))),"independent_sparse"),
                            ([slots[0],slots[0]],[slots[-1],slots[-1]],"duplicate_control")]:
                            matrix = crossing_kernel(a,1 << i,zeta,rows,columns,ring)
                            modes = separate(matrix,ring)
                            baseline = padded_restricted_modes(a,1 << i,zeta,rows,columns,ring)
                            require(reconstruct(modes,len(rows),len(columns),ring) == matrix,
                                    "crossing reconstruction failed")
                            require(reconstruct(baseline,len(rows),len(columns),ring) == matrix,
                                    "restricted padded reconstruction failed")
                            new_w = sorted(mode.weight for mode in modes)
                            old_w = sorted(mode.weight for mode in baseline)
                            require(len(new_w) <= len(old_w),"adaptive rank increased")
                            require(all(a >= b for a,b in zip(new_w,old_w)),"weight domination failed")
                            require(tuple_count(new_w,p) <= tuple_count(old_w,p),"inventory domination failed")
                            if label == "full":
                                expected = []
                                for q in range(L//(2*R)):
                                    w = a+1-i+4*q-2*q.bit_count()
                                    expected.extend([w]*R)
                                expected = [w for w in expected if w < p]
                                require(new_w == expected,"full-block Smith profile mismatch")
                                full_profiles += 1
                            checks += 1
    return {"matrices":checks,"full_profile_checks":full_profiles}


def comparison_cases():
    records = []
    for a,i,p,stride in [(5,0,24,2),(5,0,40,2),(6,0,48,2),
                          (6,0,64,4),(6,2,40,2),(6,2,48,4)]:
        L,R = 1 << a,1 << i
        slots = [(j % R)+2*R*(j//R) for j in range(L//2)]
        real = slots[::stride]
        ring,zeta = Ring(p,(1,1,1)),(0,1)
        matrix = crossing_kernel(a,1 << i,zeta,real,real,ring)
        baseline = padded_restricted_modes(a,1 << i,zeta,real,real,ring)
        adaptive = separate(matrix,ring)
        new_w,old_w = sorted(x.weight for x in adaptive), sorted(x.weight for x in baseline)
        old_count,new_count = tuple_count(old_w,p),tuple_count(new_w,p)
        require(new_count <= old_count,"comparison failed")
        records.append({"a":a,"i":i,"precision":p,"stride_in_orientation_order":stride,
                        "rows":len(real),"columns":len(real),"ring":"(Z/2^p)[U]/(U^2+U+1)",
                        "zeta":[0,1],"baseline_weights":old_w,"adaptive_weights":new_w,
                        "baseline_inventory":old_count,"adaptive_inventory":new_count,
                        "inventory_ratio":old_count/new_count})
    return records


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path,
        default=Path(__file__).resolve().parents[1]/"results/local_checks/adaptive_mode_results.json")
    args=parser.parse_args()
    result = {"random":test_random_matrices(),"crossing":test_crossing_blocks(),
              "comparisons":comparison_cases(),
              "scope":"Exact finite kernel identities and abstract inventories; no SAT runtime or asymptotic theorem validated."}
    destination = args.output
    destination.parent.mkdir(parents=True,exist_ok=True)
    destination.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps(result,indent=2))


if __name__ == "__main__":
    main()
