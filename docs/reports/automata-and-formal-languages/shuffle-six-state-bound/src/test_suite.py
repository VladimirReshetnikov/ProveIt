#!/usr/bin/env python3
"""Independent small-grid BFS checks, constructive replay tests, and negative tests."""
from __future__ import annotations
from collections import deque
from copy import deepcopy
from itertools import product
import json
from pathlib import Path
import random
import time
from check_certificates import check_record, require
from construct import Constructor

ROOT = Path(__file__).resolve().parents[1]


def valid_mask(x: int, m: int, n: int, r: int = 0, c: int = 0) -> bool:
    return any(x & (1 << (r*n+j)) for j in range(n)) and any(
        x & (1 << (i*n+c)) for i in range(m))


def cells(x: int, m: int, n: int) -> list[tuple[int, int]]:
    return [(i, j) for i in range(m) for j in range(n) if x & (1 << (i*n+j))]


def independent_bfs(m: int, n: int) -> dict:
    # Bitset implementation deliberately does not use construct.transition.
    images = []
    for f in product(range(m), repeat=m):
        for g in product(range(n), repeat=n):
            images.append(tuple((1 << (f[i]*n+j)) | (1 << (i*n+g[j]))
                                for i in range(m) for j in range(n)))
    distances = {1: 0}
    queue = deque([1])
    while queue:
        x = queue.popleft()
        support = [k for k in range(m*n) if x & (1 << k)]
        for image in images:
            y = 0
            for k in support:
                y |= image[k]
            if y not in distances:
                distances[y] = distances[x] + 1
                queue.append(y)
    expected = {x for x in range(1 << (m*n)) if valid_mask(x, m, n)}
    require(set(distances) == expected, f"BFS validity mismatch {m}x{n}")
    return {"shape": [m,n], "reachable_states": len(distances),
            "maximum_shortest_word_length": max(distances.values())}


def labeled_antichains(m: int) -> tuple[int, int]:
    # Straight list recursion, not the bitmask C++ enumerator.
    def walk(chosen: list[frozenset[int]], candidates: list[frozenset[int]]):
        yield chosen
        for k, a in enumerate(candidates):
            later = [b for b in candidates[k+1:] if not a <= b and not b <= a]
            yield from walk(chosen + [a], later)
    subsets = [frozenset(i for i in range(m) if s & (1 << i)) for s in range(1, (1<<m)-1)]
    count, hard_count = 0, 0
    for family in walk([], subsets):
        count += 1
        if any(len(a) < 2 for a in family):
            continue
        rows = [frozenset(j for j, a in enumerate(family) if i in a) for i in range(m)]
        if any(len(a) < 2 for a in rows):
            continue
        if any(i != k and a <= b for i, a in enumerate(rows) for k, b in enumerate(rows)):
            continue
        hard_count += 1
    return count, hard_count


def main():
    start = time.perf_counter()
    ctor = Constructor.load(ROOT / "data/certificates.jsonl")
    bfs = [independent_bfs(m, n) for m, n in [(2,2), (2,3), (3,3)]]
    exhaustive = []
    for m, n in [(1,4), (4,1), (2,2), (2,3), (3,3), (3,4)]:
        count = 0
        longest = 0
        for x in range(1 << (m*n)):
            if valid_mask(x, m, n):
                word = ctor.reach(m, n, cells(x,m,n))
                count += 1
                longest = max(longest, len(word))
        exhaustive.append({"shape": [m,n], "targets": count, "longest_constructed_word": longest})
    all_roots = 0
    for r in range(3):
        for c in range(3):
            for x in range(1 << 9):
                if valid_mask(x, 3, 3, r, c):
                    ctor.reach(3, 3, cells(x,3,3), (r,c))
                    all_roots += 1
    antichains = []
    coverage = json.loads((ROOT / "audit/coverage.json").read_text())["coverage"]
    for m in range(2,6):
        total, hard = labeled_antichains(m)
        expected = next(rec for rec in coverage if rec["m"] == m)
        require(total == expected["labeled_antichains_visited"] and hard == expected["hard_labeled_families"],
                f"independent antichain mismatch m={m}")
        antichains.append({"m":m, "total":total, "hard":hard})
    records = list(ctor.certificates.values())
    rec7 = min((r for r in records if r["m"] == 6 and r["n"] == 7),
               key=lambda r: (sum(s.bit_count() for s in r["columns"]), r["family"]))
    rec20 = next(r for r in records if r["m"] == 6 and r["n"] == 20)
    examples = []
    for name, rec, copies in [("six_by_seven", rec7, 1), ("six_by_twenty", rec20, 1),
                              ("six_by_one_hundred", rec20, 5)]:
        m, n = rec["m"], rec["n"] * copies
        cols = rec["columns"] * copies
        target = [(i,j) for i in range(m) for j,s in enumerate(cols) if s & (1<<i)]
        data = {"m":m, "n":n, "target":target, "root":[0,0]}
        word = ctor.reach(m,n,target)
        (ROOT / "examples" / (name + "_input.json")).write_text(json.dumps(data,indent=2)+"\n")
        data.update(word=[{"f":f,"g":g} for f,g in word], word_length=len(word),
                    length_bound=len(target)+min(m,n)-2, replay="PASS")
        (ROOT / "examples" / (name + "_word.json")).write_text(json.dumps(data,indent=2)+"\n")
        examples.append({"name":name, "shape":[m,n], "target_size":len(target),
                         "word_length":len(word), "bound":len(target)+min(m,n)-2})
    (ROOT / "examples/six_by_seven_certificate.json").write_text(json.dumps(rec7,indent=2)+"\n")
    (ROOT / "examples/six_by_twenty_certificate.json").write_text(json.dumps(rec20,indent=2)+"\n")
    target7 = [(i,j) for i in range(6) for j,s in enumerate(rec7["columns"]) if s & (1<<i)]
    for r in range(6):
        for c in range(7):
            ctor.reach(6,7,target7,(r,c))
    rng = random.Random(20260920)
    random_tests = 0
    for m, n in [(4,7),(5,11),(6,7),(6,20),(6,50),(50,6)]:
        for _ in range(30):
            while True:
                target = [(i,j) for i in range(m) for j in range(n) if rng.random() < 0.45]
                if any(i==0 for i,j in target) and any(j==0 for i,j in target):
                    break
            ctor.reach(m,n,target)
            random_tests += 1
    bad = []
    x = deepcopy(rec7); x["f"] = x["f"][:-1]; bad.append(x)
    x = deepcopy(rec7); x["g"][0] = rec7["n"]; bad.append(x)
    x = deepcopy(rec7); x["T"] = []; bad.append(x)
    x = deepcopy(rec7); x["T"].append(x["T"][0]); bad.append(x)
    x = deepcopy(rec7); x["family"] ^= 1; bad.append(x)
    x = deepcopy(rec7); x["status"] = "unknown"; bad.append(x)
    x = deepcopy(rec7); x["columns"] = list(reversed(x["columns"])); bad.append(x)
    for x in bad:
        try:
            check_record(x)
        except ValueError:
            pass
        else:
            raise ValueError("corrupted certificate was accepted")
    out = {"result":"PASS", "independent_bfs":bfs, "exhaustive_replay":exhaustive,
           "all_root_3x3_replays":all_roots, "independent_python_antichains":antichains,
           "all_root_6x7_replays":42, "random_replay_tests":random_tests,
           "negative_certificate_tests":len(bad), "examples":examples,
           "elapsed_seconds":round(time.perf_counter()-start,3)}
    text = json.dumps(out,indent=2)+"\n"
    (ROOT / "audit/tests.json").write_text(text)
    print(text, end="")

if __name__ == "__main__":
    main()
