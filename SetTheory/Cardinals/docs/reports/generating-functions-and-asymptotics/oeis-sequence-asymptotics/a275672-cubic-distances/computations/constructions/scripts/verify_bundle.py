#!/usr/bin/env python3
"""Independently verify every packaged witness with integer arithmetic."""
import itertools
import json
from pathlib import Path


def verify(w):
    n,k,points=w["n"],w["k"],w["points"]
    if not (type(n) is int and n>0 and type(k) is int and k==len(points)):
        raise ValueError("Invalid size")
    if any(len(p)!=3 or any(type(c) is not int or not 0<=c<n for c in p) for p in points):
        raise ValueError("Coordinate outside the integer cube")
    if len({tuple(p) for p in points})!=k:
        raise ValueError("Duplicate point")
    distances={}
    for i,j in itertools.combinations(range(k),2):
        d=sum((points[i][a]-points[j][a])**2 for a in range(3))
        if d<=0 or d in distances:
            raise ValueError(f"Repeated squared distance {d}: {distances.get(d)} and {(i,j)}")
        distances[d]=(i,j)
    if len(distances)!=k*(k-1)//2:
        raise ValueError("Incorrect number of pairs")
    if "squared_distances" in w and w["squared_distances"]!=sorted(distances):
        raise ValueError("Stored distance inventory differs from recomputation")
    if "distance_to_point_indices" in w and w["distance_to_point_indices"]!={
            str(d):list(pair) for d,pair in distances.items()}:
        raise ValueError("Stored distance-to-pair mapping differs from recomputation")
    if "unordered_pair_count" in w and w["unordered_pair_count"]!=len(distances):
        raise ValueError("Stored unordered-pair count differs from recomputation")
    return len(distances)


if __name__=="__main__":
    root=Path(__file__).resolve().parent.parent
    for name in ["witnesses.json","main_witnesses.json"]:
        records=json.loads((root/"data"/name).read_text())["certificates"]
        for w in records:
            count=verify(w)
            print(f"{name}: n={w['n']}, k={w['k']}, {count} distinct positive squared distances: PASS")
