"""Certify the length, centered inball and centered outer radius of the test path."""
from itertools import combinations
from math import isqrt
from pathlib import Path
import re

def dot(a,b):
    return sum(x*y for x,y in zip(a,b))

def subtract(a,b):
    return tuple(x-y for x,y in zip(a,b))

def cross(a,b):
    return (a[1]*b[2]-a[2]*b[1], a[2]*b[0]-a[0]*b[2],
            a[0]*b[1]-a[1]*b[0])

def verify():
    text = Path(__file__).with_name("witness.hpp").read_text()
    points = [tuple(map(int,m)) for m in re.findall(r"\{(-?\d+), (-?\d+), (-?\d+)\}",text)]
    assert len(points)==61
    length = sum(1+isqrt(dot(v,v)) for p,q in zip(points,points[1:]) for v in [subtract(q,p)])
    assert length <= 10**7
    assert max(dot(p,p) for p in points) <= 2450000**2
    a,b,c,d=points[:4]
    assert dot(cross(subtract(b,a),subtract(c,a)),subtract(d,a)) != 0
    count=0
    for a,b,c in combinations(points,3):
        n=cross(subtract(b,a),subtract(c,a))
        if n==(0,0,0):
            continue
        level=dot(n,a)
        vals=[dot(n,p) for p in points]
        if min(vals)<level<max(vals):
            continue
        if min(vals)==level:
            level=-level
        assert level>0 and level**2 >= 1020000**2*dot(n,n)
        count+=1
    assert count>=4
    print(f"{len(points)} spatial vertices. Length < {length}/10000000.")
    print(f"{count} supporting triples. Centered inradius >= 0.102 and outer radius <= 0.245.")

if __name__=="__main__":
    verify()
