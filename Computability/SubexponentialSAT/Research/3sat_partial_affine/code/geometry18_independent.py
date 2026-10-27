"""Independent affine-equation reconstruction of the eighteen-point plans."""


from fractions import Fraction

from itertools import combinations, product

from pathlib import Path

import hashlib

import json

def require(condition, message):
    if not condition:
        raise ValueError(message)

R = 18

VERTICES = tuple(range(R))

EDGES = tuple(combinations(VERTICES, 2))

NORMALS = ((1,0), (0,1), (1,1), (1,2))

def affine_plan(normal):
    a, b = normal
    lines = []
    for c in range(3):
        originals = tuple(3*x+y for x in range(3) for y in range(3)
                          if (a*x+b*y) % 3 == c)
        lines.append(originals + tuple(v+9 for v in originals))
    return tuple(lines)

def operations(plan):
    out = []
    universe = set(VERTICES)
    def visit(block):
        if len(block) == 1:
            return
        middle = len(block)//2
        left, right = block[:middle], block[middle:]
        visit(left)
        visit(right)
        outside = tuple(sorted(universe-set(block)))
        kind = {2:"P",3:"T",6:"B"}[len(block)]
        out.append((kind,(left,right,outside)))
    for block in plan:
        visit(block)
    out.append(("F",plan))
    return out
