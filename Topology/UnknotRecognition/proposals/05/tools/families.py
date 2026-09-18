"""Deterministic benchmark inputs; all constructors validate their PD output."""
from __future__ import annotations
import sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from fastunknot import Diagram


def connected_sum(a: Diagram,b: Diagram) -> Diagram:
    """Splice edge 0 of two sphere diagrams, preserving over/under information."""
    if not a.crossings: return b
    if not b.crossings: return a
    shift=2*a.crossings
    rows=[list(row) for row in a.pd]+[[x+shift for x in row] for row in b.pd]
    left=[(i,j) for i,row in enumerate(rows) for j,e in enumerate(row) if e==0]
    right=[(i,j) for i,row in enumerate(rows) for j,e in enumerate(row) if e==shift]
    i,j=left[1]; rows[i][j]=shift
    i,j=right[0]; rows[i][j]=0
    return Diagram.from_pd(rows)


def connected_power(d: Diagram, k: int) -> Diagram:
    if type(k) is not int or k<0: raise ValueError('k must be nonnegative')
    result=Diagram.from_pd([])
    for _ in range(k): result=connected_sum(result,d)
    return result
