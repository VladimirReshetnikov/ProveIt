"""Shared deterministic test/benchmark fixtures; no external dependencies."""
from pathlib import Path
import json
import sys
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from fastunknot import Diagram


def load(name):
    return Diagram.from_json(json.loads((ROOT / 'examples' / name).read_text()))


def connected_sum(a, b):
    """Splice one edge of each spherical PD diagram, trying the two endpoint pairings."""
    if not a.crossings:
        return b
    if not b.crossings:
        return a
    offset = 2 * a.crossings
    pd = [list(row) for row in a.pd] + [[x + offset for x in row] for row in b.pd]
    ai = [(i, j) for i, row in enumerate(pd[:a.crossings]) for j, x in enumerate(row) if x == 0]
    bi = [(i, j) for i, row in enumerate(pd) for j, x in enumerate(row) if x == offset]
    for t in (0, 1):
        rows = [row[:] for row in pd]
        i, j = ai[0]
        rows[i][j] = offset
        i, j = bi[t]
        rows[i][j] = 0
        try:
            return Diagram.from_pd(rows)
        except ValueError:
            pass
    raise ArithmeticError('no spherical edge splice')


def power_sum(d, k):
    out = Diagram.from_pd([])
    for _ in range(k):
        out = connected_sum(out, d)
    return out
