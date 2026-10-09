"""Certificate producer. The separate checker does not import this module."""
from __future__ import annotations
from typing import Any
from .core import BulkIndex, SparseOverlay, digest, histogram_records


def extended_gcd(a: int, b: int) -> tuple[int, int, int]:
    x0, x1, y0, y1 = 1, 0, 0, 1
    while b:
        q, rem = divmod(a, b)
        a, b = b, rem
        x0, x1 = x1, x0 - q * x1
        y0, y1 = y1, y0 - q * y1
    return a, x0, y0


def make_certificate(index: BulkIndex, overlay: SparseOverlay | None = None) -> dict[str, Any]:
    if overlay is None:
        overlay = SparseOverlay(index)
    if overlay.index is not index:
        raise ValueError("overlay belongs to a different index")
    final_hist = overlay.histogram  # also checks freshness
    m = index.snapshot()
    monos = {root: [] for root in index.components}
    for e in m.edges:
        sign = index.signs[e.v] * e.sign * index.signs[e.u]
        shift = index.signs[e.v] * (
            e.sign * index.shifts[e.u] + e.shift - index.shifts[e.v]) % m.sheets
        monos[index.roots[e.u]].append((sign, shift))
    components = []
    for root, maps in sorted(monos.items()):
        reflection = next((a for s, a in maps if s == -1), None)
        old = m.sheets
        witnesses = []
        for sign, shift in maps:
            inc = (shift if sign == 1 else shift - reflection) % m.sheets
            new, x, y = extended_gcd(old, inc)
            witnesses.append([new, x, y])
            old = new
        comp = index.components[root]
        if old != comp.d:
            raise ArithmeticError("static certificate and dynamic divisor differ")
        components.append({
            "root": root, "divisor": old,
            "reflection": None if reflection is None else reflection % old,
            "gcd_witnesses": witnesses,
            "histogram": histogram_records(comp.hist),
        })
    source = {"model": m.as_dict(), "defects": [vars(x) for x in overlay.defects]}
    return {
        "schema": "affine-orbit-profile-v1",
        "source_sha256": digest(source),
        "roots": index.roots.copy(), "signs": index.signs.copy(),
        "shifts": index.shifts.copy(), "parent_edges": index.parents.copy(),
        "components": components,
        "histogram": histogram_records(final_hist),
        "component_count": overlay.component_count,
    }
