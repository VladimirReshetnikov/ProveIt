"""Guard for supplied equal-width blocks and non-wrapping interval pairings."""
from __future__ import annotations
from typing import Any
from .core import Edge, Model, integer


class UnsupportedModel(ValueError):
    """The supplied decomposition is outside the exact full-fibre contract."""


def split_edge(edge: Edge, sheets: int) -> list[dict[str, int]]:
    """Encode a cyclic affine edge by at most two ordinary interval isometries."""
    s, t = edge.sign, edge.shift % sheets
    if s == 1:
        breaks = [0, sheets] if t == 0 else [0, sheets - t, sheets]
    else:
        breaks = [0, sheets] if t == sheets - 1 else [0, t + 1, sheets]
    return [dict(u=edge.u, v=edge.v, sign=s, start=a, stop=b,
                 image_start=(s * a + t) % sheets)
            for a, b in zip(breaks, breaks[1:])]


def from_pairing_groups(vertices: int, sheets: int, dimension: int,
                        groups: list[list[dict[str, Any]]],
                        weights: list[dict[str, Any]] | None = None) -> Model:
    """Each supplied group must exactly cover one complete source fibre.

    Equal signs and modular shifts are checked from the actual interval maps.
    Gaps, overlap, endpoint overflow and conflicting maps are rejected. This
    validates a supplied decomposition; it does not discover one geometrically.
    """
    v, w, d = integer(vertices), integer(sheets), integer(dimension)
    if min(v, w, d) < 1:
        raise UnsupportedModel("positive block dimensions required")
    edges = []
    for group in groups:
        if not group:
            raise UnsupportedModel("empty full-fibre group")
        rows = []
        for row in group:
            if set(row) != {"u", "v", "sign", "start", "stop", "image_start"}:
                raise UnsupportedModel("invalid pairing fields")
            u, z, s, a, b, y = (integer(row[k], k) for k in
                                 ("u", "v", "sign", "start", "stop", "image_start"))
            if not (0 <= u < v and 0 <= z < v and s in (-1, 1) and
                    0 <= a < b <= w and 0 <= y < w and
                    0 <= y + s * (b - a - 1) < w):
                raise UnsupportedModel("invalid non-wrapping pairing")
            rows.append((a, b, u, z, s, (y - s * a) % w))
        rows.sort()
        expected = rows[0][2:]
        cursor = 0
        for a, b, *signature in rows:
            if a != cursor or tuple(signature) != expected:
                raise UnsupportedModel("pairings do not form one complete affine map")
            cursor = b
        if cursor != w:
            raise UnsupportedModel("partial fibre is not a full-fibre rule")
        u, z, s, t = expected
        edges.append(dict(u=u, v=z, sign=s, shift=t))
    return Model.parse(dict(vertices=v, sheets=w, dimension=d,
                            edges=edges, weights=weights or []))
