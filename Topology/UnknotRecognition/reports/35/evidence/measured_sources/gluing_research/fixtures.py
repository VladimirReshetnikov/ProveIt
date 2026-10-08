"""Exact assembled-surface families; no knot-exterior realization is asserted."""

import random

from .oracle import compatible


def piece(orientable=True, genus=0, boundaries=2, maps=((1, 0),)):
    return dict(surface=dict(orientable=orientable, genus=genus,
                             boundary_components=boundaries),
                monodromy=[dict(sign=s, shift=a) for s, a in maps])


def seam(left, right, direction=-1, affine=(1, 0)):
    return dict(left=list(left), right=list(right), direction=direction,
                map=dict(sign=affine[0], shift=affine[1]))


def klein_seam(sheets, shift=0):
    """For even W: b=0 gives two Klein bottles; b=1 gives one torus."""
    return dict(sheets=sheets, pieces=[piece(maps=((1, 2),))],
                seams=[seam((0, 0), (0, 1), 1, (-1, shift))])


def projective_cap(sheets, shift=0):
    return dict(sheets=sheets,
                pieces=[piece(False, 1, 1, ((-1, shift),)), piece(True, 0, 1, ())],
                seams=[seam((0, 0), (1, 0), -1)])


def genus_two(sheets):
    """Two trivial pants covers, sewn with identity, translation and reflection."""
    pants = piece(True, 0, 3, ((1, 0), (1, 0)))
    return dict(sheets=sheets, pieces=[pants, pants],
                seams=[seam((0, 0), (1, 0)), seam((0, 1), (1, 1), -1, (1, 4)),
                       seam((0, 2), (1, 2), -1, (-1, 0))])


def annulus_chain(sheets, count=8, closed_shift=None):
    """A tree of regauged annuli, optionally closed with Klein-type monodromy.

    Tree seam directions are negative.  Local core shifts alternate under
    chosen reflection gauges; affine translations contain large sheet data.
    The final seam, when present, has root holonomy x -> -x+closed_shift.
    """
    if count < 1:
        raise ValueError('count must be positive')
    pieces, seams = [], []
    gauge_sign, gauge_shift = 1, 0
    for v in range(count):
        pieces.append(piece(maps=((1, 2 * gauge_sign),)))
        if v + 1 < count:
            sign = -1 if v % 3 else 1
            shift = (sheets // (v + 2) + v * v + 1) % sheets
            seams.append(seam((v, 1), (v + 1, 0), -1, (sign, shift)))
            gauge_sign, gauge_shift = sign * gauge_sign, (sign * gauge_shift + shift) % sheets
    if closed_shift is not None:
        # A = P_last R; right peripheral is the inverse local core.
        affine = -gauge_sign, (gauge_sign * closed_shift + gauge_shift) % sheets
        seams.append(seam((0, 0), (count - 1, 1), 1, affine))
    return dict(sheets=sheets, pieces=pieces, seams=seams)


def random_assemblies(count=300, seed=20261008, max_sheets=12):
    rng = random.Random(seed)
    schemas = [(True, 0, 1), (True, 0, 2), (True, 0, 3), (True, 1, 1),
               (False, 1, 1), (False, 1, 2), (False, 2, 1)]
    for _ in range(count):
        n = rng.randrange(1, max_sheets + 1)
        pieces = []
        for _ in range(rng.randrange(1, 6)):
            orient, genus, boundaries = rng.choice(schemas)
            rank = (2 * genus if orient else genus) + boundaries - 1
            maps = [(rng.choice((-1, 1)), rng.randrange(-2 * n, 2 * n + 1))
                    for _ in range(rank)]
            pieces.append(piece(orient, genus, boundaries, maps))
        raw = dict(sheets=n, pieces=pieces, seams=[])
        ports = [(v, b) for v, p in enumerate(pieces)
                 for b in range(p['surface']['boundary_components'])]
        rng.shuffle(ports)
        while len(ports) >= 2 and rng.random() < 0.95:
            left, right = ports.pop(), ports.pop()
            candidates = [seam(left, right, e, (s, a)) for e in (-1, 1)
                          for s in (-1, 1) for a in range(n)]
            rng.shuffle(candidates)
            for candidate in candidates:
                if compatible(raw, candidate):
                    raw['seams'].append(candidate)
                    break
        yield raw
