#!/usr/bin/env python3
"""Exact rational regression checks for formulas in affine_metric.tex.

These finite checks detect formula/transcription errors; they are not proofs
of the universally quantified mathematical statements.
"""
from fractions import Fraction as F
from pathlib import Path
import json
import random


def add(u, v):
    return tuple(a + b for a, b in zip(u, v))


def sub(u, v):
    return tuple(a - b for a, b in zip(u, v))


def scale(a, u):
    return tuple(a * x for x in u)


def dot(u, v):
    return sum(a * b for a, b in zip(u, v))


def sq(u):
    return dot(u, u)


def det(u, v):
    return u[0] * v[1] - u[1] * v[0]


def turn(u):
    return (-u[1], u[0])


def cross(u, v):
    return (u[1] * v[2] - u[2] * v[1],
            u[2] * v[0] - u[0] * v[2],
            u[0] * v[1] - u[1] * v[0])


def foot(x, p, u):
    return add(p, scale(dot(sub(x, p), u) / sq(u), u))


def run():
    rng = random.Random(20261122)
    counts = dict(planar_lagrange=0, triangle_centers=0,
                  circle_radical_axis=0, tangent_formula=0,
                  cross_triple=0, two_planes=0, skew_lines=0,
                  normal_reflection=0, shoelace=0)

    def q():
        return F(rng.randint(-9, 9), rng.randint(1, 9))

    def vec(d):
        return tuple(q() for _ in range(d))

    for _ in range(250):
        a, b, c = vec(2), vec(2), vec(2)
        u, v = sub(b, a), sub(c, a)
        assert sq(u) * sq(v) - dot(u, v) ** 2 == det(u, v) ** 2
        counts['planar_lagrange'] += 1
        if det(u, v):
            o = add(a, scale(F(1, 2) / det(u, v),
                            sub(scale(sq(v), turn(u)), scale(sq(u), turn(v)))))
            r2 = sq(sub(o, a))
            assert r2 == sq(sub(o, b)) == sq(sub(o, c))
            h = sub(add(add(a, b), c), scale(2, o))
            n = scale(F(1, 2), add(o, h))
            for p, z, w in ((a, b, c), (b, c, a), (c, a, b)):
                assert dot(sub(h, p), sub(z, w)) == 0
                for x in (scale(F(1, 2), add(z, w)),
                          scale(F(1, 2), add(p, h)),
                          foot(p, z, sub(w, z))):
                    assert sq(sub(x, n)) == r2 / 4
            counts['triangle_centers'] += 1

        o1, o2 = vec(2), vec(2)
        w = sub(o2, o1)
        d = sq(w)
        if d:
            r1, r2 = abs(q()), abs(q())
            t = (d + r1 - r2) / (2 * d)
            h = add(o1, scale(t, w))
            k = r1 - t * t * d
            # A symbolic coefficient s satisfying s^2=k/d gives both circles:
            assert dot(sub(h, o1), w) == (d + r1 - r2) / 2
            assert sq(sub(h, o1)) + k == r1
            assert sq(sub(h, o2)) + k == r2
            counts['circle_radical_axis'] += 1
            r2 = d / 3
            base = scale(r2 / d, w)
            # The coefficient on Jw has square r2*(d-r2)/d^2.
            coeff2 = r2 * (d - r2) / (d * d)
            assert sq(base) + coeff2 * d == r2
            assert dot(w, base) == r2
            counts['tangent_formula'] += 1

        u, v, w = vec(3), vec(3), vec(3)
        k = cross(u, v)
        assert dot(u, k) == dot(v, k) == 0
        assert sq(k) == sq(u) * sq(v) - dot(u, v) ** 2
        assert cross(u, cross(v, w)) == sub(scale(dot(u, w), v), scale(dot(u, v), w))
        counts['cross_triple'] += 1
        if sq(k):
            c0, d0 = q(), q()
            x0 = scale(1 / sq(k), add(scale(c0, cross(v, k)), scale(d0, cross(k, u))))
            assert dot(u, x0) == c0 and dot(v, x0) == d0
            counts['two_planes'] += 1
            # Two line directions u,v, with displacement w.
            aa, bb, cc = sq(u), dot(u, v), sq(v)
            rhs1, rhs2 = dot(u, w), -dot(v, w)
            t = (cc * rhs1 + bb * rhs2) / sq(k)
            s = (bb * rhs1 + aa * rhs2) / sq(k)
            delta = sub(add(w, scale(s, v)), scale(t, u))
            assert dot(delta, u) == dot(delta, v) == 0
            assert sq(delta) == dot(w, k) ** 2 / sq(k)
            counts['skew_lines'] += 1
        if sq(u):
            c0 = q()

            def reflect(x):
                return sub(x, scale(2 * (dot(u, x) - c0) / sq(u), u))

            assert reflect(reflect(v)) == v
            assert sq(sub(reflect(v), reflect(w))) == sq(sub(v, w))
            counts['normal_reflection'] += 1

        points, origin = [vec(2) for _ in range(rng.randint(3, 12))], vec(2)
        edges = list(zip(points, points[1:] + points[:1]))
        assert sum(det(sub(p, origin), sub(z, origin)) for p, z in edges) == sum(det(p, z) for p, z in edges)
        counts['shoelace'] += 1

    result = {'status': 'passed', 'arithmetic': 'fractions.Fraction (exact)',
              'seed': 20261122, 'rounds': 250,
              'checks_by_family': counts,
              'limitation': 'Finite regression checks, not formal or universal proofs.'}
    output = Path(__file__).resolve().parents[1] / 'artifacts' / 'affine_metric_validation.json'
    output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    run()
