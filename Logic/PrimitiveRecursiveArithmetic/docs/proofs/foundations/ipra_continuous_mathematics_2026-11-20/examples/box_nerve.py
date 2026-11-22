"""Exact evaluators and a regression example for the closed-box nerve theorem.

Run with Python 3. Only the standard library is used. Arguments are rational;
a rational input point must belong to the represented subspace.
"""
from fractions import Fraction as Q
from itertools import product


class BoxNerve:
    def __init__(self, boxes):
        self.boxes = tuple(tuple((Q(a), Q(b)) for a, b in box) for box in boxes)
        if not self.boxes:
            raise ValueError("an initial box is required")
        self.dim = len(self.boxes[0])
        if any(len(b) != self.dim or any(a > z for a, z in b)
               for b in self.boxes):
            raise ValueError("check dimensions and endpoint order")
        self.knots = [sorted({v for box in self.boxes for v in box[j]})
                      for j in range(self.dim)]

    def corner(self, indices):
        """Return the lower corner of a nonempty intersection or None."""
        if not indices:
            raise ValueError("a nonempty face is required")
        lower = tuple(max(self.boxes[i][j][0] for i in indices)
                      for j in range(self.dim))
        upper = tuple(min(self.boxes[i][j][1] for i in indices)
                      for j in range(self.dim))
        return lower if all(a <= b for a, b in zip(lower, upper)) else None

    def containing(self, x):
        return {i for i, box in enumerate(self.boxes)
                if all(a <= v <= b for (a, b), v in zip(box, x))}

    def grid_face(self, x):
        return [(max(v for v in knots if v <= u),
                 min(v for v in knots if v >= u))
                for knots, u in zip(self.knots, x)]

    def forward(self, x):
        """Evaluate F by radial barycentric decomposition."""
        x = tuple(map(Q, x))
        if len(x) != self.dim or not self.containing(x):
            raise ValueError("input outside the union")
        result = [Q(0)] * len(self.boxes)
        mass = Q(1)
        for _ in range(self.dim + 1):
            face = self.grid_face(x)
            center = [(a + b) / 2 for a, b in face]
            indices = self.containing(center)
            assert indices
            radius = max((abs((2*v-a-b)/(b-a)) for (a, b), v in zip(face, x)
                          if a != b), default=Q(0))
            for i in indices:
                result[i] += mass * (1-radius) / len(indices)
            if radius == 0:
                return tuple(result)
            mass *= radius
            x = tuple(c + (v-c)/radius for c, v in zip(center, x))
        raise AssertionError("dimension failed to decrease")

    def backward(self, y):
        """Evaluate G from the nested superlevel sets of simplex coordinates."""
        y = tuple(map(Q, y))
        assert len(y) == len(self.boxes) and min(y) >= 0 and sum(y) == 1
        levels = sorted({v for v in y if v > 0}, reverse=True) + [Q(0)]
        result = [Q(0)] * self.dim
        for level, next_level in zip(levels, levels[1:]):
            face = [j for j, v in enumerate(y) if v >= level]
            point = self.corner(face)
            if point is None:
                raise ValueError("support outside the nerve")
            scale = len(face) * (level-next_level)
            for j in range(self.dim):
                result[j] += scale * point[j]
        return tuple(result)

    def overlap_point(self, y):
        v = self.forward(self.backward(y))
        z = [min(a, b) for a, b in zip(y, v)]
        mass = sum(z)
        assert mass >= Q(1, len(self.boxes))
        return tuple(a/mass for a in z), mass


def frame(t=Q(0)):
    return BoxNerve([[(a-t, b+t) for a, b in box] for box in
                     [((0, 3), (0, 1)), ((2, 3), (0, 3)),
                      ((0, 3), (2, 3)), ((0, 1), (0, 3))]])


def verify():
    geom = frame()
    y = (Q(3, 4), Q(1, 4), Q(0), Q(0))
    assert geom.backward(y) == (1, 0)
    assert geom.forward((1, 0)) == (Q(1, 2), 0, 0, Q(1, 2))
    assert geom.overlap_point(y) == ((1, 0, 0, 0), Q(1, 2))
    assert geom.corner([0, 1, 3]) is None

    for pairs in product(range(11), repeat=2):
        x = tuple(Q(v, 3) for v in pairs)
        cover = geom.containing(x)
        if cover:
            y = geom.forward(x)
            assert sum(y) == 1 and min(y) >= 0
            assert all(y[i] >= Q(1, 4) for i in cover)
            assert cover & geom.containing(geom.backward(y))

    for counts in product(range(7), repeat=4):
        if sum(counts) != 6:
            continue
        y = tuple(Q(v, 6) for v in counts)
        support = [i for i, v in enumerate(y) if v]
        if geom.corner(support) is not None:
            middle, _ = geom.overlap_point(y)
            other = geom.forward(geom.backward(y))
            assert sum(middle) == 1
            assert all(not p or (a and b) for p, a, b in zip(middle, y, other))

    for t in [Q(0), Q(49, 100), Q(1, 2), Q(51, 100)]:
        thick = frame(t)
        faces = [[i for i in range(4) if (mask >> i) & 1] for mask in range(1, 16)]
        sizes = [len(face) for face in faces if thick.corner(face) is not None]
        counts = tuple(sizes.count(q) for q in (1, 2, 3, 4))
        assert counts == ((4, 4, 0, 0) if t < Q(1, 2) else (4, 6, 4, 1))
        print(f"t={t}: nonempty faces by size {counts}")

    point = BoxNerve([[(-2, -2), (3, 3)]])
    assert point.forward((-2, 3)) == (1,) and point.backward([1]) == (-2, 3)
    print("PASS: box intersections, both evaluators, common support and threshold")


if __name__ == "__main__":
    verify()
