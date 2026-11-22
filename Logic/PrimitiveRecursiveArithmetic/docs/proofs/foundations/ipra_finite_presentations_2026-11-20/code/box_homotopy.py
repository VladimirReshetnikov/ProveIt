"""Exact rational evaluations of the box-nerve homotopies. Run python3 box_homotopy.py."""
from fractions import Fraction as Q
from itertools import product


def lerp(a, b, t):
    return tuple((1 - t) * x + t * y for x, y in zip(a, b))


class BoxNerve:
    def __init__(self, boxes):
        self.boxes = [tuple((Q(a), Q(b)) for a, b in box) for box in boxes]
        assert self.boxes
        self.d = len(self.boxes[0])
        assert all(len(B) == self.d and all(a <= b for a,b in B) for B in self.boxes)
        self.grid = [sorted({u for B in self.boxes for u in B[k]}) for k in range(self.d)]

    def containing(self, cell):
        return [i for i, B in enumerate(self.boxes)
                if all(lo <= a <= b <= hi for (lo, hi), (a, b) in zip(B, cell))]

    def F(self, x):
        x = tuple(map(Q, x))
        assert len(x) == self.d
        cell = tuple((max(t for t in row if t <= z), min(t for t in row if z <= t))
                     for row,z in zip(self.grid, x))
        charts = self.containing(cell)
        assert charts, 'point outside union'
        weights = tuple(Q(i in charts, len(charts)) for i in range(len(self.boxes)))
        center = tuple((a+b)/2 for a,b in cell)
        radial = max((abs(2*(z-c)/(b-a)) for z,c,(a,b) in zip(x,center,cell) if a < b),
                     default=Q(0))
        if radial == 0:
            return weights
        # At least one more coordinate of the endpoint lies on the grid.
        boundary = tuple(c+(z-c)/radial for c,z in zip(center, x))
        return lerp(weights, self.F(boundary), radial)

    def G(self, y):
        y = tuple(map(Q, y))
        assert len(y) == len(self.boxes) and min(y) >= 0 and sum(y) == 1
        levels = sorted(set(y) - {Q(0)}, reverse=True) + [Q(0)]
        x = [Q(0)] * self.d
        for t, next_t in zip(levels, levels[1:]):
            indices = [i for i, w in enumerate(y) if w >= t]
            coeff = len(indices) * (t - next_t)
            for k in range(self.d):
                low = max(self.boxes[i][k][0] for i in indices)
                assert low <= min(self.boxes[i][k][1] for i in indices), 'outside nerve'
                x[k] += coeff * low
        return tuple(x)

    def normalize_overlap(self, y):
        z = self.F(self.G(y))
        numerators = tuple(a*b for a,b in zip(y,z))
        denominator = sum(numerators)
        assert denominator >= Q(1, len(self.boxes)**2)
        return tuple(a/denominator for a in numerators), z

    def nerve_homotopy(self, y, t):
        assert 0 <= t <= 1
        middle, z = self.normalize_overlap(y)
        return lerp(y, middle, 2*t) if t <= Q(1,2) else lerp(middle, z, 2*t-1)

    def space_homotopy(self, x, t):
        assert 0 <= t <= 1
        return lerp(x, self.G(self.F(x)), t)


if __name__ == '__main__':
    example = BoxNerve([[(0,3),(0,1)],[(2,3),(0,3)],[(0,3),(2,3)],[(0,1),(0,3)]])
    times = [Q(i,4) for i in range(5)]
    npoints = 0
    for numerator in product(range(10), repeat=2):
        x = tuple(Q(k,3) for k in numerator)
        if not example.containing(tuple((u,u) for u in x)):
            continue
        weights = example.F(x)
        assert min(weights) >= 0 and sum(weights) == 1
        for t in times:
            q = example.space_homotopy(x,t)
            assert example.containing(tuple((u,u) for u in q))
        npoints += 1
    def nerve_test(example, cut):
        count = 0
        for nums in product(range(cut+1), repeat=len(example.boxes)):
            if sum(nums) != cut:
                continue
            y = tuple(Q(k,cut) for k in nums)
            I = [i for i,w in enumerate(y) if w > 0]
            if any(max(example.boxes[i][k][0] for i in I) >
                   min(example.boxes[i][k][1] for i in I) for k in range(example.d)):
                continue
            for t in times:
                z = example.nerve_homotopy(y,t)
                example.G(z)  # checks that support belongs to the nerve
                if t == 0:
                    assert z == y
                if t == 1:
                    assert z == example.F(example.G(y))
            count += 1
        return count
    nframe = nerve_test(example, 6)
    filled = BoxNerve([[(0,3),(0,2)],[(1,4),(0,3)],[(1,2),(1,2)],[(2,2),(1,4)]])
    nfilled = nerve_test(filled, 8)
    print(f'Exact rational homotopies at 5 times: {npoints} spatial points; '
          f'{nframe} frame and {nfilled} filled-nerve points.')
