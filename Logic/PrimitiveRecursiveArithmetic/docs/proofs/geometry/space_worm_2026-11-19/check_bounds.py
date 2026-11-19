"""Reconstruct the two-dimensional base and compute the spatial volume bounds."""
from decimal import Decimal, getcontext
from fractions import Fraction as F

PARAMETERS = (F(-631, 58), F(-1), F(7, 16), F(37, 56))
OFFSETS = (F(0), F(0), F(130783, 250000), F(446199, 1000000))
HEIGHT = F(4, 13)


def normal(t):
    return (1 - t*t) / (1 + t*t), 2*t / (1 + t*t)


def dot(p, q):
    return sum(x*y for x, y in zip(p, q))


def det(p, q):
    return p[0]*q[1] - p[1]*q[0]


def intersect(p, a, q, b):
    d = det(p, q)
    return (a*q[1] - b*p[1])/d, (b*p[0] - a*q[0])/d


def base_vertices():
    normals = tuple(map(normal, PARAMETERS))
    result = []
    for i in range(4):
        j = (i + 1) % 4
        v = intersect(normals[i], OFFSETS[i], normals[j], OFFSETS[j])
        assert all(dot(n, v) <= b for n, b in zip(normals, OFFSETS))
        result.append(v)
    return result


def centered_vertices():
    vertices = base_vertices()
    cx, cy = (sum(axis)/4 for axis in zip(*vertices))
    return [(x - cx, y - cy) for x, y in vertices]


def area(vertices):
    return abs(sum(det(u, v) for u, v in
                   zip(vertices, vertices[1:] + vertices[:1]))) / 2


def dec(fraction):
    return Decimal(fraction.numerator) / Decimal(fraction.denominator)


def main():
    getcontext().prec = 36
    base_area = area(base_vertices())
    factor = HEIGHT - 3*HEIGHT**3
    upper = factor * base_area
    assert base_area == F(7170601298323360123534337, 29109471743520000000000000)
    assert factor == F(484, 2197)
    # At the change of orientation, the Pythagorean triple is (5,12,13).
    assert (1 - 2*HEIGHT)**2 + 9*HEIGHT**2 == 1
    # Conservative length bounds for the two cited width-one curves.
    lengths = F("2.27830"), F("3.905124162243594")
    lower = 1 / (6*lengths[0]*lengths[1])
    assert lower > F("0.0187328")
    assert upper < F("0.0542671")
    print("Quadrilateral area     ", base_area, dec(base_area))
    print("Lift factor            ", factor, dec(factor))
    print("Upper bound            ", upper, dec(upper))
    print("Conservative lower     ", lower, dec(lower))
    print("Elementary lower       ", Decimal(3).sqrt()/96)
    print("Centered base vertices")
    for x, y in centered_vertices():
        print(f"  ({x}, {y})")


if __name__ == "__main__":
    main()
