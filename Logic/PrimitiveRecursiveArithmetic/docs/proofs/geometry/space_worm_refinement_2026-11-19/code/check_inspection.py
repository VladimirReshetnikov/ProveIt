"""Exact certificate for a ball contained in a unit worm hull.

Coordinates are in units of 1/SCALE. No numerical geometry library is needed.
Run with Python 3.8 or later.
"""
from itertools import combinations
from math import isqrt

SCALE = 10000000
RADIUS_NUMERATOR = 1043499
POINTS = [
    (-1143768, 1917789, -1160081),
    (-1077228, 1476548, -1276405),
    (-1026509, 1253255, -1333190),
    (-963433, 1048033, -1382323),
    (-889462, 859292, -1423572),
    (-805926, 685818, -1456742),
    (-714027, 526618, -1481691),
    (-614868, 380907, -1498318),
    (-509484, 248082, -1506562),
    (-398832, 127649, -1506405),
    (-283791, 19219, -1497860),
    (-165252, -77448, -1480979),
    (-44128, -162487, -1455875),
    (78739, -236028, -1422708),
    (202634, -298200, -1381651),
    (326875, -349060, -1332898),
    (450731, -388582, -1276699),
    (573465, -416704, -1213367),
    (694407, -433350, -1143239),
    (812928, -438409, -1066679),
    (928410, -431736, -984095),
    (1040262, -413149, -895935),
    (1147923, -382429, -802683),
    (1250846, -339319, -704874),
    (1346381, -284742, -605312),
    (1425998, -225846, -509663),
    (1486805, -168980, -416312),
    (1534268, -110877, -319385),
    (1568320, -51808, -219994),
    (1588986, 7446, -118852),
    (1596295, 66698, -16922),
    (1590304, 125238, 85192),
    (1571037, 182902, 186574),
    (1538539, 238970, 286605),
    (1492845, 293247, 384307),
    (1434053, 344954, 478962),
    (1362308, 393831, 569464),
    (1268477, 444059, 664487),
    (1157808, 487004, 764835),
    (1042391, 516182, 861489),
    (923741, 531613, 952970),
    (802444, 533639, 1038722),
    (679121, 522561, 1118234),
    (554432, 498640, 1191040),
    (429072, 462100, 1256720),
    (303765, 413134, 1314896),
    (179267, 351895, 1365240),
    (56377, 278505, 1407464),
    (-64069, 193051, 1441326),
    (-181209, 95569, 1466636),
    (-294147, -13967, 1483249),
    (-401939, -135642, 1491067),
    (-503571, -269595, 1490040),
    (-597982, -416054, 1480172),
    (-684058, -575385, 1461517),
    (-760605, -748095, 1434177),
    (-826319, -934858, 1398308),
    (-879765, -1136539, 1354126),
    (-919348, -1354233, 1301914),
    (-943300, -1589467, 1241999),
    (-954376, -2039553, 1123209),
]


def sub(a, b):
    return tuple(x - y for x, y in zip(a, b))


def dot(a, b):
    return sum(x * y for x, y in zip(a, b))


def cross(a, b):
    return (a[1] * b[2] - a[2] * b[1],
            a[2] * b[0] - a[0] * b[2],
            a[0] * b[1] - a[1] * b[0])


def verify():
    length_upper = 0
    for a, b in zip(POINTS, POINTS[1:]):
        v = sub(a, b)
        length_upper += isqrt(dot(v, v) - 1) + 1
    assert length_upper <= SCALE
    a, b, c, d = POINTS[:4]
    assert dot(cross(sub(b, a), sub(c, a)), sub(d, a)) != 0
    support_triples = 0
    for a, b, c in combinations(POINTS, 3):
        normal = cross(sub(b, a), sub(c, a))
        norm_sq = dot(normal, normal)
        if norm_sq == 0:
            continue
        offset = dot(a, normal)
        sides = [dot(q, normal) - offset for q in POINTS]
        if min(sides) < 0 < max(sides):
            continue
        if min(sides) >= 0:
            offset = -offset
        # The normal points outwards after the preceding sign choice.
        assert offset > 0
        assert offset**2 >= RADIUS_NUMERATOR**2 * norm_sq
        support_triples += 1
    assert support_triples >= 4
    print(f"Length <= {length_upper}/{SCALE}; " 
          f"centered ball radius >= {RADIUS_NUMERATOR}/{SCALE}; "
          f"{support_triples} supporting triples checked.")


if __name__ == "__main__":
    verify()
