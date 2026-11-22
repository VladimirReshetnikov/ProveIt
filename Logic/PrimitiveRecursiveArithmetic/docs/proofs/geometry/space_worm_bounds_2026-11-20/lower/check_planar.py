"""Verify a rational polygon of unit length or less and planar width >0.43892.

The vertices sample an Adhikari--Pitman caliper, but all assertions about
this polygon are checked by integer arithmetic without using their theorem.
"""
from itertools import combinations
from math import isqrt

LEFT = [
    (-521795048, 0), (-436435587, 285996592), (-433538032, 295531228),
    (-430545607, 305036516), (-427458611, 314511513), (-424277348, 323955277),
    (-421002136, 333366871), (-417633299, 342745360), (-414171172, 352089812),
    (-410616098, 361399300), (-406968432, 370672899), (-403228535, 379909689),
    (-399396778, 389108751), (-395473542, 398269174), (-391459216, 407390045),
    (-387354200, 416470461), (-383158900, 425509520), (-378873734, 434506323),
    (-374499127, 443459977), (-370035514, 452369594), (-365483337, 461234288),
    (-360843049, 470053179), (-356115110, 478825391), (-351299990, 487550053),
    (-346398168, 496226300), (-341410129, 504853268), (-336336370, 513430102),
    (-331177394, 521955950), (-325933713, 530429965), (-320605849, 538851305),
    (-315194330, 547219135), (-309699693, 555532623), (-304122485, 563790944),
    (-298463259, 571993277),
]

def verify():
    points = LEFT + [(0, 10**9)] + [(-x, y) for x, y in reversed(LEFT)]
    den = sum(1+isqrt((x-u)**2+(y-v)**2)
              for (x, y), (u, v) in zip(points, points[1:]))
    tests = 0
    for (x, y), (u, v) in combinations(points, 2):
        a, b = v-y, x-u
        assert a*a+b*b > 0
        scores = [a*i+b*j for i, j in points]
        span = max(scores)-min(scores)
        assert (100000*span)**2 > (43892*den)**2 * (a*a+b*b)
        tests += 1
    print(f"{len(points)} vertices, coordinate denominator {den}, {tests} pair normals.")
    print("The rational planar path has length below one and width greater than 0.43892.")

if __name__ == "__main__":
    verify()
