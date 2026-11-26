"""Illustrative level-71 coordinates, ordered as in Berkovich--Patane (4.2)--(4.4)."""
import json
import math


def theta(a, b, c, nmax):
    result = [0]*(nmax+1)
    ymax = math.isqrt(4*a*nmax//71)
    for y in range(-ymax, ymax+1):
        t = math.isqrt(4*a*nmax-71*y*y)
        for x in range(-((t+b*y)//(2*a)), (t-b*y)//(2*a)+1):
            result[a*x*x+b*x*y+c*y*y] += 1
    return result


def central_rows(nmax, intervals):
    al, be, ga = (2*math.cos(2*math.pi*j/7) for j in (1, 2, 3))
    coeff = [(1,ga,be,al), (1,al,ga,be), (1,be,al,ga)]
    counts = [theta(*t,nmax) for t in [(1,1,18),(2,1,9),(3,1,6),(4,3,5)]]
    forms = [[sum(w*b[n] for w,b in zip(row,counts))/2
              for n in range(1,nmax+1)] for row in coeff]
    # Composite Simpson rule for 2*int_{u>=0} u^j exp(u/2) f(i exp(u)/sqrt(71)) du.
    # The output is illustrative floating point; the cross-product formula is exact.
    data = [[], []]
    for form in forms:
        sums = [[], []]
        step = 6.0/intervals
        for i in range(intervals+1):
            u = i*step
            q = math.exp(-2*math.pi*math.exp(u)/math.sqrt(71))
            f = 0.0
            for a in reversed(form):
                f = (a+f)*q
            weight = 1 if i in (0,intervals) else (4 if i%2 else 2)
            g = weight * 2*step/3 * math.exp(u/2)*f
            sums[0].append(g)
            sums[1].append(g*u*u)
        for dest, pieces in zip(data,sums):
            dest.append(math.fsum(pieces))
    return data


def cross_product(A, B):
    return [A[(j+1)%3]*B[(j+2)%3]-A[(j+2)%3]*B[(j+1)%3] for j in range(3)]


if __name__ == '__main__':
    for nmax, intervals in ((60,1024), (100,2048)):
        a, b = central_rows(nmax, intervals)
        w = cross_product(a,b)
        print(json.dumps({"q_terms": nmax, "intervals": intervals,
                          "values": a, "second_derivatives": b,
                          "normalized_coordinates": [v/w[2] for v in w]}))
