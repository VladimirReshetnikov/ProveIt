"""Dodecahedron lower bound from an edge-compatible family of planar norms.

Uses the common face table and exact cyclotomic arithmetic in dodeca_lower.py.
Run both files from the same directory.
"""
from collections import Counter
from dodeca_lower import (ADJ, FACES, SOURCE, TARGET, adjacent_face,
                          basis_pentagon, nonnegative_phi, norm2, sub)

def less_equal(left, right):
    return nonnegative_phi(right[0]-left[0], right[1]-left[1])

def chart_vectors():
    """Collect squared radial values at a terminal face's five vertices."""
    sites = [set() for face in FACES]
    def visit(word, chart, origin):
        j = word[-1]
        values = tuple(norm2(sub(chart[v], origin)) for v in FACES[j])
        sites[j].add(values)
        if len(word) == 4:
            return
        for k in ADJ[j]:
            if k not in word:
                visit(word+(k,), adjacent_face(j,k,chart), origin)
    for i, face in enumerate(FACES):
        if SOURCE in face:
            chart = dict(zip(face,basis_pentagon))
            visit((i,),chart,chart[SOURCE])
    return sites

def frontier(sites, face, a, b):
    """Discard a pair if another row is at most it at both endpoints."""
    i,j = face.index(a), face.index(b)
    lines = {(s[i],s[j]) for s in sites}
    return tuple(sorted(row for row in lines if not any(
        row != other and all(less_equal(x,y) for x,y in zip(other,row))
        for other in lines)))

def main():
    sites = chart_vectors()
    edge_orbits = Counter()
    for i, face in enumerate(FACES):
        assert sites[i]
        for j in ADJ[i]:
            if i >= j:
                continue
            a,b = sorted(set(face) & set(FACES[j]))
            rows = frontier(sites[i],face,a,b)
            assert rows == frontier(sites[j],FACES[j],a,b)
            # A canonical endpoint order groups edges with identical data.
            key = min(rows,tuple(sorted((v,u) for u,v in rows)))
            edge_orbits[key] += 1
        for endpoint, lower in [(SOURCE,(0,0)),(TARGET,(5,7))]:
            if endpoint in face:
                values = {s[face.index(endpoint)] for s in sites[i]}
                assert lower in values and all(less_equal(lower,t) for t in values)
    assert sum(edge_orbits.values()) == 30
    print("Distinct sites by face:",*(len(s) for s in sites))
    print("Edges   Nondominated endpoint pairs (a,b stands for a+b*phi)")
    for rows,n in sorted(edge_orbits.items()):
        print(n, rows)
    print("All 30 edges glue and h(0)^2=0, h(7)^2=5+7*phi.")

if __name__ == '__main__':
    main()
