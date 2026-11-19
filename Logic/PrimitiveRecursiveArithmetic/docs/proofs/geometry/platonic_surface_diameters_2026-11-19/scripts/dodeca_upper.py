"""Exact flag-strip certificates for the dodecahedron. Distances use unit edges.

Chart points are scaled by 10 so vertices, midpoints and face centres
all have coefficients in Z[z]/(1+z+z^2+z^3+z^4).
"""
from itertools import product
from dodeca_lower import (FACES, ADJ, basis_pentagon, adjacent_face,
                          add, sub, conjugate, mul, norm2, nonnegative_phi, ZERO)

def scale(n, p):
    return tuple(n * x for x in p)

# Real elements are represented by a+b*phi. These are the operations needed
# for comparing oriented areas and parameters without division.
def kmul(p, q):
    a, b = p
    c, d = q
    return (a*c+b*d, a*d+b*c+b*d)

def ksub(p,q):
    return (p[0]-q[0],p[1]-q[1])

def nonneg(p):
    return nonnegative_phi(*p)

def det(p, q):
    # Im(conj(p)*q)/sin(72 degrees). sin(144)/sin(72)=phi-1.
    _, b, c, d = mul(conjugate(p), q)
    return (b-c+d,c-d)

def ordered_crossings(s, t, hinges):
    d = sub(t,s)
    last_n, last_d = (0,0), (1,0)
    intervals = [((0,1),(1,5)), ((1,3),(1,2)), ((2,3),(5,6))]
    for (a,b),(left,right) in zip(hinges, intervals):
        h = sub(b,a)
        den = det(d,h)
        if den == (0,0):
            return False
        num = det(sub(a,s),h)
        side = det(sub(a,s),d)
        if not nonneg(den):
            den,num,side = [scale(-1,v) for v in (den,num,side)]
        checks = [ksub(scale(left[1],num),scale(left[0],den)),
                  ksub(scale(right[0],den),scale(right[1],num)),
                  num,ksub(den,num),side,ksub(den,side),
                  ksub(kmul(num,last_d),kmul(last_n,den))]
        if not all(nonneg(x) for x in checks):
            return False
        last_n,last_d = num,den
    return True

def corners(chart, a, b):
    total = ZERO
    for point in chart.values():
        total=add(total,point)
    return [scale(10,chart[a]),scale(5,add(chart[a],chart[b])),scale(2,total)]

def antipodes():
    graph={v:set() for face in FACES for v in face}
    for face in FACES:
        for i,v in enumerate(face):
            graph[v].add(face[i-1])
            graph[face[i-1]].add(v)
    opp={}
    for v in graph:
        seen={v}
        for _ in range(4):
            seen |= set().union(*(graph[u] for u in seen))
        far=set(graph)-seen
        assert len(far)==1
        opp[v]=next(iter(far))
        assert graph[opp[v]] & seen
    return opp

def coordinates(path):
    opp=antipodes()
    v,m=FACES[0][:2]
    chart=dict(zip(FACES[0],basis_pentagon))
    source=corners(chart,v,m)
    hinges=[]
    for a,b in zip(path,path[1:]):
        u,w=sorted(set(FACES[a]) & set(FACES[b]))
        hinges.append((scale(10,chart[u]),scale(10,chart[w])))
        chart=adjacent_face(a,b,chart)
    assert set(chart)=={opp[i] for i in FACES[0]}
    return source,corners(chart,opp[v],opp[m]),hinges

def compute(path):
    s,t,hinges = coordinates(path)
    if not all(ordered_crossings(x,y,hinges) for x,y in product(s,t)):
        return None
    return [[norm2(sub(x,y)) for y in t] for x in s]

def check():
    path = (0, 2, 8, 11)
    matrix = compute(path)
    assert matrix is not None
    deficit = [[ksub((1000, 1400),
                     tuple(matrix[i][j][k] + matrix[j][i][k] for k in range(2)))
                for j in range(3)] for i in range(3)]
    assert deficit == [[(0, 0), (50, 50), (20, 60)],
                       [(50, 50), (100, 50), (70, 10)],
                       [(20, 60), (70, 10), (80, 40)]]
    return path, matrix, deficit

if __name__=="__main__":
    path, mat, deficit = check()
    print("Face strip:",path)
    print("100 times squared distances, each entry is the pair (a,b) for a+b*phi")
    for row in mat: print(row)
    print("200 times gap between D^2 and transpose-averaged squared lengths")
    for row in deficit: print(row)
