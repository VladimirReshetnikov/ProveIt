"""Exact finite checks of torsion metrics and a height-two Newton polygon."""
from collections import Counter
from fractions import Fraction
from itertools import product

def valuation(i, p):
    if i == 0:
        raise ValueError('finite valuation required')
    j = 0
    while i % p == 0:
        i //= p
        j += 1
    return j

def check_metric(p, d, h0, H):
    q, k = p**d, h0-1
    L = H-k
    modulus, base = p**H, p**L
    zero = (0,)*d
    def weight(x, level):
        order_exp = level - min(valuation(i,p) for i in x if i)
        return Fraction(1,(q-1)*q**(order_exp-1))
    def difference(a,b):
        return tuple((x-y)%modulus for x,y in zip(a,b))
    nodes = [u for u in product(range(base), repeat=d) if u!=zero]
    budget = Fraction(L, q**k)
    assert sum(weight(x,H) for x in nodes)==budget
    derivative = {x:sum(weight(difference(x,y),H) for y in nodes if y!=x)
                  for x in nodes}
    assert all(derivative[x]==budget-weight(x,H) for x in nodes)
    count = 0
    for z in product(range(modulus), repeat=d):
        u = tuple(i%base for i in z)
        if u==zero:
            continue
        count += 1
        if z!=u:
            assert sum(weight(difference(z,x),H) for x in nodes)>budget
    print(f'p={p} height={d} shells={h0}..{H}: {len(nodes)} nodes, {count} tested points, cost {budget}')

def multiply(a,b):
    c=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            c[i+j]+=x*y
    return c

def check_polygon(p,q,H):
    # The Lubin-Tate endomorphism p*T+T^q for the unramified residue field F_q.
    # Starting from T, iterate the actual polynomial, then compute its lower hull.
    f=[0,1]
    for _ in range(H):
        power=[1]
        for _ in range(q):
            power=multiply(power,f)
        for i,c in enumerate(f):
            power[i]+=p*c
        f=power
    hull=[]
    for i,c in enumerate(f):
        if not c:
            continue
        point=(i,valuation(c,p))
        while len(hull)>=2:
            a,b=hull[-2:]
            if (b[1]-a[1])*(i-b[0]) < (point[1]-b[1])*(b[0]-a[0]):
                break
            hull.pop()
        hull.append(point)
    slopes=Counter()
    for (i,a),(j,b) in zip(hull,hull[1:]):
        slopes[Fraction(a-b,j-i)]+=j-i
    assert slopes==Counter({Fraction(1,(q-1)*q**j):(q-1)*q**j for j in range(H)})
    print(f'Newton polygon p={p}, q={q}, H={H}: {hull}')

if __name__=='__main__':
    for case in [(2,2,1,3),(2,2,2,3),(3,2,2,3),(2,3,2,2)]:
        check_metric(*case)
    for case in [(3,9,2),(2,4,3),(2,8,2)]:
        check_polygon(*case)
