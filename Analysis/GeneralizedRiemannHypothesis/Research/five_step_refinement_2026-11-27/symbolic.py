"""Symbolic certificates and finite witnesses; requires SymPy."""
from sympy import symbols, Poly, ZZ, expand, rem, resultant, discriminant, factorint, gcd
t,v,X,s=symbols('t v X s')
U=2*t+2*v*X+2*X**2-t*t*X**3
def constant(m):
    P=Poly(expand(U**m),X)
    return expand(sum(P.nth(i) for i in range(0,3*m+1,5)))
f=64*v**3-96*t**3*v**2-8*t*(t**5-24)*v-56*t**4
F=128+352*s+367*s*s; G=-768-1122*s+53*s*s; H=320+670*s*s
R=t*F.subs(s,t**5)+t**3*G.subs(s,t**5)*v+H.subs(s,t**5)*v*v
assert expand(constant(4)-f)==0
assert expand(rem(constant(6),f,v)-3*R)==0
rr=[int(resultant(x,y,s)) for x,y in ((F,G),(F,H),(G,H))]
assert sorted(rr)==sorted([27568640000,552418240000,28768960000])
assert gcd(gcd(rr[0],rr[1]),rr[2])==38720000
def poly(L):return sum(c*s**i for i,c in enumerate(L))
P=poly([252928,489984,1480832,78716,9003])
Q=poly([-532480,-191488,-4536064,-283272,291464,77])
assert expand(rem(f,R,v)*H.subs(s,t**5)**2).expand().cancel().expand()==expand(-32*t**4*P.subs(s,t**5)-32*t*Q.subs(s,t**5)*v)
fac=factorint(abs(resultant(P,Q,s)))
assert fac=={2:42,5:24,11:10,13:2,31:2,761:1,1297:1}
C=poly([-354418688,-419381248,-3296137216,-3222697984,881034240,7486204,-75721176,151118,77])
D=poly([-27648,21492,-4356,11])
assert expand(resultant(f,R,v)+1024*t**3*C.subs(s,t**5))==0
assert expand(discriminant(f,v)-65536*t**3*D.subs(s,t**5))==0
assert Poly(C,s,modulus=3).degree()==8 and Poly(D,s,modulus=3).degree()==3
assert Poly(C,s,modulus=3).gcd(Poly(D,s,modulus=3)).degree()==0
print("Polynomial remainders, discriminant, and all resultant certificates verified.")
def evalfR(p,t):
    s=pow(t,5,p)
    return (64%p,(-96*t**3)%p,(-8*t*(s-24))%p,(-56*t**4)%p,
            (320+670*s*s)%p,(t**3*(-768-1122*s+53*s*s))%p,
            (t*(128+352*s+367*s*s))%p)
def roots(p,t):
    a,b,c,d,e,g,h=evalfR(p,t)
    return (tuple(v for v in range(p) if not (((a*v+b)*v+c)*v+d)%p),
            tuple(v for v in range(p) if not ((e*v+g)*v+h)%p))
assert all(not set(roots(761,t)[0]).intersection(roots(761,t)[1]) for t in range(1,761))
print("All t nonzero mod 761 checked: no common f,R root.")
for p in (1031,1511,1571,2281,2351):
    z=264 if p==1031 else next(z for z in range(2,p) if pow(z,5,p)==1)
    a=[pow(z,i,p) for i in range(5)]
    def row(t):
        return [(t+x*x-t*t*pow(2,-1,p)*x*x*x)%p for x in a]
    def evalpoly(L,s):
        e=0
        for c in reversed(L):e=(e*s+c)%p
        return e
    for t in range(1,p):
        if evalpoly([-354418688,-419381248,-3296137216,-3222697984,881034240,7486204,-75721176,151118,77],pow(t,5,p)):
            continue
        r,k=roots(p,t)
        if len(r)!=3 or len(set(r).intersection(k))!=1:
            continue
        b=row(t)
        def j(v):
            w=[(v*x+y)%p for x,y in zip(a,b)]
            return next(j for j in range(1,6) if sum(pow(x,2*j,p) for x in w)%p)
        assert sorted(map(j,r))==[3,3,4]
        S=list(zip(a,b))
        assert len({min((x,y),(-x%p,-y%p)) for x,y in S})==5
        print(p,z,t,r,S)
        break
    else: raise AssertionError(p)

# Direct moment evaluation on every simple witness in the small search.
from pathlib import Path
import re
for line in Path('small_benchmarks.txt').read_text().splitlines():
    p,counts,maxima,*_=line.split()
    p=int(p)
    S=[(1,0),(0,1)]+[tuple(map(int,q)) for q in re.findall(r'\((\d+),(\d+)\)',line)]
    assert len(S)==len({min((x,y),(-x%p,-y%p)) for x,y in S})==5 and (0,0) not in S
    A=2*sum(next(j for j in range(1,6) if sum(pow(a*x+b*y,2*j,p) for x,y in S)%p)
            for a,b in [(1,t) for t in range(p)]+[(0,1)])
    assert A==int(maxima.split('/')[-1])
print("All fifteen simple witnesses independently rescored.")
