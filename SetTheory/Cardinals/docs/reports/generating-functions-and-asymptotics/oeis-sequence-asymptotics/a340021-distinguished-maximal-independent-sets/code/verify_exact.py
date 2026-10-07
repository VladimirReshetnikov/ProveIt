"""Exact, optimization-safe checks. Floating diagnostics are a separate file."""
from fractions import Fraction as F
from functools import lru_cache
from itertools import permutations
from math import factorial, gcd, comb
import json

def require(condition, text):
    if not condition:
        raise RuntimeError(text)

@lru_cache(None)
def parts(n, lo=1):
    if n == 0:
        return ((),)
    return tuple((i,) + p for i in range(lo, n+1) for p in parts(n-i, i))

def z(p):
    out=1
    for i in set(p):
        out *= i**p.count(i)*factorial(p.count(i))
    return out

def edge_orbits(p):
    return sum(i//2 for i in p)+sum(gcd(p[i],p[j]) for i in range(len(p)) for j in range(i))

def dom(u,v):
    ans=1
    for ell in u:
        ans *= 2**sum(gcd(ell,b) for b in v)-1
    return ans

def count(n,k):
    return sum((F(2**edge_orbits(u)*dom(u,v),z(u)*z(v))
                for u in parts(n-k) for v in parts(k)),F(0))

OEIS=[1,1,2,5,16,66,407,3948,66781,2057140,117820559,12562407832,
2488441442819,915216371901462,625792587599236833,797474948692631218674,
1899724021357155410243835,8486672841492724213636009230,
71324140440429733888694354552551,1131126439181050621704917376323373818]

def canonical_brute(n):
    edges=[(i,j) for j in range(n) for i in range(j)]
    index={e:i for i,e in enumerate(edges)}
    # Orbit canonicalization independent of the cycle-type Burnside formula.
    maps=[]
    for p in permutations(range(n)):
        maps.append((p,[index[tuple(sorted((p[i],p[j])))] for i,j in edges]))
    orbits=set()
    for g in range(1<<len(edges)):
        adj=[0]*n
        for bit,(i,j) in enumerate(edges):
            if g>>bit&1:
                adj[i]|=1<<j;adj[j]|=1<<i
        for b in range(1<<n):
            if any((b>>i&1) and adj[i]&b for i in range(n)):
                continue
            if any(not (b>>i&1) and not (adj[i]&b) for i in range(n)):
                continue
            candidates=[]
            for p,em in maps:
                bg=sum((1<<p[i]) for i in range(n) if b>>i&1)
                gg=sum((1<<em[i]) for i in range(len(edges)) if g>>i&1)
                candidates.append((bg,gg))
            orbits.add(min(candidates))
    return len(orbits)

def poly_add(x,y):
    out=dict(x)
    for k,v in y.items():out[k]=out.get(k,F(0))+v
    return {k:v for k,v in out.items() if v}

def poly_mul(x,y,R):
    out={}
    for i,a in x.items():
        for j,b in y.items():
            if i+j<=R:out[i+j]=out.get(i+j,F(0))+a*b
    return {k:v for k,v in out.items() if v}

def formal_exp(c,R):
    p=[F(1)]
    for j in range(1,R+1):
        p.append(sum((r*c[r]*p[j-r] for r in range(1,j+1)),F(0))/j)
    return p

def formal_coefficients(k,y,R):
    C=[F(0)]+[-F(sum(i**r for i in range(k)),r)+F(k,r)*y**r-F(1,r+1)*y**(r+1) for r in range(1,R+1)]
    return C,formal_exp(C,R)

def direct_series(k,y,R):
    # Product for the falling factorial; separate exact log of the dominance factor.
    fall={0:F(1)}
    for i in range(k):fall=poly_mul(fall,{0:F(1),1:F(-i)},R)
    D=[F(0)]+[F(k,r)*y**r-F(1,r+1)*y**(r+1) for r in range(1,R+1)]
    expD={i:v for i,v in enumerate(formal_exp(D,R))}
    result=poly_mul(fall,expD,R)
    return [result.get(i,F(0)) for i in range(R+1)]

def bernoulli(N):
    b=[F(1)]
    for n in range(1,N+1):
        b.append(-sum((F(comb(n+1,k))*b[k] for k in range(n)),F(0))/F(n+1))
    return b

def shifted_stirling(j,R):
    b=bernoulli(R+1)
    c=[F(0)]
    for r in range(1,R+1):
        bp=sum((F(comb(r+1,k))*b[k]*F(j+1)**(r+1-k) for k in range(r+2)),F(0))
        c.append(F((-1)**r,r*(r+1))*bp)
    return formal_exp(c,R)

def shift_direct(j,R):
    base=shifted_stirling(0,R)
    out={i:v for i,v in enumerate(base)}
    if j>=0:
        for ell in range(1,j+1):
            out=poly_mul(out,{r:F((-ell)**r) for r in range(R+1)},R)
    else:
        for ell in range(j+1,1):
            out=poly_mul(out,{0:F(1),1:F(ell)},R)
    return [out.get(i,F(0)) for i in range(R+1)]

def main():
    rows=[]
    for n in range(20):
        row=[count(n,k) for k in range(n+1)]
        require(all(v.denominator==1 for v in row),f"noninteger row {n}")
        total=sum(row,F(0))
        require(total==OEIS[n],f"OEIS mismatch at {n}")
        rows.append([int(v) for v in row])
    brute=[]
    for n in range(6):
        c=canonical_brute(n)
        require(c==OEIS[n],f"brute mismatch at {n}")
        brute.append(c)
    support_checks=0
    for n in range(1,19):
        for k in range(1,n+1):
            m=n-k
            I=2**comb(m,2)*(2**k-1)**m
            for u in parts(m):
                t=m-u.count(1); D=comb(m,2)-edge_orbits(u)
                require(4*D>=t*(2*m-t-2),"edge deficit")
                for v in parts(k):
                    s=k-v.count(1);d=k-len(v)
                    require(2*d>=s,"black support")
                    fixed=2**edge_orbits(u)*dom(u,v)
                    require(fixed*2**(D+d*(m-t))<=I,"fixed/identity loss")
                    if t<=m/2 and m>=4:
                        require(4*(D+d*(m-t))>=m*(s+t),"small white support loss")
                    if t>m/2:
                        require(8*D>=m*(m-2),"large white support loss")
                    support_checks+=1
    algebra_checks=0
    for k in range(1,21):
        for y in [F(0),F(1,3),F(1),F(7,2),F(13)]:
            c,p=formal_coefficients(k,y,6)
            require(p==direct_series(k,y,6),"formal expansion mismatch")
            C1=-F(k*(k-1),2)+k*y-y*y/2
            C2=-F(k*(k-1)*(2*k-1),12)+k*y*y/2-y**3/3
            C3=-F(k*k*(k-1)**2,12)+k*y**3/3-y**4/4
            require(c[1:4]==[C1,C2,C3],"displayed Cs")
            require(p[1:4]==[C1,C2+C1*C1/2,C3+C1*C2+C1**3/6],"displayed Ps")
            algebra_checks+=1
    shift_checks=0
    for j in range(-12,13):
        p=shifted_stirling(j,8)
        require(p==shift_direct(j,8),"shifted Stirling mismatch")
        require(p[1]==-F(j*(j+1),2)-F(1,12),"shift p1")
        shift_checks+=1
    return {"status":"PASS","source":"https://oeis.org/A340021","oeis_terms":OEIS,
            "burnside_rows":rows,"independent_brute_totals":brute,
            "support_inequalities_checked":support_checks,"formal_points_through_order_6":algebra_checks,
            "shifted_stirling_points_through_order_8":shift_checks,
            "certification_scope":"Exact finite identities only; asymptotic proofs are in Report206."}

if __name__=='__main__':
    print(json.dumps(main(),indent=2,sort_keys=True))
