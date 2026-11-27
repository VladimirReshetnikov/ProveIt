"""Independent incidence and orbit checks for the two distribution formulas."""
from collections import Counter
from itertools import permutations, product

def projective(p,n):
    for i in range(n):
        for v in product(range(p),repeat=n-i-1):
            yield (0,)*i+(1,)+v

def q(v):
    return sum(x*x for x in v)

def depth(p,v,m):
    return next(j for j in range(1,m+1) if sum(pow(x,2*j,p) for x in v)%p)

def three(p):
    conic=[v for v in projective(p,3) if q(v)%p==0]
    marked=[v for v in conic if depth(p,v,3)==3]
    assert len(conic)==p+1
    squares={x*x%p for x in range(1,p)}
    all_counts,simple_counts=Counter(),Counter()
    winners=set()
    for n in projective(p,3):
        hits=[v for v in conic if sum(a*b for a,b in zip(n,v))%p==0]
        score=sum(2*(depth(p,v,3)-1) for v in hits)
        all_counts[score]+=1
        nz=[a*a%p for a in n if a]
        if not (len(nz)==1 or len(nz)==2 and nz[0]==nz[1]):
            simple_counts[score]+=1
            if score==8:winners.add(n)
    t=p-7
    if p%6==1:
        expected={0:p*(p-1)//2,2:t,4:8+t*(t-1)//2,6:8*t,8:28}
        assert len(marked)==8 and len(winners)==28
        z=next(a for a in range(2,p) if pow(a,3,p)==1)
        def orbit(v):
            out=set()
            for order in permutations(v):
                for e in product((1,-1),repeat=3):
                    u=[a*b%p for a,b in zip(order,e)]
                    d=pow(next(a for a in u if a),-1,p)
                    out.add(tuple(a*d%p for a in u))
            return out
        orbits=[orbit(n) for n in [(0,-z,1),(1,1,1),(z*z-z,1,-1)]]
        assert list(map(len,orbits))==[12,4,12]
        assert set.union(*orbits)==winners
    else:
        expected={0:p*(p-1)//2,2:p+1,4:p*(p+1)//2}
        assert not marked
    assert all_counts==Counter(expected)
    for w,n in [(-1,3),(-2,6)]:
        expected[4 if w%p in squares else 0]-=n
    assert simple_counts==Counter(expected)
    print("three",p,dict(sorted(all_counts.items())),dict(sorted(simple_counts.items())))

def four(p):
    u,v=next((u,v) for u in range(p) for v in range(p) if (u*u+v*v+1)%p==0)
    h2=pow(2,-1,p)
    e=(1,0,u,v);f=(0,1,-v,u)
    g=tuple(x*h2%p for x in (1,0,-u,-v))
    h=tuple(x*h2%p for x in (0,1,v,-u))
    def add(a,t,b):
        return tuple((x+t*y)%p for x,y in zip(a,b))
    lines=[(add(e,t,h),add(f,-t,g)) for t in range(p)]+[(g,h)]
    lines += [(add(e,t,f),add(h,-t,g)) for t in range(p)]+[(f,g)]
    counts=Counter()
    for a,b in lines:
        rays=[b]+[add(a,t,b) for t in range(p)]
        assert all(q(x)%p==0 and any(x) for x in rays)
        counts[sum(2*(depth(p,x,4)-2) for x in rays)]+=1
    # Separate chart enumeration of C: first nonzero coordinate is 1.
    yzs=Counter(((a*a+b*b)%p,(pow(a,4,p)+pow(b,4,p))%p)
                for a in range(p) for b in range(p))
    c=sum(yzs[((-1-a*a)%p,(-1-pow(a,4,p))%p)] for a in range(p))
    c+=yzs[(p-1,p-1)]
    c+=sum((1+a*a)%p==0 and (1+pow(a,4,p))%p==0 for a in range(p))
    k=12*(p%8==1)
    assert counts==Counter({0:2*(p+1)-k-c//2,8:c//2,16:k})
    print("four ",p,"C points",c,"distribution",dict(sorted(counts.items())))

if __name__=="__main__":
    for p in (7,11,13,17,19,23,29,31,37,41,73,97,103):
        three(p)
    for p in (11,13,17,23,29,31,41,47,53,73,83,89,97,149,193,509):
        four(p)
