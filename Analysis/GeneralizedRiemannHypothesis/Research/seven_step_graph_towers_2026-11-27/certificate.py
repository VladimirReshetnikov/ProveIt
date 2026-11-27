"""Exact seven-step norm certificate (standard library only)."""
from collections import Counter
from itertools import permutations, product

def determinant(a):
    a=[row[:] for row in a]
    prev=sgn=1
    for k in range(len(a)-1):
        i=next((i for i in range(k,len(a)) if a[i][k]),None)
        if i is None:
            return 0
        if i!=k:
            a[k],a[i]=a[i],a[k]
            sgn=-sgn
        d=a[k][k]
        for i in range(k+1,len(a)):
            for j in range(k+1,len(a)):
                a[i][j],r=divmod(d*a[i][j]-a[i][k]*a[k][j],prev)
                assert r==0
            a[i][k]=0
        prev=d
    return sgn*a[-1][-1]

def norm(f):
    return abs(determinant([[f[(i-j)%7]-f[(6-j)%7] for j in range(6)]
                            for i in range(6)]))

def norm_product(f):
    # Product over the six conjugates, using Z^7=1 first.
    a=[1,0,0,0,0,0,0]
    for j in range(1,7):
        b=[0]*7
        for i,x in enumerate(a):
            for k,y in enumerate(f):
                b[(i+j*k)%7]+=x*y
        a=b
    assert a[1:]==[a[6]]*6
    return abs(a[0]-a[6])

def both(f):
    a=norm(f)
    assert a==norm_product(f)
    return a

def moments(p,S,a,b):
    return [sum(pow(a*x+b*y,2*j,p) for x,y in S)%p for j in range(1,8)]

def exceptional(p,S):
    out=[]
    for a,b in [(1,t) for t in range(p)]+[(0,1)]:
        ms=moments(p,S,a,b)
        assert ms[:2]==[0,0]
        r=next(j for j,v in enumerate(ms,1) if v)
        if r>3:
            out.append((a,b,r))
    return out

def main():
    perms=[(0,)+s for s in permutations(range(1,7))]
    signs=[(1,)+s for s in product((1,-1),repeat=6)]
    def coeff(s):
        return [sum((i+b)%7==j for i,b in enumerate(s)) for j in range(7)]
    tally=Counter(both(coeff(s)) for s in perms)
    assert tally=={0:19,49:441,343:42,392:126,2744:28,3479:42,8281:21,117649:1}
    print("Unsigned permutation norms:", sorted(tally.items()))
    signed=Counter(both(s) for s in signs)
    assert signed=={0:1,64:49,512:14} and norm([1]*7)==0
    print("Sign-vector norms:", sorted(signed.items()))
    exponents=[s for s in perms if all(len({(a*i+b*j)%7 for i,j in enumerate(s)})==7
                                          for a,b in [(1,1),(3,1),(1,3)])]
    assert set(exponents)=={tuple(k*i%7 for i in range(7)) for k in [1,3,5]}
    print("Permutations surviving all three exponent tests:", exponents)
    p,z=71,20
    assert pow(z,7,p)==1 and z!=1
    roots=[pow(z,i,p) for i in range(7)]
    cases=[]
    for s in perms:
        for eps in signs:
            S=tuple((roots[i],eps[i]*roots[s[i]]%p) for i in range(7))
            if all(x==y for x,y in S):
                continue
            if any(sum(x*y for x,y in terms)%p for terms in
                   [[(x**a,y**b) for x,y in S] for a,b in [(1,1),(3,1),(2,2),(1,3)]]):
                continue
            assert exceptional(p,S)==[(1,0,7),(0,1,7)]
            cases.append((s,eps))
    assert set(cases)=={(tuple(k*i%7 for i in range(7)),(1,)*7) for k in [3,5]}
    print("Survivors at p=71:",cases)
    S=((1,0),(0,1),(2,3),(6,2),(10,24),(11,21),(12,10))
    ex=exceptional(29,S)
    assert 6*30+sum(2*(r-3) for _,_,r in ex)==196
    print("p=29 witness exceptional directions:",ex)

    # Verify every simple witness independently of the search's scoring loop.
    witnesses={
        17:(82,((0,2),(0,7),(2,2),(4,14),(8,1))),
        19:(94,((0,7),(1,2),(2,5),(5,12),(8,10))),
        23:(104,((0,2),(0,3),(0,5),(4,21),(11,7))),
        29:(196,((2,3),(6,2),(10,24),(11,21),(12,10))),
        31:(140,((0,2),(1,4),(3,19),(7,19),(8,30))),
    }
    for p,(val,tail) in witnesses.items():
        S=((1,0),(0,1))+tail
        assert (0,0) not in S
        assert len({min((x,y),(-x%p,-y%p)) for x,y in S})==7
        ds=[next(i for i,n in enumerate(moments(p,S,a,b),1) if n)
            for a,b in [(1,t) for t in range(p)]+[(0,1)]]
        assert 2*sum(ds)==val
    print("All five simple maximizing witnesses independently scored.")

if __name__=="__main__":
    main()
