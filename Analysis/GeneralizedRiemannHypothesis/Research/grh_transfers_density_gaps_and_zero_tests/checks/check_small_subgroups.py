"""Check the exceptional subgroups that can improve the large-field formula."""
from fractions import Fraction
from math import gcd, isqrt


def phi(n):
    return sum(gcd(j,n) == 1 for j in range(1,n+1))


def mobius(n):
    if n == 1:
        return 1
    for p in range(2,n+1):
        if n % p == 0:
            return -mobius(n//p) if n % (p*p) else 0


def average_root(n, i):
    # Average of exp(2*pi*i*j/n) over primitive residues j.
    d = n // gcd(n,i)
    return Fraction(mobius(d),phi(d))


def h0(q):
    s = isqrt(q)
    if s*s == q:
        if s % 4 == 3:
            return q-s
        r = isqrt(s)
        if r*r == s:
            return q-q//r
    return (q+1)//2


def check(q, p, name, counts):
    a,b = (q-1)//2, (q+1)//2
    rows = [('trivial',1,0),('steinberg',q,0)]
    for n,side,degree in ((a,'split',q+1),(b,'nonsplit',q-1)):
        rows += [(side,degree,i) for i in range(1,(n+1)//2)]
        if n%2 == 0:
            rows += [(side+'-half',degree//2,sign*n//2) for sign in (1,-1)]
    assert len(rows) == (q+5)//2
    h = 1+sum(counts.values())
    fixed = []
    for row,deg,i in rows:
        acc = Fraction(deg)
        for order, number in counts.items():
            side = 'split' if a%order==0 else 'nonsplit'
            if row == 'trivial':
                val = 1
            elif order == p:
                assert q == 81 and name == 'A5' and order == 3
                if row.endswith('half'):
                    # All order-three elements of A5 are conjugate.
                    val = Fraction(1+(1 if i>0 else -1)*isqrt(q),2)
                else:
                    val = {'split':1,'nonsplit':-1,'steinberg':0}[row]
            elif row == 'steinberg':
                val = 1 if side=='split' else -1
            elif row.startswith(side):
                assert ((a if side=='split' else b) % order) == 0
                factor = 1 if row.endswith('half') else 2
                val = factor*average_root(order, i)*(1 if side=='split' else -1)
            else:
                val=0
            acc += number*val
        assert acc >= 0 and (acc/h).denominator == 1
        fixed.append(int(acc/h))
    print(f"q={q:3d} group={name} min_fixed={min(fixed)}")
    return min(fixed)>0


def verify():
    exceptions = {}
    for q in range(5,121,2):
        p=next(i for i in range(2,q+1) if q%i==0)
        k=q
        while k%p==0:
            k//=p
        if k!=1:
            continue
        base=h0(q)
        tests=[('A4',{2:3,3:8},True),('S4',{2:9,3:8,4:6},q%8 in (1,7)),
               ('A5',{2:15,3:20,5:24},q%5 in (0,1,4))]
        for name,counts,exists in tests:
            h=1+sum(counts.values())
            if exists and base<h<q-1 and check(q,p,name,counts):
                exceptions[q]=max(h,exceptions.get(q,0))
    print("Exceptional improvements:",exceptions)


if __name__ == '__main__':
    verify()
