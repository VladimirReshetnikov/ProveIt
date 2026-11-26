#!/usr/bin/env python3
"""Exact, dependency-free verification of the A6 character identities.
Composition is right-to-left; permutations act on {1,...,6}.
The Gaussian-integer encoding is a power of i (mod 4).
"""
from itertools import permutations
from collections import Counter
from fractions import Fraction
import json

N=6
E=tuple(range(1,N+1))

def cyc(*cycles):
    p=list(E)
    for c in cycles:
        for a,b in zip(c,c[1:]+c[:1]): p[a-1]=b
    return tuple(p)

def mul(p,q): return tuple(p[a-1] for a in q)

def inv(p): return tuple(p.index(a)+1 for a in E)

def parity(p): return sum(p[i]>p[j] for i in range(N) for j in range(i+1,N))%2

def typ(p):
    seen=set(); lengths=[]
    for a in E:
        if a in seen: continue
        k=0; b=a
        while b not in seen: seen.add(b); k+=1; b=p[b-1]
        lengths.append(k)
    return tuple(sorted(lengths))

G=tuple(p for p in permutations(E) if not parity(p))
assert len(G)==360
TYPES=((1,1,1,1,1,1),(1,1,1,3),(1,1,2,2),(1,5),(2,4),(3,3))
SIZE=tuple(Counter(map(typ,G))[t] for t in TYPES)
assert SIZE==(1,40,45,144,90,40)

# A homomorphism into the fourth roots of unity, specified on generators.
def subgroup(gens):
    values={E:0}; queue=[E]
    for a in queue:
        for g,k in gens:
            b=mul(a,g); j=(values[a]+k)%4
            if b in values: assert values[b]==j, 'inconsistent character'
            else: values[b]=j;queue.append(b)
    assert all(not parity(g) for g in values)
    # Independently check closure and multiplicativity.
    for a,k in values.items():
        for b,j in values.items(): assert values[mul(a,b)]==(k+j)%4
    return values

I=((1,0),(0,1),(-1,0),(0,-1))

def induced(gens, size, expected):
    H=subgroup(gens); assert len(H)==size
    out={}
    for g in G:
        re=im=0
        for x in G:
            h=mul(mul(inv(x),g),x)
            if h in H:
                a,b=I[H[h]];re+=a;im+=b
        assert re%size==0 and im==0
        out[g]=re//size
    row=[]
    for t in TYPES:
        vals={v for g,v in out.items() if typ(g)==t}
        assert len(vals)==1
        row.append(vals.pop())
    assert tuple(row)==expected,(row,expected)
    return tuple(row)

# V4: disjoint pairs on 6 letters. D8: r=(1234)(56), s=(24)(56).
v1=cyc((3,4),(5,6));v2=cyc((1,2),(5,6))
r=cyc((1,2,3,4),(5,6));s=cyc((2,4),(5,6))
a=cyc((1,2,3));b=cyc((4,5,6));t=cyc((1,4),(2,5,3,6))
c=cyc((1,2,3,4,5));d=cyc((2,5),(3,4))

specs={
 'W': ([(v1,0),(v2,2)],4,(90,0,-2,0,0,0)),
 'Y': ([(r,2),(s,0)],8,(45,0,1,0,-1,0)),
 'P': ([(v1,0),(v2,0)],4,(90,0,6,0,0,0)),
 'U': ([(a,0),(b,0),(t,1)],36,(10,1,-2,0,0,1)),
 'A': ([(a,0),(b,0),(t,2)],36,(10,1,2,0,-2,1)),
 'V': ([(c,0),(d,2)],10,(36,0,-4,1,0,0)),
 'B': ([(c,0),(d,0)],10,(36,0,4,1,0,0)),
 'Z': ([(r,0),(s,2)],8,(45,0,-3,0,1,0)),
 'C': ([(r,0),(s,0)],8,(45,0,5,0,1,0)),
}
rows={name:induced(*spec) for name,spec in specs.items()}
rows['1']=(1,)*6;rows['reg']=(360,0,0,0,0,0)

def comb(d):return tuple(sum(k*rows[n][i] for n,k in d.items()) for i in range(6))
assert comb({'W':5,'1':1})==comb({'reg':1,'U':1,'V':1,'Z':1})
assert comb({'Y':12,'1':4})==comb({'reg':1,'A':4,'V':1,'B':3})
assert comb({'P':10,'1':3})==comb({'reg':1,'A':3,'B':3,'C':9})

def inner(u,v):return Fraction(sum(n*a*b for n,a,b in zip(SIZE,u,v)),360)
assert inner(rows['Y'],rows['Y'])==6
assert inner(rows['Y'],rows['1'])==0
assert inner(rows['U'],rows['U'])==1
assert comb({'P':1,'W':-1})==(0,0,8,0,0,0)
assert inner(comb({'P':1,'W':-1}),rows['U'])==-2
# Any integer-valued, mean-zero, two-pattern detector has degree >=45.
# For a second pattern of size m, d must be a multiple of m and norm^2 integral.
small=[]
for m in SIZE[1:]:
    for deg in range(45,90):
        if deg%m==0:
            norm=Fraction(deg*deg+m*(deg//m)**2,360)
            small.append((m,deg,str(norm)));assert norm.denominator!=1
assert min(deg for deg in range(45,361) if deg%45==0 and Fraction(deg*deg+45*(deg//45)**2,360).denominator==1)==90
std=tuple(t.count(1)-1 for t in TYPES)
assert inner(std,std)==1 and inner(std,rows['W'])==1 and std[0]==5
# Count all conjugacy classes directly (no reliance on split-class rule).
remaining=set(G); classes=[]
while remaining:
    g=min(remaining); conj={mul(mul(x,g),inv(x)) for x in G}
    assert conj<=remaining;remaining-=conj;classes.append((typ(g),len(conj)))
assert len(classes)==7
assert sorted(n for t,n in classes if t==(1,5))==[72,72]
for name in specs:
    print(f'{name:>3}  |H|={specs[name][1]:>2}  values={rows[name]}  mean={inner(rows[name],rows["1"])}')
print('All three identities checked on every element of A6.')
print('Y norm squared = 6; seven classes, including two 5-cycle classes.')
print('No integer-valued mean-zero two-pattern detector with degree 45..89:',small)
print('U is irreducible, and P-W has coefficient -2 against U.')
print('W sharpness witness: standard irreducible degree 5, W multiplicity 1.')
with open('character_certificate.json','w') as f:
    json.dump({'cycle_types':TYPES,'class_sizes_merged':SIZE,'conjugacy_classes':classes,'rows':rows,'identities':['5W+1=reg+U+V+Z','12Y+4=reg+4A+V+3B','10P+3=reg+3A+3B+9C']},f,indent=2)
