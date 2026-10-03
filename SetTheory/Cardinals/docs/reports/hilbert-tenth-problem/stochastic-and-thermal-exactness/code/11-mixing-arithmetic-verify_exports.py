"""Independent exact audit of exported examples.

Matrix arithmetic and elimination use only Python's Fraction. This program does
not import the compiler or SymPy. Finite checks are evidence, not replacements
for the proofs in article.tex.
"""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parents[1]

def matrix(rows):
    return tuple(tuple(F(v) for v in row) for row in rows)

def identity(n):
    return tuple(tuple(F(i == j) for j in range(n)) for i in range(n))

def mul(A, B):
    BT = tuple(zip(*B))
    return tuple(tuple(sum((a*b for a,b in zip(row,col)), F(0))
                       for col in BT) for row in A)

def add(A, B):
    return tuple(tuple(a+b for a,b in zip(ar,br)) for ar,br in zip(A,B))

def scale(c, A):
    return tuple(tuple(c*a for a in row) for row in A)

def sub(A, B):
    return add(A,scale(-1,B))

def power(A, e):
    R = identity(len(A))
    while e:
        if e & 1:
            R = mul(R,A)
        A=mul(A,A)
        e//=2
    return R

def zero(A):
    return all(v == 0 for row in A for v in row)

def rank(A):
    B=[list(row) for row in A]
    if not B:
        return 0
    r=0
    for c in range(len(B[0])):
        j=next((j for j in range(r,len(B)) if B[j][c]),None)
        if j is None:
            continue
        B[r],B[j]=B[j],B[r]
        pivot=B[r][c]
        B[r]=[a/pivot for a in B[r]]
        for j in range(r+1,len(B)):
            t=B[j][c]
            if t:
                B[j]=[a-t*b for a,b in zip(B[j],B[r])]
        r+=1
        if r==len(B):
            break
    return r

def indices(k,d):
    if k==1:
        return [(i,) for i in range(d+1)]
    return [(i,)+tail for i in range(d+1) for tail in indices(k-1,d-i)]

def value(terms, n):
    return sum((F(t['coefficient']) * prod(nj**aj for nj,aj in
                  zip(n,t['exponents'])) for t in terms), F(0))

def prod(values):
    out=1
    for x in values:
        out*=x
    return out

def word_distribution(p, matrices, word):
    row=(p,)
    for letter in word:
        row=mul(row,matrices[letter])
    return row[0]

report=[]
family_matrices={}
family_initials={}
root_hits={"factor_family_6":[],"factor_line_6":[]}
for path in sorted((ROOT/'examples').glob('*.json')):
    data=json.loads(path.read_text())
    s=data['states']; r=data['translation_rank']; d=data['degree']
    k=len(data['variables']); theta=F(data['theta']); q=F(data['q'])
    eps=F(data['epsilon']); terms=data['polynomial_terms']
    Ms=tuple(matrix(M) for M in data['transitions'])
    As=tuple(matrix(A) for A in data['shifts'])
    E=matrix(data['E']); G=matrix(data['F']); p=tuple(map(F,data['initial']))
    u=tuple(F(1,s) for _ in range(s)); J=tuple(u for _ in range(s))
    assert s==r+1 and len(Ms)==k and sum(p)==1 and min(p)>0
    assert mul(E,G)==identity(r)
    assert mul(G,E)==sub(identity(s),J)
    for M,A in zip(Ms,As):
        assert all(sum(row)==1 for row in M)
        assert all(sum(col)==1 for col in zip(*M))
        assert all((1-theta)/s < a < (1+theta)/s for row in M for a in row)
        assert M==add(J,scale(q,mul(mul(G,A),E)))
        assert rank(M)==s
        assert zero(power(sub(A,identity(r)),d+1))
    for i in range(k):
        for j in range(i):
            assert mul(Ms[i],Ms[j])==mul(Ms[j],Ms[i])
    Ns=tuple(sub(A,identity(r)) for A in As)
    npowers=[[power(N,j) for j in range(d+2)] for N in Ns]
    nil_checks=0; depth_witness=False
    for alpha in indices(k,d+1):
        if sum(alpha) not in (d,d+1):
            continue
        B=identity(r)
        for i,a in enumerate(alpha):
            B=mul(B,npowers[i][a])
        if sum(alpha)==d+1:
            assert zero(B)
            nil_checks+=1
        elif not zero(B):
            depth_witness=True
    assert depth_witness
    # Joint-module minimality can differ from individual polynomial minimality.
    grid=indices(k,d)
    H=tuple(tuple(value(terms,tuple(a+b for a,b in zip(m,n))) for n in grid)
            for m in grid)
    hankel_rank=rank(H)
    assert hankel_rank<=r
    if not data['name'].startswith('factor_family'):
        assert hankel_rank==r
    maxcount=6 if data['name'] in root_hits else 3
    mpowers=[[power(M,j) for j in range(maxcount+1)] for M in Ms]
    count_checks=0
    for counts in product(range(maxcount+1), repeat=k):
        row=(p,)
        for i,n in enumerate(counts):
            row=mul(row,mpowers[i][n])
        P=value(terms,counts)
        assert row[0][0] == F(1,s)+eps*q**sum(counts)*P
        assert (row[0][0]==F(1,s)) == (P==0)
        assert sum(row[0])==1 and min(row[0])>0
        assert sum(abs(a-b) for a,b in zip(row[0],u))/2 <= theta**sum(counts)
        if p!=u:
            assert row[0]!=u
        if data['name'] in root_hits and P==0:
            root_hits[data['name']].append(list(counts))
        count_checks+=1
    word_checks=0
    # Arbitrary order, including the empty word, not just canonical block words.
    for L in range(5):
        for word in product(range(k),repeat=L):
            row=word_distribution(p,Ms,word)
            counts=tuple(word.count(i) for i in range(k))
            assert row[0]==F(1,s)+eps*q**L*value(terms,counts)
            word_checks+=1
    # Contraction tested on all pairs of pure states for every generator.
    for M in Ms:
        for i in range(s):
            for j in range(i):
                assert sum(abs(a-b) for a,b in zip(M[i],M[j]))/2 <= theta
    if data['name'].startswith('factor_'):
        key=data['name'].rsplit('_',1)[0]
        t=int(data['name'].rsplit('_',1)[1])
        if key not in family_matrices:
            family_matrices[key]=Ms
            family_initials[key]={}
        assert Ms==family_matrices[key]
        family_initials[key][t]=p
    report.append(dict(name=data['name'],states=s,translation_rank=r,
                       independently_computed_hankel_rank=hankel_rank,
                       count_vectors_checked=count_checks,words_checked=word_checks,
                       degree_plus_one_nilpotence_checks=nil_checks))
for hits in root_hits.values():
    assert sorted(hits)==[[1,6,6],[2,3,6],[3,2,6],[6,1,6]]
# Independently recover the two fixed endpoints of the line loader.
pts=family_initials['factor_line']
p0=pts[0]; p1=tuple(2*b-a for a,b in zip(pts[0],pts[1]))
assert min(p0)>0 and min(p1)>0 and sum(p0)==sum(p1)==1
for t,p in pts.items():
    assert p==tuple((a+t*b)/(1+t) for a,b in zip(p0,p1))
# Recover the quadratic numerator from t=0,1,2 and check all other inputs.
pts=family_initials['factor_family']
c0=pts[0]
c2=tuple((9*c-8*b+a)/2 for a,b,c in zip(pts[0],pts[1],pts[2]))
c1=tuple(4*b-a-c for a,b,c in zip(pts[0],pts[1],c2))
for t,p in pts.items():
    assert p==tuple((a+t*b+t*t*c)/(1+t)**2 for a,b,c in zip(c0,c1,c2))
assert all(min(pt)>0 and sum(pt)==1 for pt in [c0,tuple(a/2 for a in c1),c2])
result={'arithmetic':'Python fractions.Fraction; no compiler or SymPy import',
        'examples':report,'total_count_vectors':sum(x['count_vectors_checked'] for x in report),
        'total_words':sum(x['words_checked'] for x in report),
        'factor_six_roots_in_box':root_hits,
        'fixed_family_transition_identity':True,
        'linear_and_quadratic_input_curve_checks':True,
        'status':'all checks passed'}
(ROOT/'verification'/'independent_report.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
