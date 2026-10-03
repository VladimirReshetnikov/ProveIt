from random import Random
from math import comb
from pathlib import Path
import json

def counts(rows,u,v):
    n=len(v);wp=[1]*(1<<n)
    for J in range(1,1<<n):
        bit=J&-J;wp[J]=wp[J-bit]*v[bit.bit_length()-1]
    out=[0]*(min(len(rows),n)+1)
    for I in range(1<<len(rows)):
        k=I.bit_count();w=1;reach={0}
        for i,row in enumerate(rows):
            if I>>i&1:
                w*=u[i];reach={J|(1<<j)for J in reach for j in range(n)if row>>j&1 and not J>>j&1}
                if not reach:break
        if k<len(out):out[k]+=w*sum(wp[J]for J in reach)
    return trim(out)
def trim(p):
    while len(p)>1 and p[-1]==0:p.pop()
    return p
def add(a,b):return trim([(a[i]if i<len(a)else 0)+(b[i]if i<len(b)else 0)for i in range(max(len(a),len(b)))])
def mul(a,b):
    p=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):p[i+j]+=x*y
    return trim(p)
def sub(a,b):return add(a,[-x for x in b])

def one_root(rows,v,root,k,T):
    p=counts(rows,[1]*len(rows),v)
    f=counts(rows[:root]+rows[root+1:],[1]*(len(rows)-1),v);g=sub(p,f)
    n=len(v);newrows=rows[:];newrows[root]|=sum(1<<(n+i)for i in range(k))
    newrows += [1<<(n+i)for i in range(k)]
    actual=counts(newrows,[1]*len(newrows),v+[T]*k)
    common=[comb(k-1,i)*T**i for i in range(k)]
    expected=mul(common,add(mul([1,(k+1)*T],f),mul([1,T],g)))
    assert actual==expected,(rows,v,root,k,T,actual,expected)

rng=Random(372071)
for _ in range(150):
    n=rng.randrange(1,4);m=rng.randrange(1,4)
    rows=[rng.randrange(1<<n)for _ in range(m)];v=[rng.randrange(1,7)for _ in range(n)]
    one_root(rows,v,rng.randrange(m),rng.randrange(1,4),rng.randrange(1,8))
out={'seed':372071,'independent_exact_support_checks':150,'all_gadget_identities_verified':True}
Path(__file__).with_name('gadget_identity_verification.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
