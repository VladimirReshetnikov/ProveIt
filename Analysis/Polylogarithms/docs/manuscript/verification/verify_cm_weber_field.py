"""Independent standard-library replay of the degree-12 Weber witness."""
from pathlib import Path
import json
B=Path(__file__).resolve().parents[1]
p=5
def trim(a):
    while len(a)>1 and a[-1]==0:a.pop()
    return a
def sub(a,b):
    n=max(len(a),len(b));return trim([((a[i] if i<len(a) else 0)-(b[i] if i<len(b) else 0))%p for i in range(n)])
def mod(a,b):
    a=a[:];inv=pow(b[-1],-1,p)
    while a!=[0] and len(a)>=len(b):
        k=len(a)-len(b);c=a[-1]*inv%p
        for i,x in enumerate(b):a[k+i]=(a[k+i]-c*x)%p
        trim(a)
    return a
def mul(a,b,f):
    z=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):z[i+j]=(z[i+j]+x*y)%p
    return mod(trim(z),f)
def power(a,n,f):
    r=[1]
    while n:
        if n&1:r=mul(r,a,f)
        a=mul(a,a,f);n//=2
    return r
def gcd(a,b):
    while b!=[0]:a,b=b,mod(a,b)
    inv=pow(a[-1],-1,p);return [(x*inv)%p for x in a]
data=json.loads((B/'verification/CM-single-Weber.json').read_text())
w=data['weber39_irreducibility_witness'];assert w['prime']==p and w['degree']==12
f=list(reversed(w['coefficients']));x=[0,1];r=x;rows=[]
for j in range(1,13):
    r=power(r,p,f)
    if j in [4,6]:
        g=gcd(f,sub(r,x));assert g==[1]
        rows.append(dict(frobenius_power=j,gcd=g,residue=r))
assert r==x
out=dict(status='PASS',prime=p,degree=12,polynomial_ascending=f,
    proper_divisor_checks=rows,final_frobenius_residue=r,
    criterion='x^(5^12)=x modulo f; gcd(f,x^(5^6)-x)=gcd(f,x^(5^4)-x)=1',
    scope='Exact independent finite-field irreducibility certificate. CM field degrees use the written class-polynomial argument.')
(B/'verification/CM-Weber-independent.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out,indent=2))
