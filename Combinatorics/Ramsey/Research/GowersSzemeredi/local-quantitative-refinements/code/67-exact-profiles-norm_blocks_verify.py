"""Exact certificates for norm-colouring obstructions. Python 3 standard library."""
from math import gcd, comb
from random import Random
import json
from pathlib import Path


def trim(a):
    while len(a)>1 and a[-1]==0: a.pop()
    return a

def rem(a,b,p):
    a=trim(a[:]);b=trim(b[:]); inv=pow(b[-1],-1,p)
    while len(a)>=len(b) and a!=[0]:
        c=a[-1]*inv%p;k=len(a)-len(b)
        for j in range(len(b)):a[j+k]=(a[j+k]-c*b[j])%p
        trim(a)
    return a

def mul(a,b,p):
    c=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):c[i+j]=(c[i+j]+x*y)%p
    return trim(c)

def power(a,n,f,p):
    r=[1]
    while n:
        if n&1:r=rem(mul(r,a,p),f,p)
        n//=2
        if n:a=rem(mul(a,a,p),f,p)
    return r

def sub(a,b,p):
    return trim([((a[i] if i<len(a) else 0)-(b[i] if i<len(b) else 0))%p for i in range(max(len(a),len(b)))])

def pgcd(a,b,p):
    while b!=[0]:a,b=b,rem(a,b,p)
    return [x*pow(a[-1],-1,p)%p for x in a]

def factors(n):
    result=[];t=2
    while t*t<=n:
        if n%t==0:
            result.append(t)
            while n%t==0:n//=t
        t+=1
    if n>1:result.append(n)
    return result

def irreducible(f,p):
    n=len(f)-1;h=[0,1];gcds={}
    targets={n//r for r in factors(n)}
    for j in range(1,n+1):
        h=power(h,p,f,p)
        if j in targets:
            r=pgcd(sub(h,[0,1],p),f,p)
            if r!=[1]:return False
            gcds[str(j)]=r
    return h==[0,1]

def eval_poly(a,t,p):
    v=0
    for x in reversed(a):v=(v*t+x)%p
    return v

def make_odd_kernel(m,p):
    a=[0,1]
    for j in range(1,m+1):a=mul(a,[-(2*j-1)**2%p,0,1],p)
    return a

def find_irred(m,p):
    g=make_odd_kernel(m,p);rng=Random(20261007+1000*m+p)
    trials=0
    # Prefer a constant even part: it certifies monochromatic progressions.
    for c in range(1,p):
        f=g[:];f[0]=c;trials+=1
        if irreducible(f,p):return f,trials,True
    for _ in range(10000):
        f=g[:]
        for j in range(m+1):f[2*j]=rng.randrange(p)
        trials+=1
        if irreducible(f,p):return f,trials,False
    raise RuntimeError((m,p))

def certificate(m,p):
    f,trials,monochromatic=find_irred(m,p)
    expected = {11:1,13:6,17:1,19:6,23:6,29:3,31:3,37:5,41:9,43:4,47:1}
    assert f[0] == expected[p] and all(f[i] == 0 for i in [2,4,6,8])
    h=[0,1];residues={};ben_or=[]
    for i in range(1,10):
        h=power(h,p,f,p)
        if i in [3,9]:residues[str(i)]=h[:]
        if i<=4:
            g=pgcd(sub(h,[0,1],p),f,p)
            assert g==[1]
            ben_or.append(g)
    assert residues['9']==[0,1]
    values=[]
    for j in range(1,m+1):
        u=2*j-1;a=eval_poly(f,u,p);b=eval_poly(f,-u,p)
        assert a==b and a!=0
        values.append(a)
    return dict(m=m,p=p,degree=len(f)-1,polynomial_ascending=f,
                even_coefficients=f[::2],node_values=values,
                irreducible=True,monochromatic=monochromatic,trials=trials,
                frobenius_remainders=residues,ben_or_gcds=ben_or)


def find_primitive(p,n):
    rng=Random(17+p+n); fac=factors(p**n-1)
    for attempt in range(10000):
        f=[rng.randrange(1,p)]+[rng.randrange(p) for _ in range(n-1)]+[1]
        if not irreducible(f,p):continue
        if all(power([0,1],(p**n-1)//r,f,p)!=[1] for r in fac):return f
    raise RuntimeError('primitive search exhausted')


def norm_table(f,p):
    n=len(f)-1;Q=p**n;top=p**(n-1)
    norm_x=(-f[0] if n%2 else f[0])%p
    table=[0]*Q;a=[1]+[0]*(n-1);norm=1
    for _ in range(Q-1):
        index=sum(v*p**j for j,v in enumerate(a))
        assert table[index]==0
        table[index]=norm
        c=a[-1];a=[0]+a[:-1]
        for j in range(n):a[j]=(a[j]-c*f[j])%p
        norm=norm*norm_x%p
    assert a==[1]+[0]*(n-1) and norm==1 and all(table[1:])
    # Independent modular-exponentiation validation on deterministic samples.
    rng=Random(771+n+p)
    for t in [0,1,2,Q-1]+[rng.randrange(Q) for _ in range(50)]:
        b=[];u=t
        for j in range(n):b.append(u%p);u//=p
        got=power(trim(b), (Q-1)//(p-1), f,p)
        assert got==[table[t]],(t,got,table[t])
    return table


def count_norms(p,n,ms):
    f=find_primitive(p,n);table=norm_table(f,p);Q=p**n
    out=[]
    for m in ms:
        count=0;witness=None
        for a in range(Q):
            base=a-a%p;r=a%p
            if all(table[base+(r+(2*j-1))%p]==table[base+(r-(2*j-1))%p] for j in range(1,m+1)):
                count+=1
                if witness is None:witness=a
        B=sum(comb(m,s)*(p-2)**s*(2*s-1) for s in range(2,m+1))
        D=2*m+m*(p-2)*(2*m-1)+sum(comb(m,s)*(p-2)**s*2*(m-s) for s in range(2,m+1))
        # Check |(p-1)^m count -(Q-2m)| <= exact single bound+Weil bound:
        delta=abs((p-1)**m*count-(Q-2*m))
        extra=D-2*m
        assert max(0,delta-extra)**2<=B*B*Q
        if n%2 and n<2*m: assert count==0
        if (m in [2,3] and n%2 and n>=2*m+1): assert count>0
        coeff=[]
        if witness is not None:
            u=witness
            for _ in range(n):coeff.append(u%p);u//=p
        out.append(dict(p=p,degree=n,m=m,field_polynomial_ascending=f,
            ratio_count=count,ordered_nontrivial_APs=(Q-1)*count,
            first_witness_ascending=coeff,
            witness_norm_values=[] if witness is None else [[table[witness-witness%p+(witness%p+(2*j-1))%p],table[witness-witness%p+(witness%p-(2*j-1))%p]] for j in range(1,m+1)]))
    return out


def main():
    import argparse
    parser=argparse.ArgumentParser();parser.add_argument('--full',action='store_true')
    parser.add_argument('--output',type=Path,default=Path(__file__).resolve().parents[1]/'data'/'norm_blocks_verification.json')
    args=parser.parse_args()
    critical=[certificate(4,p) for p in [11,13,17,19,23,29,31,37,41,43,47]]
    numerical=[]
    if args.full:
        for p,n,ms in [(5,3,[2]),(5,4,[2]),(5,5,[2]),(7,3,[2,3]),(7,5,[2,3]),(11,5,[2,3]),(7,7,[2,3])]:
            numerical.extend(count_norms(p,n,ms))
    result={'method':'Exact polynomial arithmetic over prime fields; Rabin irreducibility; exhaustive norm tables when --full. No floating-point claims.', 'critical_degree_nine_certificates':critical,'norm_counts':numerical}
    target=args.output;target.parent.mkdir(parents=True,exist_ok=True)
    target.write_text(json.dumps(result,indent=2)+'\n')
    print('Verified 11 exact degree-nine irreducibility certificates and',len(numerical),'exhaustive norm-count cases.')
    print('Report:',target)

if __name__=='__main__':main()
