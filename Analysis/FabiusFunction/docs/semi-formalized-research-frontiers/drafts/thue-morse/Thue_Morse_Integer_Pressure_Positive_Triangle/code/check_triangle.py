"""Exact response and pressure triangles, with independent phase-jet checks."""
from pathlib import Path
import json
import sympy as s
ROOT=Path(__file__).resolve().parents[1]
DATA=ROOT/'data'

def R(k):
    return (-1)**(k+1)*2**(2*k)*(2**(2*k)-1)*s.bernoulli(2*k)/s.factorial(2*k)

def matrix_jets(m,N,normalized):
    ix=list(range(1-m,m));d=len(ix)
    def base(k,r):
        j=2*k-r
        return 2*s.Rational(s.binomial(2*m,m+j),4**m) if abs(j)<=m else s.S.Zero
    V=s.Matrix(d,d,lambda k,r:base(ix[k],ix[r]))
    matrices=[]
    for n in range(N+1):
        def entry(k,r):
            j=2*ix[k]-ix[r]
            if abs(j)>m:return s.S.Zero
            if normalized:
                q=sum((-1)**h*s.binomial(m+j,h)*s.binomial(m-j,n-h)for h in range(n+1))
            else:q=s.Rational((-2*j)**n,s.factorial(n))
            return V[k,r]*q
        matrices.append(s.Matrix(d,d,entry))
    A=s.eye(d)-V;C=A.copy();C[0,:]=s.ones(1,d);inv=C.inv()
    rhs=s.zeros(d,1);rhs[0]=1
    vectors=[inv*rhs];eigen=[s.S.One]
    assert A*vectors[0]==s.zeros(d,1) and sum(vectors[0])==1
    for n in range(1,N+1):
        b=sum((matrices[j]*vectors[n-j]for j in range(1,n+1)),s.zeros(d,1))
        eigen.append(sum(b))
        target=b-sum((eigen[j]*vectors[n-j]for j in range(1,n+1)),s.zeros(d,1))
        assert sum(target)==0
        rhs=target.copy();rhs[0]=0;vn=inv*rhs
        assert A*vn==target and sum(vn)==0
        vectors.append(vn)
    return ix,vectors,eigen

def mul(a,b,N):
    c=[s.S.Zero]*(N+1)
    for i,x in enumerate(a):
        for j,y in enumerate(b[:N+1-i]):c[i+j]+=x*y
    return c

def tan_relative_power(power,N):
    f=[R(j+1)for j in range(N+1)];out=[s.S.One]+[s.S.Zero]*N
    for _ in range(power):out=mul(out,f,N)
    return out

def pressure_from_responses(m,H):
    out=[]
    for r in range(1,m):
        value=sum(H[j]*tan_relative_power(2*m+2*j,r-j)[r-j]for j in range(r+1))
        value-=s.Rational(m,m+r)*R(m+r)
        out.append(s.factor(value))
    return out

def direct_pressure(m,N):
    _,_,eigen=matrix_jets(m,N,False)
    assert all(eigen[n]==0 for n in range(1,N+1,2))
    lam=[eigen[n]*(-1)**(n//2)if n%2==0 else s.S.Zero for n in range(N+1)]
    p=[s.S.Zero]
    for n in range(1,N+1):
        p.append(s.factor(lam[n]-sum(k*p[k]*lam[n-k]for k in range(1,n))/n))
    assert p[2*m]==0
    return p

def main():
    reference={row['m']:row['responses']for row in json.loads((DATA/'response_triangle_reference.json').read_text())['rows']}
    rows=[];count=0;pressure_count=0
    for m in range(2,15):
        ix,h,lam=matrix_jets(m,2*m-2,True)
        assert all(x==0 for x in lam[1:])
        H=[R(m)]+[s.factor((-1)**r*sum((-1)**abs(k)*h[2*r][j]for j,k in enumerate(ix)))for r in range(1,m)]
        assert list(map(str,H[1:]))==reference[m]
        E=pressure_from_responses(m,H)
        assert all(v>0 for v in H+E)
        direct_checked=False
        if m<=8:
            p=direct_pressure(m,4*m-2)
            assert E==[p[2*m+2*r]for r in range(1,m)]
            direct_checked=True;pressure_count+=m-1
        rows.append({'m':m,'responses':list(map(str,H[1:])),'pressure_coefficients':list(map(str,E)),'independent_phase_comparison':direct_checked})
        count+=m-1
        print('m',m,'exact response and pressure signs pass',flush=True)
    result={'all_checks_passed':True,'exact_response_pairs':count,'exact_pressure_pairs':count,'independent_direct_pressure_pairs':pressure_count,'scope':'Finite regressions; universal proof is the tangent-majorization argument','rows':rows}
    (DATA/'triangle_checks.json').write_text(json.dumps(result,indent=2)+'\n')
    print('PASS:',count,'exact response and pressure pairs;',pressure_count,'independent direct pressure comparisons')
if __name__=='__main__':main()
