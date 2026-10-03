"""Independent checks: coefficient-array DP, direct graph orientations, and AD quadrature.
Does not import or execute the submission's calculation scripts.
"""
from pathlib import Path
import json, math, hashlib, itertools
import sympy as sy
import mpmath as mp
ROOT=Path(__file__).resolve().parents[1]
OUT={}
# Exact bivariate polynomials, with no Kronecker encoding.
N=40
Q=[[1]]
for k in range(1,N+1):
    prev=Q[-1]
    Q.append([0]+[j*(prev[j] if j<len(prev) else 0)+prev[j-1] for j in range(1,k+1)])
def conv(a,b):
    c=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):c[i+j]+=x*y
    return c
values={}
for distinct in (False,True):
    dp=[[0]*(n+1) for n in range(N+1)];dp[0]=[1]
    for k in range(1,N+1):
        for n in (range(N,k-1,-1) if distinct else range(k,N+1)):
            term=conv(dp[n-k],Q[k])
            for j,v in enumerate(term):dp[n][j]+=v
    vals=[sum((-1)**(n-j)*math.factorial(j)*v for j,v in enumerate(row)) for n,row in enumerate(dp)]
    label='distinct' if distinct else 'unrestricted'
    expected=json.loads((ROOT/'exact_values_150.json').read_text())[label]
    assert vals==[int(v) for v in expected[:N+1]]
    values[label]=vals
OUT['array_dp_all_values_match_through']=N
# Brute force all orientations on each complete multipartite graph up to n=6.
def parts(n, lo=1):
    if not n:yield ()
    for k in range(lo,n+1):
        for rest in parts(n-k,k):yield (k,)+rest
brute_counts={}
for n in range(7):
    sums=[0,0]
    for lam in parts(n):
        groups=[i for i,k in enumerate(lam) for _ in range(k)]
        edges=[(i,j) for i in range(n) for j in range(i+1,n) if groups[i]!=groups[j]]
        cnt=0
        for mask in range(1<<len(edges)):
            indeg=[0]*n;adj=[[] for _ in range(n)]
            for p,(i,j) in enumerate(edges):
                if mask>>p&1:i,j=j,i
                adj[i].append(j);indeg[j]+=1
            stack=[i for i in range(n) if not indeg[i]];seen=0
            while stack:
                i=stack.pop();seen+=1
                for j in adj[i]:
                    indeg[j]-=1
                    if not indeg[j]:stack.append(j)
            cnt+=(seen==n)
        sums[0]+=cnt
        if len(set(lam))==len(lam):sums[1]+=cnt
    assert sums==[values['unrestricted'][n],values['distinct'][n]]
    brute_counts[n]=sums
OUT['direct_orientation_enumeration']=brute_counts
# Newton sums from the exact signed Stirling polynomials, checked against R-polys.
k,u,t,x,z,e=sy.symbols('k u t x z e')
p={}
for r in range(1,7):
    v=k*u+sum(p[j]*u**(j+1) for j in range(1,r))
    delta=sy.expand(r*sum(v**a/sy.Integer(a) for a in range(1,r+1))).coeff(u,r)
    h=sy.symbols('h',integer=True)
    p[r]=sy.factor(sy.summation(delta.subs(k,h),(h,0,k-1)))
for K in range(1,13):
    signed=sum((-1)**(K-j)*v*t**j for j,v in enumerate(Q[K]))
    series=sy.series(signed.subs(t,1/u)*u**K,u,0,7).removeO()
    logseries=sy.series(sy.log(series),u,0,7).removeO().expand()
    for r in range(1,7):assert sy.simplify(-r*logseries.coeff(u,r)-p[r].subs(k,K))==0
OUT['root_power_polynomials']={str(r):str(v) for r,v in p.items()}
print('Exact checks passed',flush=True)
# Independent first correction using automatic differentiation rather than the
# submitted explicit cumulant and coefficient formula implementation.
mp.mp.dps=40
num={}
for eta in (1,-1):
    rho=lambda X,C: 1/mp.expm1(C*X+X*X/2) if eta==1 else 1/(mp.exp(C*X+X*X/2)+1)
    quad=lambda f:mp.quad(f,[0,1,mp.inf])
    M=lambda j,C:quad(lambda X:X**j*rho(X,C))
    c=mp.findroot(lambda C:M(1,C)-1,mp.mpf('.765') if eta==1 else mp.mpf('-.324'))
    f0=lambda X,C: -mp.log(-mp.expm1(-C*X-X*X/2)) if eta==1 else mp.log1p(mp.exp(-C*X-X*X/2))
    J=lambda C:quad(lambda X:f0(X,C))
    Jd={r:quad(lambda X:mp.diff(lambda C:f0(X,C),c,r)) for r in range(2,5)}
    H0=lambda C,Z:M(1,C)/2+Z*M(2,C)/2-M(3,C)/3
    d=lambda C:mp.log(C/(2*mp.pi))/2 if eta==1 else -mp.log(2)/2
    alpha=M(2,c)/2;V=Jd[2]
    # Direct ell1,ell2 feed the formal Taylor coefficient integral f2.
    ell1=lambda X,Z:X/2+Z*X**2/2-X**3/3
    ell2=lambda X,Z:-Z*X/2-Z**2*X**2/2+2*Z*X**3/3+3*X**2/4-3*X**4/8
    def h1(Z):
        f2=lambda X:rho(X,c)*ell2(X,Z)+rho(X,c)*(1+eta*rho(X,c))*ell1(X,Z)**2/2
        E1=(1/c-c)/24 if eta==1 else c/24
        boundary=-1/(4*c) if eta==1 else 0
        return quad(f2)+E1+boundary
    def D(Z):
        # Derivatives of log A computed by automatic differentiation under x-integrals.
        h0_integrand=lambda X,C:rho(X,C)*(X/2+Z*X**2/2-X**3/3)
        ld1=mp.diff(d,c)+quad(lambda X:mp.diff(lambda C:h0_integrand(X,C),c))
        ld2=mp.diff(d,c,2)+quad(lambda X:mp.diff(lambda C:h0_integrand(X,C),c,2))
        return -(ld2+ld1**2)/(2*V)+Jd[3]*ld1/(2*V**2)+Jd[4]/(8*V**2)-5*Jd[3]**2/(24*V**3)
    # Three values determine the quadratic; E polynomial directly.
    vals=[h1(Z)+D(Z) for Z in (-1,0,1)]
    a0=vals[1];a1=(vals[2]-vals[0])/2;a2=(vals[2]+vals[0])/2-vals[1]
    correction=a0+a1*alpha+a2*(1+alpha**2)+(alpha**3+3*alpha)/3
    C=c+J(c);EE=mp.exp(mp.mpf('.5')-M(3,c)/3+M(2,c)**2/8)
    A=mp.sqrt(c)*EE/(2*mp.pi*mp.sqrt(V)) if eta==1 else EE/(2*mp.sqrt(mp.pi*V))
    label='unrestricted' if eta==1 else 'distinct'
    expected=mp.mpf(json.loads((ROOT/'first_correction.json').read_text())[label]['a1'])
    assert abs(correction-expected)<mp.mpf('1e-34')
    num[label]={key:mp.nstr(val,39) for key,val in {'c':c,'C':C,'A':A,'a1':correction,'a1_difference':correction-expected}.items()}
    print(label,num[label],flush=True)
OUT['independent_quadrature']=num
OUT['inputs_sha256']={name:hashlib.sha256((ROOT/name).read_bytes()).hexdigest() for name in ['proof.md','first_correction.py','first_correction.json','exact_check.py','exact_values_150.json']}
Path(__file__).with_suffix('.json').write_text(json.dumps(OUT,indent=2))
print('All independent checks passed',flush=True)
