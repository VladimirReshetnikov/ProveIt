"""Original exact experiments, no downloaded code execution."""
from fractions import Fraction as Q
from itertools import permutations,combinations_with_replacement,product
from math import factorial,comb
from collections import defaultdict
import json

def permanent(a):
    n=len(a)
    return sum(prod(a[i][p[i]] for i in range(n)) for p in permutations(range(n)))
def prod(it):
    ans=1
    for x in it: ans*=x
    return ans
def strong(a):
    n=len(a)
    for rev in (False,True):
        seen={0}; todo=[0]
        while todo:
            u=todo.pop()
            for v in range(n):
                if (a[v][u] if rev else a[u][v]) and v not in seen:
                    seen.add(v);todo.append(v)
        if len(seen)!=n:return False
    return True

def mul(a,b,N=None):
    if N is None: N=len(a)+len(b)-1
    c=[Q(0)]*N
    for i,x in enumerate(a):
        for j,y in enumerate(b[:max(0,N-i)]):c[i+j]+=x*y
    return c

def kernel_poly(K=4):
    # Store S_k as a finite sum coeff[v,l] z^v L^l, L=z/(1-z)
    out={k:defaultdict(Q) for k in range(3,K+1)}
    hist=defaultdict(int)
    for v in range(1,2*K-3):
      for e in range(1,K-1):
       for edges in combinations_with_replacement(range(v*v),v+e):
        a=[[0]*v for _ in range(v)]
        for edge in edges:a[edge//v][edge%v]+=1
        indeg=[sum(row[i] for row in a) for i in range(v)]
        outdeg=list(map(sum,a))
        if any(min(x,y)==0 or (x,y)==(1,1) for x,y in zip(indeg,outdeg)):continue
        if not strong(a):continue
        b=[row[:] for row in a]
        for i in range(v):b[i][i]+=1
        k=permanent(b)
        if k<3 or k>K or e>k-2:continue
        hist[k,v,e]+=1
        p=[Q(1,factorial(v))]
        for i in range(v):
          for j in range(v):
            m=a[i][j]
            if not m:continue
            q=[Q(0)]*(m+1);q[m]=Q(1,factorial(m))
            if i!=j:q[m-1]=Q(1,factorial(m-1))
            p=mul(p,q)
        for ell,c in enumerate(p):out[k][v,ell]+=c
    return out,hist

def expand_kernel(terms,N):
    ans=[Q(0)]*N
    for (v,ell),c in terms.items():
        if ell==0:
            if v<N:ans[v]+=c
        else:
            for n in range(v+ell,N):ans[n]+=c*comb(n-v-1,ell-1)
    return ans

def small_brute(N=4):
    out={}
    for n in range(1,N+1):
        counts=defaultdict(int);scc=defaultdict(int)
        pos=[(i,j) for i in range(n) for j in range(n) if i!=j]
        for mask in range(1<<len(pos)):
            a=[[0]*n for _ in range(n)]
            for b,(i,j) in enumerate(pos):a[i][j]=(mask>>b)&1
            mat=[row[:] for row in a]
            for i in range(n):mat[i][i]=1
            k=permanent(mat);counts[k]+=1
            if strong(a):scc[k]+=1
        out[n]={'diagonal_one':dict(counts),'scc':dict(scc)}
    return out

def formulas(S,N,K):
    # B_k = Delta(e^-z exp(-sum S_ke_k)); D=B^{-1}, all exactly rational.
    ex=[Q((-1)**n,factorial(n)) for n in range(N)]
    V={1:[Q(1)]+[Q(0)]*(N-1)}
    denominator={1:ex[:]}
    term=V
    for r in range(1,K.bit_length()+1):
        nxt={}
        for a,va in term.items():
          for b,vb in S.items():
            if a*b>K:continue
            out=nxt.setdefault(a*b,[Q(0)]*N)
            for i,x in enumerate(mul(va,vb,N)):out[i]+=x
        term=nxt
        for k,v in term.items():
            out=denominator.setdefault(k,[Q(0)]*N)
            for n,x in enumerate(mul(ex,v,N)):out[n]+=Q((-1)**r,factorial(r))*x
    for v in denominator.values():
        for n in range(N):v[n]/=2**comb(n,2)
    D={k:[Q(0)]*N for k in range(1,K+1)};D[1][0]=Q(1)
    for n in range(1,N):
      for k in range(1,K+1):
       D[k][n]=-sum(denominator[j][m]*D[k//j][n-m] for j in denominator if k%j==0 for m in range(1,n+1))
    return D

def require(condition,message):
    if not condition: raise ArithmeticError(message)

def kernel_rational_numerator(terms):
    degree=max(ell for (v,ell),c in terms.items() if c)
    numerator=[Q(0)]*(degree+max(v for v,ell in terms)+1)
    for (v,ell),c in terms.items():
      for j in range(degree-ell+1):
        numerator[v+ell+j]+=c*(-1)**j*comb(degree-ell,j)
    while numerator and not numerator[-1]:numerator.pop()
    return numerator,degree

if __name__=='__main__':
    kernels,hist=kernel_poly(4)
    rat={}
    expected={3:([Q(0)]*3+[Q(3,2),Q(-1)],3),4:([Q(0)]*3+[Q(1),Q(14,3),Q(-47,6),Q(14,3),Q(-1)],6)}
    for k,t in kernels.items():
        numerator,degree=kernel_rational_numerator(t)
        require((numerator,degree)==expected[k],('closed-form numerator',k,numerator,degree))
        rat[k]={'numerator_coefficients':[str(c) for c in numerator],'denominator_one_minus_z_power':degree}
    print('KERNEL EGFS',rat)
    print('KERNEL HISTOGRAM',dict(hist))
    N=21;S={2:[Q(0),Q(0)]+[Q(1,n) for n in range(2,N)]}
    S.update({k:expand_kernel(t,N) for k,t in kernels.items()})
    D=formulas(S,N,4);brute=small_brute(4)
    for n,row in brute.items():
      for k in range(1,5):
        b=D[k][n]*factorial(n)*2**comb(n,2)
        require(b==row['diagonal_one'].get(k,0),(n,k,b,row))
        if k>=2:require(S[k][n]*factorial(n)==row['scc'].get(k,0),(n,k,'scc'))
    ref={1:[1,1,6,150,13032,3513720,2722682160],2:[0,0,1,69,10800,4339440,4513642920],3:[0,0,0,18,4992,2626800,3177532800],4:[0,0,0,9,4254,3015450,4466769300]}
    counts={k:[int(D[k][n]*factorial(n)**2*2**comb(n,2)/k) for n in range(N)] for k in range(1,5)}
    for k,vals in ref.items(): require(counts[k][:len(vals)]==vals,(k,counts[k],vals))
    print('ALL EXACT LOW-N CHECKS PASS')
    for k in counts:print('k=',k,counts[k][:10])
    data={'S':rat,'kernel_histogram':{str(k):v for k,v in hist.items()},'counts':counts,'brute':brute}
    open('exact_checks.json','w').write(json.dumps(data,indent=2)+'\n')
