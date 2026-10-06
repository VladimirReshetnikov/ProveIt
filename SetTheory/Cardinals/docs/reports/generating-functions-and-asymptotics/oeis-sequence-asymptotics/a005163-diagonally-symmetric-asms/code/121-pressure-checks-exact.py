"""Exact finite mathematics for report121. Python standard library only.

These calculations do not certify analytic limits. All decisions use integers or
Fractions; no floating-point root finder or tolerance is used.
"""
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
from math import comb, factorial
from collections import Counter

class Failure(Exception):
    def __init__(self, code, detail=''):
        self.code, self.detail = code, detail
        super().__init__(code + (': '+detail if detail else ''))

def need(test, code, detail=''):
    if not test: raise Failure(code, detail)

def eye(n): return [[F(i==j) for j in range(n)] for i in range(n)]
def mm(a,b): return [[sum(x*y for x,y in zip(row,col)) for col in zip(*b)] for row in a]
def add(a,b): return [[x+y for x,y in zip(r,s)] for r,s in zip(a,b)]
def scale(a,c): return [[c*x for x in row] for row in a]
def trace(a): return sum(a[i][i] for i in range(len(a)))
def toeplitz(c,n): return [[c[i-j] if i>=j else F(0) for j in range(n)] for i in range(n)]

def determinant(a):
    """Fraction-free Bareiss, with row exchanges and singular matrices allowed."""
    a=[list(map(F,row)) for row in a]; n=len(a)
    need(all(len(row)==n for row in a),'DET_SHAPE')
    if not n: return F(1)
    old=F(1); sign=1
    for k in range(n-1):
        p=next((r for r in range(k,n) if a[r][k]),None)
        if p is None: return F(0)
        if p!=k: a[p],a[k]=a[k],a[p]; sign=-sign
        pivot=a[k][k]
        for i in range(k+1,n):
            for j in range(k+1,n): a[i][j]=(pivot*a[i][j]-a[i][k]*a[k][j])/old
            a[i][k]=0
        old=pivot
    return sign*a[-1][-1]

def inverse(a):
    n=len(a); b=[list(map(F,row))+ir for row,ir in zip(a,eye(n))]
    for k in range(n):
        p=next((r for r in range(k,n) if b[r][k]),None)
        need(p is not None,'INVERSE_SINGULAR')
        b[k],b[p]=b[p],b[k]; v=b[k][k]; b[k]=[x/v for x in b[k]]
        for i in range(n):
            if i!=k:
                v=b[i][k]; b[i]=[x-v*y for x,y in zip(b[i],b[k])]
    out=[row[n:] for row in b]
    need(mm(a,out)==eye(n),'INVERSE_RESIDUAL')
    return out

def determinant_derivative(a,b):
    """Multilinearity, independently of inversion/Jacobi's derivative formula."""
    return sum(determinant([[b[i][j] if j==k else a[i][j] for j in range(len(a))] for i in range(len(a))]) for k in range(len(a)))

def trim(p):
    p=list(map(F,p))
    while len(p)>1 and p[-1]==0: p.pop()
    return p

def pa(a,b): return trim([(a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0) for i in range(max(len(a),len(b)))])
def ps(p,c): return trim([c*x for x in p])
def pm(a,b):
    c=[F(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b): c[i+j]+=x*y
    return trim(c)
def pd(p): return trim([i*p[i] for i in range(1,len(p))] or [0])
def pe(p,x):
    y=F(0)
    for c in reversed(p): y=y*x+c
    return y

def divmodp(a,b):
    a,b=trim(a),trim(b); need(b!=[0],'POLY_DIV_ZERO')
    q=[F(0)]*max(1,len(a)-len(b)+1)
    while a!=[0] and len(a)>=len(b):
        k=len(a)-len(b); v=a[-1]/b[-1]; q[k]=v
        a=pa(a,[0]*k+ps(b,-v))
    return trim(q),a

def gcd(a,b):
    a,b=trim(a),trim(b)
    while b!=[0]: a,b=b,divmodp(a,b)[1]
    return ps(a,1/a[-1])
def quotient(a,b):
    q,r=divmodp(a,b); need(r==[0],'POLY_REMAINDER'); return q

def series(num,den,n):
    out=[]
    for k in range(n): out.append(F((num[k] if k<len(num) else 0)-sum(den[j]*out[k-j] for j in range(1,min(k,len(den)-1)+1)),den[0]))
    return out

def choose(n,k): return comb(n,k) if n>=0 and 0<=k<=n else 0

def original_pfaffian_entry(i,j):
    """Coefficient sum for the original unweighted skew kernel, not transformed V."""
    if i==j: return 0
    if i>j: return -original_pfaffian_entry(j,i)
    return sum((2 if k==0 else 3)*(choose(i+j-2*k-1,i-k)-choose(i+j-2*k-1,i-k-1)) for k in range(i+1))

def kernel(i,j,t):
    """Independent bivariate expansion of (v-u)/(1-uv)[t+(1+u)(1+v)/(1-u-v)]."""
    def bracket(r,s):
        if min(r,s)<0: return F(0)
        return (t if r==s==0 else 0)+sum(choose(r+s-a-b,r-a) for a,b in product(range(2),repeat=2) if r>=a and s>=b)
    return sum(bracket(i-k,j-k-1)-bracket(i-k-1,j-k) for k in range(min(i,j)+1))

def pfaffian_polynomial(n):
    """Exact recursive matching expansion in t, with memoized vertex subsets.

    This route uses no determinant, division, interpolation, or eigenvalues.
    Z_n(s)=s^(n mod 2)*P_n(s^2).
    """
    ix=list(range(n%2,n)); m=len(ix)
    entries={}
    for a in range(m):
        for b in range(a+1,m):
            i,j=ix[a],ix[b]; edge=int(j==i+1)
            entries[a,b]=[F(original_pfaffian_entry(i,j)-edge),F(edge)]
    @lru_cache(None)
    def rec(mask):
        if not mask: return (F(1),)
        indices=[i for i in range(m) if mask>>i&1]; a=indices[0]; result=[F(0)]
        for position,b in enumerate(indices[1:]):
            term=pm(entries[a,b],rec(mask^(1<<a)^(1<<b)))
            result=pa(result,ps(term,(-1)**position))
        return tuple(result)
    return list(rec((1<<m)-1))

def asm_masks(n):
    """Enumerate original symmetric matrices using legal row and column partial sums."""
    rows=[]
    for row in product((-1,0,1),repeat=n):
        s=0
        for x in row:
            s+=x
            if s not in (0,1): break
        else:
            if s==1: rows.append(row)
    result=Counter(); corner_matrices=0
    def visit(done,columns,mask):
        nonlocal corner_matrices
        r=len(done)
        if r==n:
            if all(c==1 for c in columns):
                result[mask]+=1
                if n and done[0][0]:
                    need(done[0][0]==1 and all(done[0][j]==done[j][0]==0 for j in range(1,n)),'CORNER_ROW_COLUMN')
                    corner_matrices+=1
            return
        for row in rows:
            if any(row[j]!=done[j][r] for j in range(r)): continue
            new=tuple(x+y for x,y in zip(columns,row))
            if any(x not in (0,1) for x in new): continue
            visit(done+[row],new,mask|((1<<r) if row[r] else 0))
    visit([],tuple([0]*n),0)
    return dict(result),corner_matrices

def q_from_pfaffian(n,p):
    out=[F(0)]*(n+1)
    for k,c in enumerate(p):
        exponent=n%2+2*k; out[exponent]=(-1)**((n-exponent)//2)*c
    need(out[-1]==1,'Q_MONIC')
    return trim(out)

def sturm(p):
    p=trim(p)
    if len(p)<=1: return [p]
    out=[p,pd(p)]
    while out[-1]!=[0]:
        r=divmodp(out[-2],out[-1])[1]
        if r==[0]: break
        # Positive normalization controls coefficient growth and preserves signs.
        r=ps(r,-1); r=ps(r,1/abs(r[-1])); out.append(r)
    return out

def variations(seq,x):
    signs=[1 if y>0 else -1 for p in seq if (y:=pe(p,x))]
    return sum(a!=b for a,b in zip(signs,signs[1:]))

def root_count(seq,a,b):
    need(pe(seq[0],a)!=0 and pe(seq[0],b)!=0,'STURM_ENDPOINT_ROOT')
    return variations(seq,a)-variations(seq,b)

def squarefree(p): return quotient(p,gcd(p,pd(p))) if len(p)>1 else p

def real_root_check(p):
    sf=squarefree(p); bound=F(2)+sum(abs(c/sf[-1]) for c in sf[:-1]); seq=sturm(sf)
    need(root_count(seq,-bound,bound)==len(sf)-1,'NONREAL_ROOT')
    return len(sf)-1

def interlaces(f,g):
    """Cancel gcd exactly, Sturm-isolate the reduced union, restore common roots.

    Common factors are checked real-rooted, with arbitrary multiplicities allowed.
    Alternating labels of the disjoint reduced roots certify weak interlacing of
    the originals after insertion of the shared root multiset.
    """
    need(len(f)==len(g)+1,'INTERLACING_DEGREES')
    real_root_check(f); real_root_check(g)
    h=gcd(f,g); u,v=quotient(f,h),quotient(g,h)
    need(len(gcd(u,pd(u)))==1 and len(gcd(v,pd(v)))==1,'INTERLACING_REDUCED_MULTIPLICITY')
    union=pm(u,v); seq=sturm(union); su,sv=sturm(u),sturm(v)
    B=F(2)+sum(abs(c/union[-1]) for c in union[:-1]); labels=[]; intervals=[]
    def split(a,b,count):
        if not count: return
        if count==1:
            cu,cv=root_count(su,a,b),root_count(sv,a,b)
            need(cu+cv==1,'INTERLACING_CLASSIFICATION')
            labels.append('f' if cu else 'g'); intervals.append([str(a),str(b)]); return
        mid=(a+b)/2; denominator=3
        while pe(union,mid)==0:
            mid=a+(b-a)/denominator; denominator+=1
        left=root_count(seq,a,mid)
        split(a,mid,left); split(mid,b,count-left)
    split(-B,B,len(union)-1)
    need(labels==['f' if k%2==0 else 'g' for k in range(len(union)-1)],'INTERLACING_ORDER')
    return {'gcd_degree':len(h)-1,'reduced_degree':len(u)-1,'root_labels':''.join(labels),'isolating_intervals':intervals}

class Poly:
    """Sparse Q[x,y,n,a], four algebraically independent variables."""
    def __init__(self,d): self.d={k:F(v) for k,v in d.items() if v}
    @staticmethod
    def cv(x): return x if isinstance(x,Poly) else Poly({(0,0,0,0):x})
    def __add__(self,x):
        x=Poly.cv(x); d=self.d.copy()
        for k,v in x.d.items(): d[k]=d.get(k,0)+v
        return Poly(d)
    __radd__=__add__
    def __neg__(self): return Poly({k:-v for k,v in self.d.items()})
    def __sub__(self,x): return self+-Poly.cv(x)
    def __rsub__(self,x): return Poly.cv(x)+-self
    def __mul__(self,x):
        x=Poly.cv(x); d={}
        for ka,a in self.d.items():
            for kb,b in x.d.items():
                k=tuple(i+j for i,j in zip(ka,kb)); d[k]=d.get(k,0)+a*b
        return Poly(d)
    __rmul__=__mul__
    def __pow__(self,k):
        r=Poly.cv(1)
        for _ in range(k): r=r*self
        return r

def arbitrary_parameter_identities():
    x,y,n,a=[Poly({tuple(int(j==k) for j in range(4)):1}) for k in range(4)]
    N=n*(n+a); f=lambda z:N-z*(z+a)
    b=lambda z:2*z**3+3*(a+1)*z**2+((a+1)*(a+2)-N)*z
    c=(a+1)*(N-a-1)
    comm=(x+y+a)*(x+y+a+1)*(f(x+1)-f(y+1))+x*(x+a)*f(x)-y*(y+a)*f(y)+(x+y+a)*(b(x)-b(y))
    conjug=(x-y+1)*((x-y)*(f(x)-f(y+1))+b(x)+b(y)-c)+(x+1)*(x+a+1)*f(x+1)-y*(y+a)*f(y)
    need(not comm.d,'SYMBOLIC_COMMUTATOR'); need(not conjug.d,'SYMBOLIC_CONJUGATION')
    need(not f(n).d,'SYMBOLIC_UPPER_BOUNDARY')
    return {'variables':['i','j','n','a'],'commutator_residual_terms':len(comm.d),'conjugation_residual_terms':len(conjug.d),'denominator_cleared':'i+j+a'}

def rational_matrices(n,a):
    """Simultaneous diagonal similarity of symmetric C,J,L, avoiding radicals.

    D_i=sqrt((i+a)!/i!). V=D C D^-1; Jhat=D J D^-1.
    Lhat=D L D^-1 and Uhat=D L^T D^-1; V=Lhat Uhat.
    """
    N=n*(n+a); f=lambda k:N-k*(k+a)
    b=lambda i:2*i**3+3*(a+1)*i*i+((a+1)*(a+2)-N)*i
    V=[[rising(a+j+1,i)/factorial(i) for j in range(n)] for i in range(n)]
    L=[[rising(a+j+1,i-j)/factorial(i-j) if i>=j else F(0) for j in range(n)] for i in range(n)]
    U=[[F(comb(j,i)) if j>=i else F(0) for j in range(n)] for i in range(n)]
    J=[[F(b(i)) if i==j else F((i+a)*f(i)) if i==j+1 else F(j*f(j)) if j==i+1 else F(0) for j in range(n)] for i in range(n)]
    E=[[F((-1)**i if i==j else 0) for j in range(n)] for i in range(n)]
    c=(a+1)*(N-a-1)
    need(mm(L,U)==V,'RATIONAL_CHOLESKY')
    need(mm(mm(E,L),E)==inverse(L),'RATIONAL_TRIANGULAR_INVERSE')
    need(mm(J,V)==mm(V,J),'RATIONAL_COMMUTATOR')
    need(mm(J,L)==mm(L,add(scale(mm(mm(E,J),E),-1),scale(eye(n),c))),'RATIONAL_CONJUGATION')
    B=mm(L,E); need(mm(B,B)==eye(n),'RECIPROCAL_INVOLUTION')
    need(mm(mm(B,V),B)==inverse(V),'RECIPROCAL_PAIRING')
    Q=inverse(add(eye(n),V)); need(trace(Q)==F(n,2),'RECIPROCAL_TRACE')
    return V,J,Q

def rising(a,k):
    v=F(1)
    for j in range(k): v*=a+j
    return v

def minus_J(m): return F(factorial(m))*rising(F(2),m)*rising(F(3),3*m)*rising(F(4),3*m)/(rising(F(2),2*m)*rising(F(3),2*m))
def plus_H(k):
    m=k//2
    if not k%2: return 2*factorial(m)*rising(F(3,2),m)*rising(F(3,2),3*m)*rising(F(4),3*m)/(rising(F(3,2),2*m)*rising(F(5,2),2*m))
    return F(21,2)*factorial(m)*rising(F(5,2),m)*rising(F(9,2),3*m)*rising(F(4),3*m)/(rising(F(5,2),2*m)*rising(F(7,2),2*m))

def bernoulli(k):
    b=[F(1)]
    for n in range(1,k+1): b.append(-sum(F(comb(n+1,j))*b[j] for j in range(n))/F(n+1))
    return b[k]
def bernoulli_polynomial(k,x): return sum(F(comb(k,j))*bernoulli(j)*x**(k-j) for j in range(k+1))

def stirling():
    specs=[(2,1,F(2)),(-1,1,F(3,2)),(-1,1,F(5,2)),(2,3,F(3)),(-1,3,F(3,2)),(-1,3,F(9,2)),(1,2,F(3,2)),(2,2,F(5,2)),(1,2,F(7,2)),(-2,2,F(2)),(-2,2,F(3))]
    need(sum(sign*scale for sign,scale,d in specs)==0,'STIRLING_M_LOG_M')
    need(sum(sign*(d-F(1,2)) for sign,scale,d in specs)==0,'STIRLING_LOG_M')
    need(sum(sign for sign,scale,d in specs)==0,'STIRLING_LOG_2PI')
    scale_linear=F(1); normalization_squared=F(3,7)**2; pi_exponent=0
    for sign,scale,d in specs:
        scale_linear*=F(scale)**(sign*scale)
        normalization_squared*=F(scale)**int(sign*(2*d-1))
        if d.denominator==1: gamma=F(factorial(int(d)-1)); flag=0
        else:
            k=int(d-F(1,2)); gamma=F(factorial(2*k),4**k*factorial(k)); flag=1
        normalization_squared/=gamma**(2*sign); pi_exponent-=sign*flag
    need(scale_linear==1,'STIRLING_LINEAR_LOG_SCALE')
    need(normalization_squared==1 and pi_exponent==0,'STIRLING_CONSTANT_NORMALIZATION')
    coeff=[sum(sign*(-1)**(k+1)*bernoulli_polynomial(k+1,d)/(k*(k+1)*F(scale)**k) for sign,scale,d in specs) for k in range(1,4)]
    need(coeff==[F(-3,4),F(3,4),F(-961,1152)],'STIRLING_COEFFICIENTS')
    return {'log_ratio_inverse_m_coefficients':list(map(str,coeff)),'constant_normalization_squared':str(normalization_squared),'pi_exponent':pi_exponent}

def integral_algebra():
    # y=sin(phi)^2, u^2=(1+3y)/4. Every radical canceled below is positive
    # on 0<phi<pi/2; the squared identities therefore fix the positive branch.
    y=Poly({(1,0,0,0):1}); u2=(1+3*y)*F(1,4); ct=1-2*u2
    # X^2=(1-2cos(theta))/(2(1-cos(theta)))=3y/(1+3y).
    need(not ((1-2*ct)*(1+3*y)-3*y*2*(1-ct)).d,'INTEGRAL_REGION_SUBSTITUTION')
    # A(theta)=(2-cos(theta))/(5-4cos(theta))=(1+y)/(2(1+2y)).
    need(not ((2-ct)*2*(1+2*y)-(5-4*ct)*(1+y)).d,'INTEGRAL_SYMBOL_SUBSTITUTION')
    # (dtheta/dphi)^2=9y(1-y)/(4u^2(1-u^2))=12y/(1+3y).
    need(not (9*y*(1-y)*(1+3*y)-12*y*4*u2*(1-u2)).d,'INTEGRAL_JACOBIAN_SQUARE')
    # Multiplying the three positive factors yields
    # X*A*dtheta/dphi=3y(1+y)/[(1+3y)(1+2y)].
    need(not (3*y*12*y*(1+y)**2-4*(3*y*(1+y))**2).d,'INTEGRAL_SUBSTITUTION')
    den=(1+3*y)*(1+2*y)
    partial=F(1,2)*den-2*(1+2*y)+F(3,2)*(1+3*y)
    need(not (partial-3*y*(1+y)).d,'INTEGRAL_PARTIAL_FRACTIONS')
    # tan(phi)=z changes dphi/(1+c sin^2(phi)) into dz/(1+(1+c)z^2).
    # Its endpoints 0,infinity give pi/(2sqrt(1+c)). The elementary
    # arctangent endpoint evaluation is explained in README, not numerically fit.
    z=Poly({(0,1,0,0):1}); c=Poly({(0,0,1,0):1})
    need(not ((1+z*z)+c*z*z-(1+(1+c)*z*z)).d,'INTEGRAL_TANGENT_IDENTITY')
    # In Q(sqrt(3)): (1/pi) integral is 1/4-1/2+3/(4sqrt(3)).
    exact_pair=(F(1,4)-F(1,2),F(3,4)/3)
    need(exact_pair==(F(-1,4),F(1,4)),'INTEGRAL_VALUE')
    low=F('1.7320508075688772'); high=F('1.7320508075688774')
    need(low*low<3<high*high,'SQRT3_ENCLOSURE')
    return {'value':'(sqrt(3)-1)/4','rational_enclosure':[str((low-1)/4),str((high-1)/4)],'scope':'Exact substitution/partial-fraction algebra and elementary integral evaluation; no quadrature or asymptotic inference.'}
