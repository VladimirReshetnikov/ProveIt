"""Fresh rational finite identities for report124; Python standard library only.

No analytic limit, uniform operator bound, or asymptotic remainder is decided here.
"""
from fractions import Fraction as F
from functools import lru_cache
from math import comb, factorial

class Failure(Exception):
    def __init__(self, code, detail=''):
        self.code, self.detail = code, str(detail)
        super().__init__(code + ': ' + str(detail))

def require(test, code, detail=''):
    if not test:
        raise Failure(code, detail)

def trim(p):
    p=list(map(F,p)) or [F(0)]
    while len(p)>1 and not p[-1]: p.pop()
    return p

def padd(p,q): return trim([(p[k] if k<len(p) else 0)+(q[k] if k<len(q) else 0) for k in range(max(len(p),len(q)))])
def pscale(p,c): return trim([c*v for v in p])
def pmul(p,q):
    out=[F(0)]*(len(p)+len(q)-1)
    for i,a in enumerate(p):
        for j,b in enumerate(q): out[i+j]+=a*b
    return trim(out)
def ppow(p,n):
    out=[F(1)]
    for _ in range(n): out=pmul(out,p)
    return out
def pdiff(p): return trim([k*p[k] for k in range(1,len(p))])
def peval(p,x):
    out=F(0)
    for a in reversed(p): out=out*x+a
    return out
def rising(a,n):
    out=F(1)
    for k in range(n): out*=a+k
    return out
def binomial(a,n): return rising(a-n+1,n)/factorial(n)

def zeros(r,c): return [[F(0) for _ in range(c)] for _ in range(r)]
def eye(n): return [[F(i==j) for j in range(n)] for i in range(n)]
def transpose(A): return [list(c) for c in zip(*A)]
def madd(A,B): return [[x+y for x,y in zip(r,s)] for r,s in zip(A,B)]
def mscale(A,c): return [[c*x for x in r] for r in A]
def mmul(A,B):
    require(len(A[0])==len(B),'MATRIX_SHAPE')
    return [[sum((x*y for x,y in zip(r,c)),F(0)) for c in zip(*B)] for r in A]
def mpow(A,n):
    out=eye(len(A))
    for _ in range(n): out=mmul(out,A)
    return out
def trace(A): return sum((A[i][i] for i in range(len(A))),F(0))
def diag(values): return [[v if i==j else F(0) for j in range(len(values))] for i,v in enumerate(values)]
def frobenius2(A): return sum((x*x for r in A for x in r),F(0))
def determinant(A):
    """Ordinary exact Gaussian elimination, independently of Pfaffian matching."""
    A=[list(map(F,r)) for r in A]; n=len(A); ans=F(1)
    require(all(len(r)==n for r in A),'DETERMINANT_SHAPE')
    for k in range(n):
        pivot=next((j for j in range(k,n) if A[j][k]),None)
        if pivot is None: return F(0)
        if pivot!=k: A[k],A[pivot]=A[pivot],A[k]; ans=-ans
        v=A[k][k]; ans*=v
        for j in range(k+1,n):
            ratio=A[j][k]/v
            for l in range(k+1,n): A[j][l]-=ratio*A[k][l]
    return ans

def inverse(A):
    n=len(A); out=[list(map(F,r))+e for r,e in zip(A,eye(n))]
    for k in range(n):
        pivot=next((j for j in range(k,n) if out[j][k]),None)
        require(pivot is not None,'INVERSE_SINGULAR')
        out[k],out[pivot]=out[pivot],out[k]
        v=out[k][k]; out[k]=[x/v for x in out[k]]
        for j in range(n):
            if j!=k:
                v=out[j][k]; out[j]=[x-v*y for x,y in zip(out[j],out[k])]
    result=[r[n:] for r in out]
    require(mmul(A,result)==eye(n),'INVERSE_RESIDUAL')
    return result

def replace_columns(A,columns):
    return [[columns[j][i] if j in columns else A[i][j] for j in range(len(A))] for i in range(len(A))]
def derivative_det(A,B):
    return sum((determinant(replace_columns(A,{j:[r[j] for r in B]})) for j in range(len(A))),F(0))
def mixed_derivative_det(A,B,C):
    return sum((determinant(replace_columns(A,{j:[r[j] for r in B],k:[r[k] for r in C]})) for j in range(len(A)) for k in range(len(A)) if j!=k),F(0))

# Original DSASM skew generating function and a distinct published binomial entry.
def choose(n,k): return comb(n,k) if n>=0 and 0<=k<=n else 0

def kernel_grid(size,t):
    """Truncated formal product (v-u)/(1-uv) [t+(1+u)(1+v)/(1-u-v)]."""
    B=zeros(size,size)
    for i in range(size):
        for j in range(size):
            for a in (0,1):
                for b in (0,1):
                    if i>=a and j>=b: B[i][j]+=comb(i+j-a-b,i-a)
    B[0][0]+=t
    G=zeros(size,size)
    for i in range(size):
        for j in range(size):
            for k in range(min(i,j)+1):
                if j-k>=1: G[i][j]+=B[i-k][j-k-1]
                if i-k>=1: G[i][j]-=B[i-k-1][j-k]
    return G

def skew_entry(i,j):
    if i>j: return -skew_entry(j,i)
    if i==j: return F(0)
    return F(sum((2 if k==0 else 3)*(choose(i+j-2*k-1,i-k)-choose(i+j-2*k-1,i-k-1)) for k in range(i+1)))

def pfaffian_polynomial(n):
    """Perfect matchings in polynomial t; no determinant or interpolation."""
    vertices=tuple(range(n%2,n))
    @lru_cache(None)
    def solve(ix):
        if not ix: return (F(1),)
        out=[F(0)]
        for position in range(1,len(ix)):
            a,b=ix[0],ix[position]; edge=F(b==a+1)
            rest=ix[1:position]+ix[position+1:]
            out=padd(out,pscale(pmul([skew_entry(a,b)-edge,edge],solve(rest)),(-1)**(position+1)))
        return tuple(out)
    return list(solve(vertices))

def dsasm_checks(ranges, historical):
    maxn=ranges['dsasm_n_max']; fugacities=list(map(F,ranges['determinant_t']))
    p=[pfaffian_polynomial(n) for n in range(maxn+2)]
    for n in range(7):
        z=[0]*(n+1)
        for k,a in enumerate(p[n]): z[n%2+2*k]=a
        require(z==historical['small_z'][str(n)],'INHERITED_SMALL_Z_MATH',n)
    cases=0; results=[]
    for t in fugacities:
        grid=kernel_grid(maxn+2,t)
        for i in range(maxn+2):
            for j in range(maxn+2):
                target=skew_entry(i,j)+(t-1)*(int(j==i+1)-int(i==j+1))
                require(grid[i][j]==target,'ORIGINAL_KERNEL_COEFFICIENT',f'{i},{j},{t}')
        for n in range(1,maxn+1):
            H=[[grid[i][j+1] for j in range(n)] for i in range(n)]
            D=determinant(H)
            require(D==peval(p[n],t)*peval(p[n+1],t),'ADJACENT_DETERMINANT',f'{n},{t}')
            cases+=1
    grid=kernel_grid(maxn+2,F(3)); base=kernel_grid(maxn+2,F(2))
    for n in range(1,maxn+1):
        H=[[grid[i][j+1] for j in range(n)] for i in range(n)]
        B=[[grid[i][j+1]-base[i][j+1] for j in range(n)] for i in range(n)]
        V=[[F(comb(i+j+2,i)) for j in range(n)] for i in range(n)]
        D=determinant(H); dp=derivative_det(H,B); ell=dp/D
        require(D==2**n*determinant(madd(eye(n),V)),'PASCAL_CALIBRATION',n)
        asm=F(1)
        for j in range(n+1): asm*=F(factorial(3*j+1),factorial(n+1+j))
        require(D==2**n*asm,'ASM_PRODUCT_CALIBRATION',n)
        ep=peval(pdiff(p[n]),3)/peval(p[n],3)+peval(pdiff(p[n+1]),3)/peval(p[n+1],3)
        require(ell==ep,'ADJACENT_DERIVATIVE',n)
        require(ell==trace(mmul(inverse(H),B)),'JACOBI_DETERMINANT_DERIVATIVE',n)
        require(str(ell)==historical['ell_at_3'][str(n)],'INHERITED_DERIVATIVE_MATH',n)
        def mean(k): return F(k%2)+6*peval(pdiff(p[k]),3)/peval(p[k],3)
        require(mean(n)+mean(n+1)==1+6*ell,'ADJACENT_MEAN_CALIBRATION',n)
        require(3*ell<=mean(n)<=3*ell+1,'FINITE_MEAN_BRACKET',n)
        results.append({'n':n,'D3':str(D),'Dprime3':str(dp),'ell3':str(ell)})
    # Bernoulli B2 coefficient in log Gamma(c*N+d), using the four factorials.
    terms=[(F(3),F(-1),1),(F(1),F(0),1),(F(2),F(0),-1),(F(2),F(-1),-1)]
    contributions=[sign*(d*d-d+F(1,6))/(2*c) for c,d,sign in terms]
    log_asm=sum(contributions,F(0)); log_even=log_asm/2
    require(log_asm==F(-5,36) and log_even==F(-5,72),'CALIBRATION_STIRLING_LOG_POWER')
    return {'adjacent_cases':cases,'calibration':results,'historical_small_z_recomputed':7,'gamma_1_over_N_contributions':list(map(str,contributions)),'calibration_log_n_coefficient':str(log_even),'analytic_stirling_remainder_certified':False}

# Continuous Hahn, Jacobi, and Fourier conversion, with all radicals factored out.
def hahn_a(n): return F(n*(n+2)*(3*n+2)*(3*n+4),4*(2*n+1)*(2*n+3))
def monic_family(nmax,scale):
    out=[[F(1)],[F(0),F(1)]]
    for k in range(1,nmax): out.append(padd([0]+out[k],pscale(out[k-1],-hahn_a(k)/scale)))
    return out[:nmax+1]

def shift_parts(p,h):
    re=[F(0)]*len(p); im=[F(0)]*len(p)
    for n,c in enumerate(p):
        for k in range(n+1):
            power=n-k; v=c*comb(n,k)*h**power
            (re if power%2==0 else im)[k]+=v*(-1)**(power//2)
    return trim(re),trim(im)

def hahn_difference(p):
    re,im=shift_parts(p,F(3)); re=padd(re,pscale(p,-1))
    return pscale(padd(pmul([F(-35,4),0,1],re),pscale([0]+im,-6)),2)

def hahn_hypergeometric(n):
    # p_n(z)=i^n (5/3)_n (2)_n/n! sum [(-n)_k(n+3)_k(a+iz)_k/...].
    total=[F(0)]; term=[F(1)]
    for k in range(n+1):
        if k: term=pmul(term,[F(5,6)+k-1,1])
        factor=rising(-n,k)*rising(n+3,k)/(rising(F(5,3),k)*rising(F(2),k)*factorial(k))
        total=padd(total,pscale(term,factor))
    total=pscale(total,rising(F(5,3),n)*factorial(n+1)/factorial(n))
    require(all(not c for j,c in enumerate(total) if (n+j)%2),'HAHN_REAL_PARITY',n)
    return trim([c*(-1)**((n+j)//2) if (n+j)%2==0 else F(0) for j,c in enumerate(total)])

def jacobi(n,a,b):
    out=[F(0)]
    for k in range(n+1):
        coeff=binomial(n+a,n-k)*binomial(n+b,k)/2**n
        out=padd(out,pscale(pmul(ppow([-1,1],k),ppow([1,1],n-k)),coeff))
    return out

def L(p): return padd(pscale(pmul([1,0,-1],pdiff(p)),F(1,2)),pmul([F(-1,6),-1],p))
def jacobi_moment(k,a,b):
    return sum((F(comb(k,j)*2**j*(-1)**(k-j))*rising(b+1,j)/rising(a+b+2,j) for j in range(k+1)),F(0))
def norm_ratio(n,a,b): return F(a+b+1,2*n+a+b+1)*rising(a+1,n)*rising(b+1,n)/(factorial(n)*rising(a+b+1,n))
def expectation(p,a,b): return sum((c*jacobi_moment(k,a,b) for k,c in enumerate(p)),F(0))

def coefficients(p,basis):
    p=trim(p); out=[F(0)]*len(basis)
    require(len(p)<=len(basis),'BASIS_DEGREE')
    for k in range(len(basis)-1,-1,-1):
        if k<len(p):
            out[k]=p[k]
            p=padd(p,pscale(basis[k],-out[k]))
    require(p==[0],'BASIS_REMAINDER')
    return out

def K_action(p):
    out=list(p); derivative=list(p)
    for k in range(len(p)):
        if k: derivative=pdiff(derivative)
        if k%2==0: factor=F((-1)**(k//2),3**(k//2)*factorial(k))
        else: factor=F(-(-1)**(k//2),3**(k//2)*factorial(k))
        out=padd(out,pscale(derivative,factor))
    return out

def hahn_jacobi_checks(ranges):
    nmax=ranges['hahn_degree_max']; a,b=F(4,3),F(2,3)
    qx=monic_family(nmax,1); qz=monic_family(nmax,9)
    limages=[[F(1)]]
    for n in range(nmax): limages.append(L(limages[-1]))
    polys=[jacobi(n,a,b) for n in range(nmax+1)]
    for n in range(nmax+1):
        require(hahn_difference(qx[n])==pscale(qx[n],-9*n*(n+3)),'HAHN_DIFFERENCE_EIGENVALUE',n)
        hp=hahn_hypergeometric(n); ell=comb(2*n+2,n)
        require(hp==pscale(qz[n],ell),'HAHN_HYPERGEOMETRIC_RECURRENCE',n)
        image=[F(0)]
        for k,c in enumerate(hp):
            if c: image=padd(image,pscale(limages[k],c*(-1)**((n-k)//2)))
        require(image==pscale(polys[n],(-1)**n*factorial(n+1)),'FOURIER_JACOBI_PHASE',n)
        require(limages[n][-1]==F((-1)**n*factorial(n+1),2**n),'FOURIER_FLAG_LEADING',n)
        require(polys[n][-1]==F(ell,2**n),'JACOBI_LEADING',n)
        for k in range(n+1):
            target=norm_ratio(n,a,b) if k==n else F(0)
            require(expectation(pmul(polys[n],polys[k]),a,b)==target,'JACOBI_BETA_ORTHOGONALITY',f'{n},{k}')
        if n:
            hn=F(factorial(n+1)**2,ell**2)*norm_ratio(n,a,b)
            prev=F(factorial(n)**2,comb(2*n,n-1)**2)*norm_ratio(n-1,a,b)
            require(hn/prev==hahn_a(n)/9,'HAHN_JACOBI_NORM_RATIO',n)
    # Fourier beta-logistic measure: squared gauge, then dxi/dt=2/(1-t^2).
    exponents=[2*F(7,6)-1,2*F(5,6)-1]
    require(exponents==[a,b] and F(2,16)*2==F(1,4),'FOURIER_MEASURE_NORMALIZATION')
    gamma_product=F(4,9)*F(2,3)*2 # Gamma(7/3)Gamma(5/3) in units pi/sqrt(3).
    hzero=F(2,3)*gamma_product/2 # h0 in units pi^2/sqrt(3).
    require(hzero==F(16,81) and F(81,8)*hzero==2,'FOURIER_TOTAL_MASS')
    # Finite cubic uses t=x/sqrt(3), avoiding irrational matrix entries.
    defects=[]
    for n in range(1,ranges['cubic_matrix_n_max']+1):
        basis=monic_family(n,3); I=eye(n)
        J=zeros(n,n)
        for k in range(n):
            if k+1<n: J[k+1][k]=1
            if k: J[k-1][k]=hahn_a(k)/3
        K=transpose([coefficients(K_action(basis[k]),basis[:n]) for k in range(n)])
        comm=madd(mmul(J,K),mscale(mmul(K,J),-1))
        Km2=madd(K,mscale(I,-2))
        first=mscale(mmul(mmul(madd(mscale(mpow(J,2),3),mscale(I,F(-35,4))),mpow(Km2,2)),madd(K,I)),-1)
        second=mscale(mmul(mmul(mmul(J,comm),K),Km2),18)
        require(madd(first,second)==diag([-9*k*(k+3) for k in range(n)]),'FINITE_HAHN_CUBIC',n)
        defect=madd(madd(mpow(madd(K,mscale(I,-1)),2),mscale(mpow(comm,2),3)),mscale(I,-4))
        require(all(defect[i][j]==0 for i in range(n) for j in range(n-1)),'FINITE_BOUNDARY_SUPPORT',n)
        require(defect[-1][-1]==3*n*(n-2),'FINITE_BOUNDARY_DIAGONAL',n)
        defects.append(str(defect[-1][-1]))
    return {'degrees':nmax+1,'beta_orthogonality_pairs':(nmax+1)*(nmax+2)//2,'finite_cubic_sizes':ranges['cubic_matrix_n_max'],'retained_boundary_diagonals':defects,'original_total_mass':'2'}

# Gamma recurrences are exact products; transcendental base factors must cancel.
def gamma_reduction(q):
    q=F(q); require(q>0,'GAMMA_POSITIVE_ARGUMENT')
    multiplier=F(1)
    while q>1: q-=1; multiplier*=q
    return multiplier,q

def gamma_quotient(numerator,denominator):
    factor=F(1); bases={}
    for sign,args in [(1,numerator),(-1,denominator)]:
        for arg in args:
            m,b=gamma_reduction(arg); factor*=m if sign==1 else 1/m
            bases[b]=bases.get(b,0)+sign
    require(all(v==0 for v in bases.values()),'GAMMA_BASE_NOT_CANCELLED',bases)
    return factor

def scalar_checks(ranges):
    pairs=[(F(4,3),F(2,3)),(F(2,3),F(4,3)),(F(7,3),F(2,3)),(F(5,3),F(4,3))]
    cases=0
    for a,b in pairs:
        s=a+b
        for n in range(1,ranges['contiguous_n_max']+1):
            lhs=pscale(pmul([1,-1],jacobi(n-1,a+1,b)),2*n+s)
            rhs=padd(pscale(jacobi(n-1,a,b),2*(n+a)),pscale(jacobi(n,a,b),-2*n))
            require(lhs==rhs,'JACOBI_CONTIGUOUS',f'{a},{b},{n}')
            original=gamma_quotient([n+a,n+b,n+1,n+s+1],[n,n+s,n+a+1,n+b+1])*(2*n+s+1)/(2*n+s-1)
            shifted=2*gamma_quotient([n+a+1,n+b,n+1,n+s+1],[n,n+s+1,n+a+1,n+b+1])*(2*n+s+1)/(2*n+s)
            A2=(n+a)**2/n**2*original
            B2=(2*n+s)**2/(4*n*n)*shifted
            require(A2==(n+a)*(n+s)*(2*n+s+1)/(n*(n+b)*(2*n+s-1)),'CONTIGUOUS_A_GAMMA',f'{a},{b},{n}')
            require(B2==(2*n+s)*(2*n+s+1)/(2*n*(n+b)),'CONTIGUOUS_B_GAMMA',f'{a},{b},{n}')
            cases+=1
    # Formal polynomial identity for cancellation of the first gamma-ratio term.
    a=spvar(2,0); b=spvar(2,1); one=spconstant(2,1); s=spadd(a,b)
    term1=spscale(spmul(a,spadd(a,one)),F(1,2))
    term2=spscale(spmul(a,spadd(spadd(s,b),one)),F(1,2))
    target=spmul(a,spadd(s,one))
    require(spadd(term1,term2)==target,'GAMMA_FIRST_ORDER_CANCELLATION')
    require(F(2,3)*2-2==F(-2,3) and F(-2,3)>-1,'SCALAR_VARIANCE_EXPONENT')
    return {'contiguous_and_gamma_cases':cases,'gamma_first_order_identity':'alpha*(alpha+beta+1)','variance_diagonal_power':'-2/3','uniform_bound_certified':False}

# Sparse Laurent polynomials: exponents can be negative; log symbols independent.
def spconstant(n,c): return {(0,)*n:F(c)} if c else {}
def spvar(n,k):
    key=[0]*n; key[k]=1; return {tuple(key):F(1)}
def spterm(exponents,c=1): return {tuple(exponents):F(c)} if c else {}
def spadd(*polys):
    out={}
    for p in polys:
        for k,v in p.items(): out[k]=out.get(k,F(0))+v
    return {k:v for k,v in out.items() if v}
def spscale(p,c): return {k:v*c for k,v in p.items() if v*c}
def spmul(p,q):
    out={}
    for a,c in p.items():
        for b,d in q.items():
            key=tuple(x+y for x,y in zip(a,b)); out[key]=out.get(key,F(0))+c*d
    return {k:v for k,v in out.items() if v}
def sppow(p,n):
    out=spconstant(len(next(iter(p))),1)
    for _ in range(n): out=spmul(out,p)
    return out

def inverse_center_checks():
    # Variable order alpha, beta, kappa, r, L=log r.
    a,b,k,r,L=[spvar(5,j) for j in range(5)]
    d=spadd(spterm([-1,0,1,0,1],F(1,2)),spterm([-2,2,0,0,0],F(1,8)))
    z=spadd(r,spterm([-1,1,0,0,0],F(-1,2)),spmul(d,spterm([0,0,0,-1,0])))
    lhs=spadd(spmul(a,sppow(z,2)),spmul(b,z),spscale(spmul(a,sppow(r,2)),-1),spscale(spmul(k,L),-1))
    rhs=spmul(spmul(a,sppow(d,2)),spterm([0,0,0,-2,0]))
    require(lhs==rhs,'INVERSE_CENTER_EXACT_CANCELLATION')
    # rho=sqrt(alpha), Y=sqrt(y), Ly=log y, La=log alpha, beta, kappa.
    images=[spterm([2,0,0,0,0,0]),spvar(6,4),spvar(6,5),spterm([-1,1,0,0,0,0]),spadd(spscale(spvar(6,2),F(1,2)),spscale(spvar(6,3),F(-1,2)))]
    mapped={}
    for powers,coefficient in z.items():
        image=spconstant(6,coefficient)
        for power,replacement in zip(powers,images):
            if power<0:
                require(len(replacement)==1,'INVERSE_SUBSTITUTION_MONOMIAL')
                (exponent,value),=replacement.items()
                replacement=spterm([-v for v in exponent],1/value); power=-power
            if power: image=spmul(image,sppow(replacement,power))
        mapped=spadd(mapped,image)
    target=spadd(spterm([-1,1,0,0,0,0]),spterm([-2,0,0,0,1,0],F(-1,2)),spterm([-1,-1,1,0,0,1],F(1,4)),spterm([-1,-1,0,1,0,1],F(-1,4)),spterm([-3,-1,0,0,2,0],F(1,8)))
    require(mapped==target,'INVERSE_CENTER_Y_SUBSTITUTION')
    require(mapped.get((-1,-1,1,0,0,1))==F(1,4),'INVERSE_LOGLOG_COEFFICIENT')
    require(F(5,72)*mapped[(-1,-1,1,0,0,1)]==F(5,288),'INVERSE_LOGLOG_KAPPA')
    # Independent rational samples of exact cancellation, not numerical log tests.
    count=0
    for av in [F(1,3),F(2),F(7,5)]:
        for bv in [F(-2,3),F(0),F(5,4)]:
            for rv,Lv in [(F(3),F(2)),(F(7,2),F(-1,3)),(F(11),F(5))]:
                kv=F(5,72); dv=(kv*Lv+bv*bv/(4*av))/(2*av); zv=rv-bv/(2*av)+dv/rv
                require(av*zv*zv+bv*zv==av*rv*rv+kv*Lv+av*dv*dv/(rv*rv),'INVERSE_CENTER_SAMPLE')
                count+=1
    require(F(3,4)-F(1,2)==F(1,4) and F(-1,2)+F(1,2)==0,'CALIBRATION_LINEAR_COEFFICIENT')
    return {'exact_laurent_identity':True,'loglog_multiplier_of_inverse_sqrt_alpha':'5/288','rational_polynomial_samples':count,'rounding_or_effective_threshold_certified':False}

# Rational noncommuting finite projections. Exponentials/square roots are avoided.
def householder(v):
    den=sum(x*x for x in v); return madd(eye(len(v)),mscale([[x*y for y in v] for x in v],F(-2,den)))

def frame(d,n):
    U=mmul(householder(list(range(1,d+1))),householder([(-1)**j*(j+2) for j in range(d)]))
    S=[r[:n] for r in U]
    require(mmul(transpose(S),S)==eye(n),'RATIONAL_FRAME_ORTHONORMAL')
    return S

def matrix_checks(ranges):
    cases=[]; mixed_cases=0; noncommuting=0
    for d,n in ranges['projection_dimensions']:
        S=frame(d,n); ST=transpose(S); P=mmul(S,ST); I=eye(n)
        weights=[F(j+1,3*d) for j in range(d)]
        X=mmul(diag([v if j<d//2 else F(0) for j,v in enumerate(weights)]),S)
        Y=mmul(diag([v if j>=d//2 else F(0) for j,v in enumerate(weights)]),S)
        A=mmul(transpose(X),X); B=mmul(transpose(Y),Y)
        require(trace(mmul(A,B))==frobenius2(mmul(X,transpose(Y))),'OVERLAP_TRACE_FACTORIZATION',f'{d},{n}')
        require(trace(mmul(A,B))>0,'OVERLAP_FINITE_PROJECTION_NOT_DISCARDED',f'{d},{n}')
        if mmul(A,B)!=mmul(B,A): noncommuting+=1
        for s,u in [(F(0),F(0)),(F(1,3),F(2,3)),(F(1),F(1))]:
            T=madd(I,mscale(madd(mscale(A,s),mscale(B,u)),-2)); R=inverse(T)
            D=determinant(T); Ds=derivative_det(T,mscale(A,-2)); Du=derivative_det(T,mscale(B,-2)); Dsu=mixed_derivative_det(T,mscale(A,-2),mscale(B,-2))
            hessian=(D*Dsu-Ds*Du)/(D*D)
            require(hessian==-4*trace(mmul(mmul(mmul(R,A),R),B)),'MIXED_LOGDETERMINANT_HESSIAN',f'{d},{n},{s},{u}')
            require(hessian<=0,'MIXED_LOGDETERMINANT_SIGN')
            Ra=inverse(madd(I,mscale(A,-2*s)))
            left=mmul(mmul(X,R),transpose(Y))
            right=mmul(mmul(mmul(X,Ra),transpose(Y)),madd(eye(d),mscale(mmul(mmul(Y,R),transpose(Y)),2*u)))
            require(left==right,'NONCOMMUTING_RESOLVENT_FACTORIZATION',f'{d},{n},{s},{u}')
            mixed_cases+=1
        IA=madd(I,mscale(A,-2)); IB=madd(I,mscale(B,-2)); total=madd(I,mscale(madd(A,B),-2))
        correction=madd(I,mscale(mmul(mmul(mmul(inverse(IA),A),B),inverse(IB)),-4))
        require(mmul(mmul(IA,correction),IB)==total,'ORDERED_DETERMINANT_FACTORIZATION',f'{d},{n}')
        require(determinant(correction)==determinant(total)/(determinant(IA)*determinant(IB)),'NONCOMMUTING_DETERMINANT_RATIO')
        # Tilted-projection factorization for arbitrary commuting positive E,V.
        E=diag([F(j+2,d+2) for j in range(d)]); V=diag([F(2*j-d,3*d) for j in range(d)])
        T=mmul(mmul(ST,mpow(E,2)),S); Ti=inverse(T)
        Q=mmul(mmul(mmul(mmul(E,S),Ti),ST),E)
        require(mpow(Q,2)==Q and transpose(Q)==Q,'TILTED_ORTHOGONAL_PROJECTION',f'{d},{n}')
        IQ=madd(eye(d),mscale(Q,-1)); IP=madd(eye(d),mscale(P,-1))
        residual=mmul(mmul(mmul(mmul(IQ,E),IP),V),S)
        hess=trace(mmul(Q,mpow(V,2)))-trace(mmul(mmul(mmul(Q,V),Q),V))
        factor=trace(mmul(Ti,mmul(transpose(residual),residual)))
        require(hess==factor==frobenius2(mmul(mmul(IQ,V),Q)),'TILTED_VARIANCE_FACTORIZATION',f'{d},{n}')
        # Relative Fredholm finite algebra, keeping the nonnormal error.
        C=mscale(madd(A,B),F(1,2)); skew=madd(A,mscale(transpose(A),-1))
        skew=[[F(i-j,17*d) for j in range(n)] for i in range(n)]
        sym=mscale(madd(A,B),F(1,7)); error=madd(sym,skew)
        for delta in [F(-2),F(0),F(3,2)]:
            base=madd(I,mscale(C,delta)); R=inverse(base)
            require(trace(mmul(R,skew))==0,'RELATIVE_SKEW_TRACE_CANCELLATION')
            require(trace(mmul(R,error))==trace(mmul(R,sym)),'RELATIVE_SYMMETRIC_TRACE')
            ratio=determinant(madd(I,mscale(madd(C,error),delta)))/determinant(base)
            require(ratio==determinant(madd(I,mscale(mmul(R,error),delta))),'RELATIVE_FINITE_DETERMINANT')
        cases.append({'ambient':d,'rank':n,'overlap':str(trace(mmul(A,B))),'tilted_variance':str(hess)})
    require(noncommuting==len(cases),'NONCOMMUTING_CONTROLS_REQUIRED')
    return {'projections':cases,'mixed_hessian_cases':mixed_cases,'noncommuting_controls':noncommuting,'analytic_overlap_bound_certified':False}
