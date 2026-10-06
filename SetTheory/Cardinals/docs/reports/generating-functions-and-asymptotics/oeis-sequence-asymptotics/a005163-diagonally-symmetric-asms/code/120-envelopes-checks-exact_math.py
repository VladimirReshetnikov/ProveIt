"""Independent finite DSASM reconstructions over integers and rational numbers.

The orientation and original matrix enumerations are unrelated algorithms.
Finite calculations here supplement, rather than prove, the all-size stability
and asymptotic arguments in the report. No numerical root finder is used.
"""
from fractions import Fraction as F
from itertools import product
from math import comb, factorial
from collections import Counter
from functools import lru_cache
from support import need


def choose(n,k):
    return comb(n,k) if n>=0 and 0<=k<=n else 0


def original_entry(i,j):
    """The original unweighted Pfaffian coefficient sum, independently coded."""
    if i==j:return 0
    if i>j:return -original_entry(j,i)
    return sum((2 if k==0 else 3)*(choose(i+j-2*k-1,i-k)-choose(i+j-2*k-1,i-k-1)) for k in range(i+1))


def pfaffian(a):
    """Exact skew elimination, with a separate recursive check for small sizes."""
    a=[[F(x) for x in row] for row in a];n=len(a);v=F(1)
    need(n%2==0 and all(len(row)==n for row in a),'PFAFFIAN_SHAPE')
    need(all(a[i][j]==-a[j][i] for i in range(n) for j in range(n)),'PFAFFIAN_SKEW')
    for k in range(0,n,2):
        pivot=next((j for j in range(k+1,n) if a[k][j]),None)
        if pivot is None:return F(0)
        if pivot!=k+1:
            a[pivot],a[k+1]=a[k+1],a[pivot]
            for row in a:row[pivot],row[k+1]=row[k+1],row[pivot]
            v=-v
        h=a[k][k+1];v*=h
        for i in range(k+2,n):
            for j in range(i+1,n):
                a[i][j]+=(a[k][j]*a[k+1][i]-a[k][i]*a[k+1][j])/h
                a[j][i]=-a[i][j]
    return v


def recursive_pfaffian(a):
    if not a:return F(1)
    return sum(((-1)**(j+1))*a[0][j]*recursive_pfaffian([[a[r][c] for c in range(1,len(a)) if c!=j] for r in range(1,len(a)) if r!=j]) for j in range(1,len(a)))


def det(a):
    """Fraction-free Bareiss elimination, including pivot swaps."""
    a=[[F(v) for v in row] for row in a];n=len(a)
    need(all(len(row)==n for row in a),'DETERMINANT_SHAPE')
    if not n:return F(1)
    sign=1;previous=F(1)
    for k in range(n-1):
        p=next((r for r in range(k,n) if a[r][k]),None)
        if p is None:return F(0)
        if p!=k:a[p],a[k]=a[k],a[p];sign=-sign
        h=a[k][k]
        for i in range(k+1,n):
            for j in range(k+1,n):a[i][j]=(h*a[i][j]-a[i][k]*a[k][j])/previous
            a[i][k]=0
        previous=h
    return sign*a[-1][-1]


def matrix_add(a,b):return [[x+y for x,y in zip(r,s)] for r,s in zip(a,b)]
def mm(a,b):return [[sum(x*y for x,y in zip(row,col)) for col in zip(*b)] for row in a]
def transpose(a):return list(map(list,zip(*a)))
def identity(n):return [[F(i==j) for j in range(n)] for i in range(n)]
def toeplitz(coeff,n):return [[coeff[i-j] if i>=j else F(0) for j in range(n)] for i in range(n)]


def trim(p):
    p=list(map(F,p))
    while len(p)>1 and not p[-1]:p.pop()
    return p

def pa(p,q):return trim([(p[i] if i<len(p) else 0)+(q[i] if i<len(q) else 0) for i in range(max(len(p),len(q)))])
def pm(p,q):
    out=[F(0)]*(len(p)+len(q)-1)
    for i,a in enumerate(p):
        for j,b in enumerate(q):out[i+j]+=a*b
    return trim(out)
def ps(p,c):return trim([c*v for v in p])
def pe(p,x):
    v=F(0)
    for a in reversed(p):v=v*x+a
    return v

def quotient(p,q):
    p=trim(p);q=trim(q);need(q!=[0],'POLYNOMIAL_ZERO_DIVISOR');out=[F(0)]*max(1,len(p)-len(q)+1)
    while p!=[0] and len(p)>=len(q):
        i=len(p)-len(q);v=p[-1]/q[-1];out[i]=v
        p=pa(p,[0]*i+ps(q,-v))
    need(p==[0],'POLYNOMIAL_DIVISION_REMAINDER')
    return trim(out)


def interpolate(values):
    """Newton forward interpolation, independently of determinant construction."""
    d=list(map(F,values));out=[F(0)];basis=[F(1)]
    for k in range(len(values)):
        out=pa(out,ps(basis,d[0]));d=[d[j+1]-d[j] for j in range(len(d)-1)]
        basis=ps(pm(basis,[-k,1]),F(1,k+1))
    need(all(pe(out,k)==v for k,v in enumerate(values)),'INTERPOLATION_RESIDUAL')
    return out


def series(num,den,n):
    need(den[0]!=0,'SERIES_ZERO_DIVISOR');out=[]
    for k in range(n):out.append(((num[k] if k<len(num) else 0)-sum(den[j]*out[k-j] for j in range(1,min(k,len(den)-1)+1)))/F(den[0]))
    return out


def compose_series(f,h,n):
    out=[F(0)]*n;power=[F(1)]+[F(0)]*(n-1)
    for c in f:
        out=[a+c*b for a,b in zip(out,power)];power=(pm(power,h)+[F(0)]*n)[:n]
    return out


def kernel(i,j,t):
    """Direct bivariate expansion of (v-u)/(1-uv)*(t+(1+u)(1+v)/(1-u-v))."""
    def bracket(r,s):
        if r<0 or s<0:return F(0)
        return (t if r==s==0 else 0)+sum(choose(r+s-a-b,r-a) for a,b in product(range(2),repeat=2) if r>=a and s>=b)
    return sum(bracket(i-k,j-k-1)-bracket(i-k-1,j-k) for k in range(min(i,j)+1))


def matrix_polynomials(n):
    """Recover D_n(t) from n+1 exact evaluations; degree at most n."""
    return interpolate([det([[kernel(i,j+1,F(t)) for j in range(n)] for i in range(n)]) for t in range(n+1)])


def asm_polynomial(n):
    """Enumerate the original symmetric {-1,0,1} matrices by legal ASM rows."""
    rows=[]
    for row in product((-1,0,1),repeat=n):
        total=0;valid=True
        for x in row:
            total+=x
            if total not in (0,1):valid=False;break
        if valid and total==1:rows.append(row)
    result=Counter()
    def search(done,columns,mask):
        r=len(done)
        if r==n:
            if all(x==1 for x in columns):result[mask]+=1
            return
        for row in rows:
            if any(row[i]!=done[i][r] for i in range(r)):continue
            new=tuple(columns[i]+row[i] for i in range(n))
            if any(x not in (0,1) for x in new):continue
            search(done+[row],new,mask|((1<<r) if row[r] else 0))
    search([],tuple([0]*n),0)
    return result


def orientation_polynomial(n):
    """Enumerate arrows of the actual triangular graph, retaining joint fugacities."""
    vertices=[(i,j) for i in range(n) for j in range(i,n)];index={v:k for k,v in enumerate(vertices)}
    edges=[]
    for i,j in vertices:
        if j<n-1:edges.append((index[i,j],index[i,j+1]))
        if i<j:edges.append((index[i,j],index[i+1,j]))
    need(len(edges)==n*(n-1),'ORIENTATION_EDGE_COUNT')
    fixed=[int(j==n-1) for i,j in vertices];bulk=[index[i,j] for i,j in vertices if i<j];diagonal=[index[i,i] for i in range(n)]
    result=Counter()
    for arrows in product((0,1),repeat=len(edges)):
        degree=fixed[:]
        for edge,choice in zip(edges,arrows):degree[edge[choice]]+=1
        if any(degree[k]!=2 for k in bulk):continue
        need(sum(degree[k] for k in diagonal)==n,'ORIENTATION_HOMOGENEITY')
        need(all(degree[k] in (0,1,2) for k in diagonal),'ORIENTATION_DIAGONAL_DEGREE')
        mask=sum(1<<i for i,k in enumerate(diagonal) if degree[k]==1)
        result[mask]+=1
    return result


def mask_to_z(masks,n):
    p=[0]*(n+1)
    for mask,c in masks.items():p[mask.bit_count()]+=c
    return p


def ordinary_asm(n):
    out=F(1)
    for j in range(n):out*=F(factorial(3*j+1),factorial(n+j))
    need(out.denominator==1,'ASM_PRODUCT_INTEGRAL')
    return out


def shifted_product(n):
    out=F(1)
    for i in range(1,n+2):
        for j in range(i,n+2):out*=F(n+i+j,2*i+j-1)
    return out


class Poly:
    """Sparse Q[u,v,t], used only for exact rational-function residuals."""
    def __init__(self,d):self.d={k:F(v) for k,v in d.items() if v}
    @staticmethod
    def cv(x):return x if isinstance(x,Poly) else Poly({(0,0,0):x})
    def __add__(self,o):
        o=Poly.cv(o);d=self.d.copy()
        for k,v in o.d.items():d[k]=d.get(k,0)+v
        return Poly(d)
    __radd__=__add__
    def __neg__(self):return Poly({k:-v for k,v in self.d.items()})
    def __sub__(self,o):return self+-Poly.cv(o)
    def __rsub__(self,o):return Poly.cv(o)+-self
    def __mul__(self,o):
        o=Poly.cv(o);d={}
        for a,x in self.d.items():
            for b,y in o.d.items():
                k=tuple(i+j for i,j in zip(a,b));d[k]=d.get(k,0)+x*y
        return Poly(d)
    __rmul__=__mul__
    def derivative(self,index):
        return Poly({tuple(k-int(j==index) for j,k in enumerate(p)):p[index]*c for p,c in self.d.items() if p[index]})
    def __pow__(self,n):
        need(type(n) is int and n>=0,'SPARSE_POWER');r=Poly.cv(1)
        for _ in range(n):r=r*self
        return r


class Rat:
    def __init__(self,n,d=1):self.n=Poly.cv(n);self.d=Poly.cv(d);need(bool(self.d.d),'RATIONAL_ZERO_DIVISOR')
    @staticmethod
    def cv(x):return x if isinstance(x,Rat) else Rat(x)
    def __add__(self,o):o=Rat.cv(o);return Rat(self.n*o.d+o.n*self.d,self.d*o.d)
    __radd__=__add__
    def __neg__(self):return Rat(-self.n,self.d)
    def __sub__(self,o):return self+-Rat.cv(o)
    def __rsub__(self,o):return Rat.cv(o)+-self
    def __mul__(self,o):o=Rat.cv(o);return Rat(self.n*o.n,self.d*o.d)
    __rmul__=__mul__
    def __truediv__(self,o):o=Rat.cv(o);return Rat(self.n*o.d,self.d*o.n)
    def __rtruediv__(self,o):return Rat.cv(o)/self
    def derivative(self,index):return Rat(self.n.derivative(index)*self.d-self.n*self.d.derivative(index),self.d**2)
    def __pow__(self,n):return Rat(self.n**n,self.d**n)
    def equals(self,o):o=Rat.cv(o);return not (self.n*o.d-o.n*self.d).d


def rational_identities():
    u,v,t=[Rat(Poly({tuple(int(k==j) for k in range(3)):1})) for j in range(3)]
    K=(v-u)/(1-u*v)*(t+(1+u)*(1+v)/(1-u-v));K0=-u*(t+(1+u)/(1-u))
    Q=u*u-u+1;A=(1-u*u)*(t-1-3*u/Q);B=(u-2)*(u+1)*(2*u-1)/((1-u)*Q)
    need((K-K0).equals(v*(A/(1-u*v)+B/(1-u-v))),'RATIONAL_KERNEL_DECOMPOSITION')
    def C(z):return (1-z)**2*((t-1)*(z*z-z+1)-3*z)/((z-2)*(2*z-1))
    need((A/B).equals(C(u)),'RATIONAL_A_OVER_B')
    G=((t-4)*u*u+(4-t)*u+t-1)/((2-u)*(1-u)**2*(1+u))
    need(C(-u/(1-u)).equals(G),'RATIONAL_MOBIUS_TRANSFORM')
    G3=(-u*u+u+2)/((2-u)*(1-u)**2*(1+u))
    need(G3.equals(1/(1-u)**2),'RATIONAL_CALIBRATION')
    # exp(xi)=(4+gamma)/(1+gamma); eliminate logarithms in phi(xi).
    need(((1+2*(4+u)/(1+u))/3).equals((3+u)/(1+u)),'JENSEN_PARAMETER_IDENTITY')
    # exp(psi(v))=(3 exp(v)-1)/2, the exact inverse relationship.
    need(((1+2*((3*u-1)/2))/3).equals(u),'JENSEN_INVERSE_IDENTITY')
    need((u*(2*u/(1+2*u)).derivative(0)).equals(2*u/(1+2*u)**2),'JENSEN_CONVEXITY_IDENTITY')
    need((1-3*u/(3*u-1)).equals(-1/(3*u-1)),'UPPER_MAP_DERIVATIVE_IDENTITY')
    need(((v/(2*u))*u).equals(v/2),'CHORD_PARITY_CANCELLATION')
    need(((4+u)/(1+u)-1).equals(3/(1+u)) and (4-(4+u)/(1+u)).equals(3*u/(1+u)),
         'JENSEN_PARAMETER_RANGE')
    return {'kernel_decomposition':True,'Mobius_transform':True,'calibration_rational_identity':True,'Jensen_parameter_and_inverse':True}


def algebra_checks(f):
    result=rational_identities();maximum=f['ranges']['triangular_n_max']
    for n in range(1,maximum+1):
        L=[[F(choose(i,j)) for j in range(n)] for i in range(n)]
        Li=[[F((-1)**(i-j)*choose(i,j)) for j in range(n)] for i in range(n)]
        P=[[F(comb(i+j,i)) for j in range(n)] for i in range(n)]
        need(mm(L,transpose(L))==P,'PASCAL_FACTORIZATION')
        need(mm(L,Li)==identity(n),'PASCAL_INVERSE')
        need(mm(Li,transpose(Li))==[[(-1)**(i+j)*P[i][j] for j in range(n)] for i in range(n)],'PASCAL_CONGRUENCE')
        h=[0]+[F((-1)**(k-1)) for k in range(1,n)]
        for degree in range(n):
            fz=[0]*degree+[1];left=mm(mm(Li,toeplitz((fz+[0]*n)[:n],n)),L)
            right=toeplitz(compose_series(fz,h,n),n)
            need(left==right,'BINOMIAL_TOEPLITZ_CONJUGACY')
        V=mm(toeplitz([F(k+1) for k in range(n)],n),P)
        need(V==[[F(comb(i+j+2,i)) for j in range(n)] for i in range(n)],'HOCKEY_STICK')
    # Gamma(aN+b) inverse-N coefficients from Bernoulli B2(b)/(2a).
    specs=[(3,-1,1),(1,0,1),(2,0,-1),(2,-1,-1)]
    contributions=[F(sign)*(F(b*b-b)+F(1,6))/(2*a) for a,b,sign in specs]
    need(list(map(str,contributions))==f['stirling']['contributions'],'STIRLING_CONTRIBUTIONS')
    d=sum(contributions);need(str(d)==f['stirling']['ratio_inverse_N'],'STIRLING_RATIO')
    need(str(d/2)==f['stirling']['even_logarithm'],'STIRLING_EVEN')
    need(d==F(-5,36) and d/2==F(-5,72),'STIRLING_RATIONAL_IDENTITY')
    # Formal log coefficients: N*(3 log3 -4 log2), constant -3/2 log3 +2 log2.
    need(sum(F(sign)*(F(b)-F(1,2)) for a,b,sign in specs)==0,'STIRLING_LOG_N_CANCELLATION')
    need(sum(sign*a for a,b,sign in specs)==0,'STIRLING_N_LOG_N_CANCELLATION')
    logN={a:sum(F(sign)*(F(b)-F(1,2)) for aa,b,sign in specs if aa==a) for a in (2,3)}
    need(logN=={2:F(2),3:F(-3,2)},'STIRLING_CONSTANT_LOG_COEFFICIENTS')
    nlog={a:sum(F(sign*a) for aa,b,sign in specs if aa==a) for a in (2,3)}
    need(nlog=={2:F(-4),3:F(3)},'STIRLING_LINEAR_LOG_COEFFICIENTS')
    kappa=F(5,72)
    need(kappa==-d/2,'STIRLING_INVERSE_KAPPA')
    # Formal inverse residual: g, c and L=log(n0) are independent symbols.
    gg,cc,LL=[Rat(Poly({tuple(int(k==j) for k in range(3)):1})) for j in range(3)]
    displacement=-cc/gg;log_shift=kappa*LL/gg
    need((gg*displacement+cc).equals(0),'INVERSE_LINEAR_CANCELLATION')
    need((gg*log_shift-kappa*LL).equals(0),'INVERSE_LOG_CANCELLATION')
    need((gg*displacement**2/2+cc*displacement).equals(-cc**2/(2*gg)),
         'INVERSE_CONSTANT_RESIDUAL')
    # Odd calibration: use 2b=g+log2, and retain only controlled coefficients.
    need((gg-gg/2).equals(gg/2),'ODD_CALIBRATION_QUADRATIC')
    need(((2*cc-gg)+gg-cc).equals(cc),'ODD_CALIBRATION_LINEAR')
    need(d+kappa==-kappa,'ODD_CALIBRATION_LOGARITHM')
    ceiling_checks=0
    for den in range(2,10):
        for a in range(-2*den,2*den+1):
            for b in range(a,a+den):
                left=F(a,den);right=F(b,den)
                ceil_left=-((-left.numerator)//left.denominator)
                ceil_right=-((-right.numerator)//right.denominator)
                need(0<=ceil_right-ceil_left<=1,'INVERSE_CEILING_WIDTH')
                ceiling_checks+=1
    # Equality distinguishes >= from >, independently of any asymptotic bound.
    need(-((-F(4).numerator)//F(4).denominator)==4 and F(4).numerator//F(4).denominator+1==5,
         'INVERSE_THRESHOLD_EQUALITY')
    need(F(65,32)<F(27,16)**2,'MAP_ENDPOINT_RATIONAL_BOUND')
    result.update({'finite_triangular_identity_sizes':maximum,'Stirling_inverse_N':str(d),'even_calibration_logarithm':str(d/2),'inverse_formal_cancellations':True,'finite_ceiling_lemma_instances':ceiling_checks})
    return result


def enumeration_checks(f):
    terms=[]
    for n in range(1,21):
        ix=list(range(n%2,n));a=[[F(original_entry(i,j)) for j in ix] for i in ix];value=pfaffian(a)
        need(value.denominator==1,'PFAFFIAN_INTEGRAL');terms.append(int(value))
        if n<=8:need(value==recursive_pfaffian(a),'PFAFFIAN_RECURSIVE_AGREEMENT')
        need(value*value==det(a),'PFAFFIAN_SQUARE')
    need(terms==f['external_prefix'],'EXTERNAL_PREFIX')
    polys={}
    for n in range(1,f['ranges']['matrix_n_max']+1):
        masks=asm_polynomial(n);polys[str(n)]=mask_to_z(masks,n)
        need(polys[str(n)]==f['small_z'][str(n)],'MATRIX_POLYNOMIAL')
        need(sum(polys[str(n)])==terms[n-1],'MATRIX_PFAFFIAN_COUNT')
        need(sum(c*2**i for i,c in enumerate(polys[str(n)]))==terms[n],'WEIGHT_TWO_IDENTITY')
        need(all(c==0 for i,c in enumerate(polys[str(n)]) if i%2!=n%2),'DIAGONAL_PARITY')
        if n<=f['ranges']['graph_n_max']:
            need(orientation_polynomial(n)==masks,'ORIENTATION_MATRIX_JOINT_POLYNOMIAL')
    for i in range(f['ranges']['kernel_grid_size']):
        for j in range(f['ranges']['kernel_grid_size']):
            need(kernel(i,j,F(1))==original_entry(i,j),'KERNEL_ORIGINAL_ENTRY')
    return {'external_terms_verified':len(terms),'external_index_range':[1,20],
            'matrix_polynomials_n_max':f['ranges']['matrix_n_max'],'orientation_joint_polynomials_n_max':f['ranges']['graph_n_max'],
            'small_z':polys,'kernel_grid_size':f['ranges']['kernel_grid_size'],'root_finding_used':False}


def determinant_checks(f):
    prev=[F(1)];polys={1:prev}
    for n in range(1,f['ranges']['determinant_polynomial_n_max']+1):
        dn=matrix_polynomials(n);nextp=quotient(dn,prev)
        need(all(c.denominator==1 and c>=0 for c in nextp),'ADJACENT_POLYNOMIAL_POSITIVITY')
        need(len(nextp)-1==(n+1)//2 and nextp[-1]==1 and nextp[0]>0,'ADJACENT_POLYNOMIAL_DEGREE')
        polys[n+1]=nextp;prev=nextp
        need(pe(dn,3)==2**n*ordinary_asm(n+1),'CALIBRATION_DETERMINANT')
        need(pe(dn,1)==f['external_prefix'][n-1]*f['external_prefix'][n],'ADJACENT_UNWEIGHTED')
        if n+1<=f['ranges']['matrix_n_max']:
            eps=(n+1)%2;z=f['small_z'][str(n+1)]
            need(nextp==list(map(F,z[eps::2])),'ADJACENT_MATRIX_POLYNOMIAL')
        # n+1 distinct values certify equality of all degree-at-most-n determinant polynomials.
        for t in range(n+1):
            P=[[F(comb(i+j,i)) for j in range(n)] for i in range(n)]
            R=[2,-3,-1,3,-1];Nt=[t-1,4-t,t-4]
            band=matrix_add(toeplitz((R+[0]*n)[:n],n),mm(toeplitz((Nt+[0]*n)[:n],n),P))
            need(det(band)==pe(dn,t),'BANDED_DETERMINANT_POLYNOMIAL')
            if n<=f['ranges']['transform_n_max']:
                cnum=pm([1,-2,1],[t-1,-t-2,t-1]);cden=[2,-5,2]
                C=series(cnum,cden,n);G=series([t-1,4-t,t-4],pm(pm([2,-1],[1,-2,1]),[1,1]),n)
                need(2**n*det(matrix_add(P,toeplitz(C,n)))==pe(dn,t),'PASCAL_C_DETERMINANT')
                need(2**n*det(matrix_add(identity(n),mm(toeplitz(G,n),P)))==pe(dn,t),'PASCAL_G_DETERMINANT')
                # Original bordered coefficient determinant of K/((1+u)(1+v)).
                bordered=[[sum((-1)**(i-r+j-s)*kernel(r,s,F(t)) for r in range(i+1) for s in range(j+1)) for j in range(n)]+[F((-1)**i)] for i in range(n+1)]
                need(det(bordered)==pe(dn,t),'ORIGINAL_BORDERED_DETERMINANT')
    for n in range(1,f['ranges']['calibration_n_max']+1):
        shifted=det([[F(i==j)+comb(i+j+2,i) for j in range(n)] for i in range(n)])
        need(shifted==shifted_product(n)==ordinary_asm(n+1),'SHIFTED_ANDREWS_INDEXING')
        N=n+1;ratio=F(factorial(N-1)*factorial(3*N-2),factorial(2*N-1)*factorial(2*N-2))
        need(ordinary_asm(N)/ordinary_asm(N-1)==ratio,'ASM_FACTORIAL_RATIO')
        if n>=2:need(shifted_product(n)/shifted_product(n-1)==ratio,'SHIFTED_PRODUCT_RATIO')
    # Direct even product against calibrated polynomial values, without selecting an amplitude.
    val=F(1)
    for m in range(1,(max(polys)//2)+1):
        val*=2*ordinary_asm(2*m)/ordinary_asm(2*m-1)
        need(pe(polys[2*m],3)==val,'EVEN_CALIBRATION_PRODUCT')
    return {'adjacent_polynomials_n_max':max(polys),'determinant_polynomial_degree_n_max':f['ranges']['determinant_polynomial_n_max'],
            'bordered_Pascal_transform_sizes':f['ranges']['transform_n_max'],'shifted_Andrews_sizes':f['ranges']['calibration_n_max'],
            'independent_polynomials':{str(n):[int(x) for x in p] for n,p in polys.items()}}
