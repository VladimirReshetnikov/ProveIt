"""Exact algebra for Report180. Python standard library only; no removable checks.

P is the polynomial ring Q[lambda, x], where x denotes rho**2. Coefficients
are fractions.Fraction throughout. There is no floating-point arithmetic.
"""
from fractions import Fraction as F
from math import comb, factorial


def need(condition, message):
    if not condition:
        raise ValueError(message)


class P:
    def __init__(self, value=0):
        if isinstance(value, P): self.d = dict(value.d)
        elif isinstance(value, dict):
            self.d = {key:F(v) for key,v in value.items() if v}
        else: self.d = {(0,0):F(value)} if value else {}

    def __add__(self, other):
        result = dict(self.d)
        for key,value in P(other).d.items(): result[key] = result.get(key,F(0))+value
        return P(result)
    __radd__ = __add__
    def __neg__(self): return P({key:-v for key,v in self.d.items()})
    def __sub__(self, other): return self+-P(other)
    def __rsub__(self, other): return P(other)+-self
    def __mul__(self, other):
        result = {}
        for (a,b),v in self.d.items():
            for (c,d),w in P(other).d.items():
                key=(a+c,b+d); result[key]=result.get(key,F(0))+v*w
        return P(result)
    __rmul__ = __mul__
    def __truediv__(self, other):
        denominator = P(other)
        need(set(denominator.d)=={(0,0)}, 'division requires a nonzero rational constant')
        return P({key:v/denominator.d[(0,0)] for key,v in self.d.items()})
    def __pow__(self, n):
        need(type(n) is int and n>=0, 'nonnegative integer power required')
        result = P(1)
        for _ in range(n): result=result*self
        return result
    def __eq__(self, other): return self.d == P(other).d
    def at_lambda(self, value):
        result = P()
        for (a,b),c in self.d.items(): result += P({(0,b):c*F(value)**a})
        return result
    def derivative_lambda(self): return P({(a-1,b):a*v for (a,b),v in self.d.items() if a})
    def serial(self):
        return [{'lambda_degree':a,'rho_squared_degree':b,'coefficient':str(v)}
                for (a,b),v in sorted(self.d.items())]
    def univariate(self):
        need(all(b==0 for a,b in self.d),'rho remains in univariate polynomial')
        result=[F(0)]*(1+max((a for a,b in self.d),default=0))
        for (a,b),v in self.d.items(): result[a]=v
        return result


LAM=P({(1,0):1})
X=P({(0,1):1})


def integer_triangle(nmax):
    rows=[[1]]
    for n in range(1,nmax+1):
        old=rows[-1];row=[0]*(n+1);row[1]=old[-1]
        for k in range(2,n+1): row[k]=row[k-1]+(n-2)*old[n-k]
        rows.append(row)
    return rows


def marked_triangle(nmax):
    need(nmax>=2,'marked base requires n>=2')
    rows={2:[P(0),P(1),P(1)]}
    for n in range(3,nmax+1):
        old=rows[n-1]; row=[P() for _ in range(n+1)];row[1]=LAM*old[-1]
        for k in range(2,n+1): row[k]=row[k-1]+(n-2)*old[n-k]
        rows[n]=row
    return rows


def euler_coefficients(nmax):
    e=[F(1)]
    for n in range(nmax):
        e.append((sum(e[j]*e[n-j] for j in range(n+1))+(n==0))/(2*(n+1)))
    return e


def euler_by_trigonometry(nmax):
    """Independent series division: (1+sin z)/cos z = sec z+tan z."""
    num=[F(0)]*(nmax+1);den=list(num);num[0]=den[0]=F(1)
    for n in range(1,nmax+1):
        if n%2: num[n]=F((-1)**((n-1)//2),factorial(n))
        else: den[n]=F((-1)**(n//2),factorial(n))
    result=[]
    for n in range(nmax+1):result.append(num[n]-sum(den[j]*result[n-j] for j in range(1,n+1)))
    return result


def ode_coefficients(nmax, marked=False):
    e=euler_coefficients(nmax);a=[P(1) if marked else F(1)]
    for n in range(nmax):
        nxt=sum(e[j]*a[n-j] for j in range(n+1))/((n+1)**2)
        a.append(LAM*nxt if marked else nxt)
    b=[sum(e[j]*a[n-j] for j in range(n+1)) for n in range(nmax+1)]
    return e,a,b


def bernoulli(nmax):
    b=[F(1)]
    for n in range(1,nmax+1):b.append(-sum(F(comb(n+1,k))*b[k] for k in range(n))/F(n+1))
    return b


def cot_coefficients(nmax):
    """C0(t)=rho*t*cot(rho*t/2), by Bernoulli and independent series division."""
    b=bernoulli(nmax);c=[P(0) for _ in range(nmax+1)];c[0]=P(2)
    for n in range(2,nmax+1,2):c[n]=2*(-1)**(n//2)*b[n]*X**(n//2)/factorial(n)
    num=[P() for _ in c];den=[P() for _ in c]
    for n in range(0,nmax+1,2):
        num[n]=2*(-1)**(n//2)*X**(n//2)/(2**n*factorial(n))
        den[n]=(-1)**(n//2)*X**(n//2)/(2**n*factorial(n+1))
    quotient=[]
    for n in range(nmax+1):quotient.append(num[n]-sum(den[j]*quotient[n-j] for j in range(1,n+1)))
    need(c==quotient,'Bernoulli and trigonometric cotangent coefficients differ')
    return c


def frobenius(nmax=10):
    c=cot_coefficients(nmax+2);h=[P(),P(1)];g=[P(1),P()]
    for m in range(1,nmax):
        h.append(((m*m+2*LAM)*h[m]+LAM*sum(c[j]*h[m-j] for j in range(2,m+1)))/(m*(m+1)))
        rhs=-2*LAM*((2*m+1)*h[m+1]-2*m*h[m])
        g.append(((m*m+2*LAM)*g[m]+LAM*sum(c[j]*g[m-j] for j in range(2,m+1))+rhs)/(m*(m+1)))
    # Direct coefficient substitution in t*L(H)=0, independent of series assembly.
    for k in range(nmax):
        residual=(k+1)*k*h[k+1]-k*k*h[k]-LAM*sum(c[j]*h[k-j] for j in range(k+1))
        need(residual==0,'Frobenius H residual at degree '+str(k))
        r=(2*k+1)*h[k+1]-2*k*h[k]
        residual=(k+1)*k*g[k+1]-k*k*g[k]-LAM*sum(c[j]*g[k-j] for j in range(k+1))+2*LAM*r
        need(residual==0,'Frobenius G residual at degree '+str(k))
    # F=G+2lambda H log(t): logarithms cancel in F H'-F' H.
    for k in range(nmax-1):
        wr=sum(g[j]*(k-j+1)*h[k-j+1]-(j+1)*g[j+1]*h[k-j] for j in range(k+1))
        wr-=2*LAM*sum(h[j]*h[k+1-j] for j in range(k+2))
        need(wr==1,'Frobenius Wronskian at degree '+str(k))
    L=[sum(c[k]*h[j+1-k] for k in range(j+2)) for j in range(nmax-1)]
    return c,h,g,L


def falling_corrections(L,order):
    result=[P(1)]+[P() for _ in range(order)]
    for j in range(order):
        inverse=[1]+[0]*order
        for i in range(1,j+1):
            inverse=[sum(inverse[k]*i**(n-k) for k in range(n+1)) for n in range(order+1)]
        for k in range(j+1,order+1):
            result[k]+=LAM*L[j]*((-1)**(j+1)*factorial(j)*inverse[k-j-1])
    return result


def falling_corrections_independent(L,order):
    result=[P(1)]+[P() for _ in range(order)]
    for j in range(order):
        den=[1]
        for i in range(1,j+1):
            nxt=[0]*(len(den)+1)
            for k,value in enumerate(den):nxt[k]+=value;nxt[k+1]-=i*value
            den=nxt
        terms=[]
        for n in range(order-j):
            terms.append((1 if n==0 else 0)-sum(den[k]*terms[n-k] for k in range(1,min(n,len(den)-1)+1)))
            result[n+j+1]+=LAM*L[j]*((-1)**(j+1)*factorial(j)*terms[-1])
    return result


def pgf_multipliers(corrections,order):
    q=[P(1)]
    for n in range(1,order+1):q.append(corrections[n]-sum(corrections[j].at_lambda(1)*q[n-j] for j in range(1,n+1)))
    for n in range(order+1):
        need(sum(corrections[j].at_lambda(1)*q[n-j] for j in range(n+1))==corrections[n],'PGF quotient product')
        need(q[n].at_lambda(1)==(n==0),'PGF normalization')
    return q


def trim(poly):
    poly=list(poly)
    while len(poly)>1 and poly[-1]==0:poly.pop()
    return poly


def remainder(a,b):
    a=trim(a);b=trim(b)
    need(b!=[0],'polynomial division by zero')
    while len(a)>=len(b) and a!=[0]:
        degree=len(a)-len(b);factor=a[-1]/b[-1]
        for j,c in enumerate(b):a[j+degree]-=factor*c
        a=trim(a)
    return a


def sturm(poly):
    poly=trim([F(x) for x in poly]);chain=[poly,[j*poly[j] for j in range(1,len(poly))]]
    while chain[-1]!=[0]:
        rem=remainder(chain[-2],chain[-1])
        if rem==[0]:break
        chain.append([-x for x in rem])
    degrees=[len(p)-1 for p in chain]
    plus=[1 if p[-1]>0 else -1 for p in chain]
    minus=[sg*(-1)**degree for sg,degree in zip(plus,degrees)]
    changes=lambda signs:sum(a!=b for a,b in zip(signs,signs[1:]))
    return {'degrees':degrees,'signs_minus_infinity':minus,'signs_plus_infinity':plus,
            'variations_minus_infinity':changes(minus),'variations_plus_infinity':changes(plus),
            'real_root_count':changes(minus)-changes(plus),'squarefree':degrees[-1]==0,
            'chain_coefficients_ascending':[[str(x) for x in p] for p in chain]}


def rational_tails(M=420):
    a=F(200,2**(M+1));d=F(200*(M+1),2**M)
    h=F(8,3)*F(3,4)**(M+1);t=F(16,3)*(M+4)*F(3,4)**(M+1)
    tail=(16*a+200*t+a*t+2*d+200*h+d*h)/2
    need(tail<F(1,10**44),'Taylor tail exceeds certificate threshold')
    # The audit's coefficient majorant: zeta(2j)<2 and a=3/2 give
    # 8*sum_{j>=1}36^{-j}=8/35. The induction gap is increasing for m>=2.
    gap=lambda m:F(3,2)*m*(m+1)-m*m-2-F(8,35)
    need(gap(2)>0 and gap(3)-gap(2)>0,'Frobenius majorant induction base')
    # exp(4)<200 by a rational exponential series plus geometric tail.
    K=20; exp4=sum(F(4**k,factorial(k)) for k in range(K+1))
    exp4_upper=exp4+F(4**(K+1),factorial(K+1))/(1-F(4,K+2))
    need(exp4_upper<200,'global endpoint majorant')
    # The elementary classical pi<22/7 bound implies pi²/3<4.
    need(F(22,7)**2/3<4,'pi bound')
    return {'degree':M,'epsilon_A':str(a),'epsilon_D':str(d),'epsilon_H':str(h),
            'epsilon_T':str(t),'wronskian_tail_bound':str(tail),'strict_upper':'1/10^44',
            'H_weighted_coefficient_sum_upper':'8/35','majorant_gap_at_m2':str(gap(2)),
            'exp4_rational_upper':str(exp4_upper)}
