"""Supplementary exact algebra for the pressure theorem; no analytic-limit proof.

Finite matrices are reconstructed from the original kernel. All formal algebra,
path sums, integrations of polynomial symbols and density partial fractions use
Fractions. The all-size limiting and analytic-continuation arguments are separate.
"""
from fractions import Fraction as F
from math import comb
import exact as e


def derivative(p,index=0):
    return e.Poly({tuple(v-int(j==index) for j,v in enumerate(k)):k[index]*c for k,c in p.d.items() if k[index]})

class Rat:
    def __init__(self,n,d=1): self.n,self.d=e.Poly.cv(n),e.Poly.cv(d);e.need(bool(self.d.d),'PRESSURE_RAT_DENOMINATOR')
    @staticmethod
    def cv(x): return x if isinstance(x,Rat) else Rat(x)
    def __add__(self,x): x=Rat.cv(x);return Rat(self.n*x.d+x.n*self.d,self.d*x.d)
    __radd__=__add__
    def __neg__(self): return Rat(-self.n,self.d)
    def __sub__(self,x): return self+-Rat.cv(x)
    def __rsub__(self,x): return Rat.cv(x)+-self
    def __mul__(self,x): x=Rat.cv(x);return Rat(self.n*x.n,self.d*x.d)
    __rmul__=__mul__
    def __truediv__(self,x): x=Rat.cv(x);return Rat(self.n*x.d,self.d*x.n)
    def __rtruediv__(self,x): return Rat.cv(x)/self
    def __pow__(self,k): return Rat(self.n**k,self.d**k)
    def dby(self,index=0): return Rat(derivative(self.n,index)*self.d-self.n*derivative(self.d,index),self.d**2)
    def equal(self,x): x=Rat.cv(x);return not (self.n*x.d-x.n*self.d).d
    def point(self,value):
        def poly(p):
            e.need(all(k[1:]==(0,0,0) for k in p.d),'PRESSURE_UNIVARIATE_POINT')
            return sum(c*value**k[0] for k,c in p.d.items())
        return poly(self.n)/poly(self.d)
    def coefficients(self):
        def poly(p):
            e.need(all(k[1:]==(0,0,0) for k in p.d),'PRESSURE_UNIVARIATE_COEFFICIENTS')
            out=[F(0)]*(1+max((k[0] for k in p.d),default=0))
            for k,c in p.d.items(): out[k[0]]=c
            return out
        n,d=poly(self.n),poly(self.d); g=e.gcd(n,d); n,d=e.quotient(n,g),e.quotient(d,g)
        scale=1/d[-1]; return {'numerator':list(map(str,e.ps(n,scale))),'denominator':list(map(str,e.ps(d,scale)))}


def mod_sqrt3(r):
    def poly(p):
        e.need(all(k[1:]==(0,0,0) for k in p.d),'PRESSURE_SQRT3_UNIVARIATE')
        out=[F(0)]*(1+max((k[0] for k in p.d),default=0))
        for k,c in p.d.items(): out[k[0]]=c
        return out
    e.need(e.divmodp(poly(r.n),[-3,0,1])[1]==[0],'PRESSURE_SQRT3_IDENTITY')
    e.need(e.divmodp(poly(r.d),[-3,0,1])[1]!=[0],'PRESSURE_SQRT3_DENOMINATOR')


def algebra():
    s,a,z,w=[Rat(e.Poly({tuple(int(j==k) for j in range(4)):1})) for k in range(4)]
    q=2+z-z*z; r=1-z+z*z; A0=a*a+a+1; t=4-3/A0
    e.need((q+(t-3)*r).equal((4-t)*(a+1-z)*(a+z)),'PRESSURE_POLE_FACTORIZATION')
    e.need(((2*a+1)**2).equal(4*A0-3),'PRESSURE_ROOT_PARAMETER')
    # Resolvent integral partial fractions, c=s here; w=sin(phi)^2.
    B=s*s-s+1
    lhs=6*w/(1+3*w)*(s-F(1,2)+F(3,2)*w)/(B+3*s*w)
    rhs=-2/((s-1)*(3*w+1))+1/s+(s+1)*B/(s*(s-1)*(B+3*s*w))
    e.need(lhs.equal(rhs),'PRESSURE_RESOLVENT_PARTIAL_FRACTIONS')
    # Differentiate the log pressure explicitly in s, using t=s^2.
    fp=(2/(s+1)-1/(s+2))/(2*s)
    expected=(s+3)/(2*s*(s+1)*(s+2))
    e.need(fp.equal(expected),'PRESSURE_FIRST_DERIVATIVE')
    # Insert A0=3/(4-s^2) in dF/da divided by dt/da, after sqrt(A0)=(2a+1)/s.
    B0=3/(4-s*s)
    integrated_derivative=B0*B0*(1-1/s)/(3*(B0-1))-B0/6
    e.need(integrated_derivative.equal(fp),'PRESSURE_INTEGRAL_DERIVATIVE')
    fpp=fp.dby()/(2*s)
    mod_sqrt3(fp-(1-s/2)); mod_sqrt3(fpp-(F(1,4)-s/6))
    exponential=(s+1)**2/(2*(s+2))
    e.need(exponential.point(F(1))==F(2,3) and exponential.point(F(2))==F(9,8),'PRESSURE_SPECIAL_VALUES')
    mod_sqrt3(exponential-1)
    mean=s*s*fp; variance=s*mean.dby()
    e.need(mean.equal(F(1,2)-1/((s+1)*(s+2))),'PRESSURE_MEAN')
    e.need(variance.equal(s*(2*s+3)/((s+1)**2*(s+2)**2)),'PRESSURE_VARIANCE')
    e.need((2*s*s*fp+2*s**4*fpp).equal(variance),'PRESSURE_VARIANCE_T_DERIVATIVE')
    mod_sqrt3(variance-(F(21,2)-6*s))
    cumulants=[mean,variance]
    for _ in range(2): cumulants.append(s*cumulants[-1].dby())
    e.need([x.point(F(1)) for x in cumulants]==[F(1,3),F(5,36),F(-1,27),F(-19,216)],'PRESSURE_UNIFORM_STATISTICS')
    # Linear free-energy coefficient in the independent basis log(2),log(3):
    # b=(3/4)log(3)-(1/2)log(2); (1/2)f(1)=(1/2)log(2)-(1/2)log(3).
    e.need(F(3,4)-F(1,2)==F(1,4) and -F(1,2)+F(1,2)==0,'PRESSURE_LINEAR_FREE_ENERGY')
    # Density: lambda=y^2, x=y^2 represented by w for polynomial partial fractions.
    mass=6/((w+1)*(w+4)); mass_parts=2/(w+1)-2/(w+4)
    e.need(mass.equal(mass_parts),'PRESSURE_DENSITY_MASS_PARTIAL_FRACTIONS')
    e.need(F(2,2)-F(2,4)==F(1,2),'PRESSURE_DENSITY_MASS')
    trans=6/((w+1)*(w+4)*(w+s*s))
    apart=2/((s*s-1)*(w+1))-2/((s*s-4)*(w+4))+6/((s*s-1)*(s*s-4)*(w+s*s))
    e.need(trans.equal(apart),'PRESSURE_STIELTJES_PARTIAL_FRACTIONS')
    evaluated=1/(s*s-1)-1/(2*(s*s-4))+3/(s*(s*s-1)*(s*s-4))
    e.need(evaluated.equal(fp),'PRESSURE_STIELTJES_TRANSFORM')
    # Compactification u=1/(3+lambda): test the elementary resolvent identity.
    u=w; lam=1/u-3
    e.need((1/(s+lam)).equal(u/(1+(s-3)*u)),'PRESSURE_COMPACTIFIED_RESOLVENT')
    return {'pressure_exponential':'(s+1)^2/(2(s+2)), t=s^2',
            'f_at_1':'log(2/3)','f_at_3':'0','f_at_4':'log(9/8)',
            'linear_free_energy_coefficient':'log(3)/4','f_prime_at_3':'1-sqrt(3)/2','f_second_at_3':'1/4-sqrt(3)/6',
            'cumulants':[{'order':k+1,'rational_coefficients_ascending':x.coefficients(),'at_s1':str(x.point(F(1)))} for k,x in enumerate(cumulants)],
            'finite_density_mass':'1/2','compactification_infinity_mass':'1/2',
            'density_transform':'(sqrt(t)+3)/(2sqrt(t)(sqrt(t)+1)(sqrt(t)+2))',
            'note':'The transform partial fractions have removable exceptional values t=1,4; equality there follows by continuity of the positive convergent integral.'}


def path_trace(matrices,word):
    """Sparse closed-walk enumeration, independently of matrix multiplication."""
    n=len(next(iter(matrices.values()))); total=F(0)
    for start in range(n):
        states={start:F(1)}
        for letter in word:
            new={}; matrix=matrices[letter]
            for i,value in states.items():
                for j in range(n):
                    if matrix[i][j]: new[j]=new.get(j,F(0))+value*matrix[i][j]
            states=new
        total+=states.get(start,F(0))
    return total


def symbol_moment(word):
    """Exact phase-space integral of z^net h(x,theta)^r by Laurent expansion."""
    net=word.count('A')-word.count('T'); r=word.count('H')
    b=[0,-1,0,2]; a=[0,1,0,-1]; terms={0:[F(1)]}
    for _ in range(r):
        new={}
        for shift,p in terms.items():
            for delta,factor in [(0,b),(1,a),(-1,a)]: new[shift+delta]=e.pa(new.get(shift+delta,[0]),e.pm(p,factor))
        terms=new
    p=terms.get(-net,[F(0)])
    return sum(c/F(k+1) for k,c in enumerate(p))


def finite(ranges):
    values=[]; times=list(map(F,ranges['pressure_t']))
    words=ranges['mixed_words']
    moments=[]
    for n in range(1,ranges['pressure_n_max']+1):
        V,J,Q=e.rational_matrices(n,F(2)); I=e.eye(n)
        S=[[F(i==j+1) for j in range(n)] for i in range(n)]; S2=e.mm(S,S)
        q=e.add(e.add(e.scale(I,2),S),e.scale(S2,-1)); r=e.add(e.add(I,e.scale(S,-1)),S2)
        U=e.add(I,e.scale(Q,-1)); base=e.determinant([[e.kernel(i,j+1,F(3)) for j in range(n)] for i in range(n)])
        for t in times:
            delta=t-3; M=e.add(q,e.scale(e.mm(r,U),delta)); B=e.add(I,e.scale(U,-delta))
            N=e.add(q,e.scale(e.mm(U,e.inverse(B)),3*delta))
            e.need(e.mm(N,B)==M,'PRESSURE_FINITE_ORDERED_FACTORIZATION',f'n={n},t={t}')
            original=e.determinant([[e.kernel(i,j+1,t) for j in range(n)] for i in range(n)])/base
            e.need(e.determinant(M)/2**n==original,'PRESSURE_FINITE_POLE_CLEARING',f'n={n},t={t}')
            e.need(e.determinant(q)==2**n,'PRESSURE_Q_DETERMINANT',str(n))
            values.append({'n':n,'t':str(t),'ratio':str(original)})
    # Small hand-integrated symbol checkpoints, independent of path traces.
    known={'A':F(0),'AT':F(1),'H':F(0),'AH':F(1,4),'HH':F(9,35),'HHHH':F(729,5005)}
    for word,want in known.items(): e.need(symbol_moment(word)==want,'PRESSURE_SYMBOL_MOMENT',word)
    # Additional exact word checks at n=12 use rationally similar A,A*,H.
    for n in ranges['mixed_word_sizes']:
        V,J,Q=e.rational_matrices(n,F(2)); I=e.eye(n)
        A=[[F(i==j+1) for j in range(n)] for i in range(n)]
        T=[[F(j,j+2) if j==i+1 else F(0) for j in range(n)] for i in range(n)]
        tau=F(3*(n*(n+2)-3),2); H=e.scale(e.add(J,e.scale(I,-tau)),F(1,n**3))
        matrices={'A':A,'T':T,'H':H}
        for word in words:
            prod=I
            for letter in word: prod=e.mm(prod,matrices[letter])
            val=e.trace(prod)/n
            e.need(val==path_trace(matrices,word)/n,'PRESSURE_MIXED_PATH_IDENTITY',f'n={n},{word}')
            moments.append({'n':n,'word':word,'normalized_finite_trace':str(val),'formal_symbol_integral':str(symbol_moment(word))})
    # Leading local Jacobi profiles, checked at every fixed integer offset used by words.
    x=e.Poly({(1,0,0,0):1}); n=e.Poly({(0,0,1,0):1}); N=n*(n+2)
    def lead(p): return e.Poly({(k[0],k[1],0,k[3]):v for k,v in p.d.items() if k[2]==3})
    for offset in range(ranges['profile_offsets'][0],ranges['profile_offsets'][1]+1):
        i=n*x+offset; f=N-i*(i+2)
        diagonal=2*i**3+9*i**2+(12-N)*i-F(3,2)*(N-3)
        e.need(not (lead(diagonal)-(2*x**3-x)).d,'PRESSURE_JACOBI_DIAGONAL_PROFILE')
        e.need(not (lead((i+2)*f)-x*(1-x*x)).d and not (lead(i*f)-x*(1-x*x)).d,'PRESSURE_JACOBI_OFFDIAGONAL_PROFILE')
    return {'determinant_cases':values,'mixed_word_cases':moments,'local_profile_offsets':ranges['profile_offsets'],
            'scope':'Finite equality and formal local-symbol certificates only; the printed finite traces are not used to infer convergence.'}


def corollaries():
    r,x,alpha,d=[Rat(e.Poly({tuple(int(j==k) for j in range(4)):1})) for k in range(4)]
    mean=F(1,2)-1/((r+1)*(r+2))
    # The positive saddle formula is recovered from its squared radical identity.
    e.need(((2*r+3)**2).equal(1+8/(1-2*mean)),'LDP_SADDLE_DISCRIMINANT')
    saddle_gradient=x/r-1/(r+1)+1/(2*(r+2))
    e.need(saddle_gradient.equal((x-mean)/r),'LDP_SADDLE_GRADIENT')
    e.need(mean.dby().point(F(0))==F(3,4),'LDP_ZERO_ENDPOINT_RATE')
    # At x=1/2 the r-dependent logarithms combine into
    # (1/2)log[r(r+2)/(r+1)^2], tending to zero.
    e.need((1-r*(r+2)/(r+1)**2).equal(1/(r+1)**2),'LDP_HALF_ENDPOINT_CANCELLATION')
    # (1/2-x)=O(r^-2); at zero x=O(r). The vanishing log terms require
    # the elementary analytic limits r log(r)->0 and log(r)/r^2->0.
    e.need((F(1,2)-mean).equal(1/((r+1)*(r+2))),'LDP_ENDPOINT_REMAINDER')
    # Here r is b, x is L, alpha is alpha, and d is sqrt(b^2+4alpha L).
    root=(d-r)/(2*alpha)
    residual=alpha*root**2+r*root-x
    e.need(residual.equal((d*d-r*r-4*alpha*x)/(4*alpha)),'THRESHOLD_QUADRATIC_ROOT')
    # Here x denotes n0. Rationalization proves the O(1/n0) remainder in
    # r_b=n0-b/(2alpha)+O(1/n0), without asserting a real-valued inverse.
    e.need(((d-2*alpha*x)*(d+2*alpha*x)).equal(d*d-4*alpha**2*x*x),'THRESHOLD_RATIONALIZATION')
    rational_cases=0
    for aa in [F(1,4),F(2,3),F(3,2)]:
        for bb in [F(-1,2),F(0),F(5,4)]:
            for rr in [F(3),F(10,3),F(7)]:
                LL=aa*rr*rr+bb*rr; dd=2*aa*rr+bb
                e.need(dd>0 and LL>0 and dd*dd==bb*bb+4*aa*LL,'THRESHOLD_POSITIVE_BRANCH')
                e.need((dd-bb)/(2*aa)==rr,'THRESHOLD_EXACT_ROOT')
                rational_cases+=1
    return {'rate_saddle':'r(x)=(sqrt(1+8/(1-2x))-3)/2',
            'rate_function':'x log(r/s)-log((r+1)/(s+1))+(1/2)log((r+2)/(s+2))',
            'rate_at_zero':'log(s+1)-(1/2)log(s+2)+(1/2)log(2)',
            'rate_at_half':'log(s+1)-(1/2)log(s+2)-(1/2)log(s)',
            'threshold_quadratic':'(sqrt(b^2+4alpha L)-b)/(2alpha)',
            'threshold_positive_branch_cases':rational_cases,
            'scope':'Algebra and endpoint cancellations only. The LDP, analytic endpoint limits, and two-ceiling integer threshold theorem require the proof; no real-valued o(1) inverse is asserted.'}


def run(ranges): return {'algebra':algebra(),'finite':finite(ranges),'corollaries':corollaries(),'status':'PASS','scope':'Supplementary algebra and finite checks. Analytic passage to limits, continuation, root-measure convergence and the CLT require the report proof.'}
