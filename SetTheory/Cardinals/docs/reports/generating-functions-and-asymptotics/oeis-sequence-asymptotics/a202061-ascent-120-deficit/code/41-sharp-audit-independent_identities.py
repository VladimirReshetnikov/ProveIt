"""Independent identities needed by the sharp-deficit audit (no global transfer theorem)."""
import sympy as S
z = S.symbols('z')
p = z**3-5*z**2+6*z-1

def red(e):
    num, den = S.cancel(e).as_numer_denom()
    return S.factor(S.rem(S.rem(num,p,z)*S.invert(S.rem(den,p,z),p,z),p,z))

alpha=(8*z*z-29*z+9)/7
kappa=(17*z*z-59*z+13)/7
rho=3*z*z-10*z+2
v=(2*z*z-7*z+2)/2

# Entropy is independently assembled from the four binomial factors.
a,b,u,w=S.symbols('a b u w', positive=True)
L=lambda x:x*S.log(x)
E=2*(L(a+u)-L(a)-L(u)) + L(a)-L(b-u)-L(a-b+u) + L(1+a)-L(1-b-u)-L(a+b+u)
point={a:alpha,b:alpha,u:kappa}
# Rational forms of exponentiated gradient, directly from the factorial arguments.
expEa=(a+u)**2*(1+a)/(a*(a-b+u)*(a+b+u))
expEb=(a-b+u)*(1-b-u)/((b-u)*(a+b+u))
expEu=(a+u)**2*(b-u)*(1-b-u)/(u*u*(a-b+u)*(a+b+u))
assert red((expEa*expEb).subs(point)-1)==0
assert red(expEb.subs(point)-z)==0
assert red(expEu.subs(point)-1)==0
assert red(rho-(1-alpha-kappa)/(1+alpha))==0
# Euler identity recovers critical entropy normalization from these gradients.
assert S.simplify(S.expand_log(E-a*S.diff(E,a)-b*S.diff(E,b)-u*S.diff(E,u)-S.log((1+a)/(1-b-u)),force=True))==0

Ec=E.subs(b,a+w)
H=S.hessian(Ec,(a,w,u)).subs({a:alpha,w:0,u:kappa}).applyfunc(red)
G=(-H).adjugate().applyfunc(red).applyfunc(lambda x:red(x/red((-H).det())))
assert red(G[1,1]-v)==0
beta=red(G[0,1]/v)
expected_beta=-4*(z-3)*(2*z-1)/7
assert red(beta-expected_beta)==0
# Principal minors certify strict local concavity once signs are checked at z_*.
minors=[red((-H)[:j,:j].det()) for j in (1,2,3)]
zstar=S.CRootOf(p,0)
lo,hi=S.Poly(p,z).intervals(eps=S.Rational(1,10**20))[0][0]
def lower_bound(e):
    terms=S.Poly(red(e),z).terms()
    return sum(c*(lo**degree[0] if c>=0 else hi**degree[0]) for degree,c in terms)
assert all(lower_bound(x)>0 for x in minors)
assert all(lower_bound(x)>0 for x in [alpha,kappa,alpha-kappa,1-alpha-kappa,rho,1-rho,v])

# Independently implicit-differentiate the positive-kernel discriminant.
x,Z,t=S.symbols('x Z t')
bb=1-x
D=(bb*(Z-bb)+x*t*(x-Z))**2-4*x*t*(1-Z)*bb*Z
at=lambda e:e.subs({x:rho,Z:z,t:1/z})
K=lambda e:-Z*S.diff(e,Z)+t*S.diff(e,t)
assert red(at(D))==0
assert red(at(K(D)))==0
assert red(at(Z*S.diff(D,Z))-alpha*at(x*S.diff(D,x)))==0
assert red(at(K(K(D)))-v*at(x*S.diff(D,x)))==0

print('PASS: entropy stationarity and critical normalization')
print('PASS: marginal height covariance =',v)
print('PASS: conditional q saddle coefficient =',expected_beta)
print('PASS: three positive principal minors of -H at z_*')
print('PASS: discriminant identities for Psi_s=1/alpha and Psi_theta_theta=v/alpha')
print('alpha =',S.N(alpha.subs(z,zstar),30))
print('v =',S.N(v.subs(z,zstar),30))
print('C_* =',S.N(((3*S.pi**2*alpha**2/(2*v))**S.Rational(1,3)).subs(z,zstar),30))
