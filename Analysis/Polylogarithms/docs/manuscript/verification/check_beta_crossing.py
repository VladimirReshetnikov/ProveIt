"""Independent scalar finite-part, Fourier-phase and chamber audits.

Imports no delivered program. Exact finite identities and numerical
quadrature diagnostics have separate scopes; the text proves all indices.
"""
from pathlib import Path
from itertools import product
import json,math,time
import sympy as s
import mpmath as mp
V=Path(__file__).resolve().parent
started=time.monotonic()
a,A,B,L,W,u=s.symbols('a A B L W u')
polynomials=[]
for m in range(1,13):
    # Affine two-vertex pushforward density differentiated m-1 times.
    p=sum(s.binomial(m-1,k)*(-1)**k*s.ff(a-1,k)*s.ff(m-a-1,m-1-k)
          *A**k*B**(m-1-k) for k in range(m))
    q=s.prod(j-a for j in range(1,m))*(A+B)**(m-1)
    assert s.Poly(s.expand(p-q),a,A,B).is_zero
    polynomials.append(dict(m=m,identity=s.sstr(s.factor(p)),passed=True))
    print('Exact affine density order',m,flush=True)
# Gamma reflection and its finite recurrence turn this exact polynomial
# into Gamma(m)*sin(pi*a)/pi. This is not an independence assumption.
jets=[]
for q in range(13):
    for parity in [0,1]:
        direct=s.diff(s.exp(u*L)*s.I*(-1)**parity*s.sin(s.pi*u*W),u,q).subs(u,0)
        closed=(-1)**parity*((L+s.I*s.pi*W)**q-(L-s.I*s.pi*W)**q)/2
        assert s.expand(direct-closed)==0
        jets.append(dict(order=q,integer_phase_parity=parity,passed=True))
# Build crossed-frequency tangent matrices directly from actual integer cuts,
# with v_d=-sum(v_1,...,v_{d-1}); compare their exact kernels with chamber sums.
chambers=[]
for d in range(2,8):
    for cuts in product([0,1],repeat=d-1):
        group=[0]
        for cut in cuts:group.append(group[-1]+cut)
        c=group[-1]+1
        for gap in [1,2,3]:
            theta=[s.Rational(2*gap*h+1,2) for h in group]
            frequency_rows=[]
            for k in range(math.floor(min(theta))+1,math.ceil(max(theta))):
                neg=[int(bool(t<k)) for t in theta]
                if any(neg) and not all(neg):frequency_rows.append([neg[j]-neg[-1] for j in range(d-1)])
            M=s.Matrix(frequency_rows) if frequency_rows else s.zeros(0,d-1)
            G=s.Matrix([[int(group[j]==h)-int(group[-1]==h) for j in range(d-1)] for h in range(c)])
            assert M.rank()==G.rank()==c-1
            assert all(G*z==s.zeros(c,1) for z in M.nullspace())
            chambers.append(dict(factors=d,occupied_chambers=c,gap=gap,rank=c-1,balanced_kernel_dimension=d-c))
assert len(chambers)==378
ZZ=s.Function('ZZ');x=s.symbols('x');moments=[]
for r in range(1,5):
    for t in range(1,5):
        m=r+t
        pol=s.Poly(s.prod(j+u for j in range(1,r))*s.prod(j-u for j in range(1,t)),u)
        for q in range(m,m+8):
            actual=0
            for shift,sign in [(t,(-1)**m),(r,(-1)**q)]:
                multiplicity=s.Poly(s.prod(x-shift+j for j in range(1,m))/s.factorial(m-1),x)
                for (j,),coefficient in multiplicity.terms():
                    power=q+1-j
                    actual+=sign*coefficient*(ZZ(power)-sum(s.Rational(1,k**power) for k in range(1,shift)))
            expected=2*(-1)**(r+1)/s.factorial(m-1)*sum(ZZ(2*k)*pol.nth(q-2*k) for k in range(1,q//2+1))
            assert s.expand(actual-expected)==0
            moments.append(dict(r=r,s=t,logarithmic_order=q,passed=True))
assert len(moments)==128
half_correction=s.simplify(s.I/(2*s.pi*s.I)*s.sin(s.pi/2)*2)
jet_correction=s.diff(s.I*s.sin(s.pi*u)/s.pi**2,u).subs(u,0)
assert half_correction==1/s.pi and jet_correction==s.I/s.pi
assert half_correction!=0 and jet_correction!=0
mp.mp.dps=90
def affine_numeric(m,aa,bb,alpha):
    beta=m-alpha;delta=min(aa,bb)/4
    normal=mp.gamma(m)/(mp.gamma(alpha)*mp.gamma(beta)*(aa+bb)**(m-1))
    def density(y):return normal*(bb-y)**(alpha-1)*(aa+y)**(beta-1)
    def coefficients(N):
        left=[mp.binomial(alpha-1,k)*(-1/bb)**k for k in range(N)]
        right=[mp.binomial(beta-1,k)*(1/aa)**k for k in range(N)]
        return [normal*bb**(alpha-1)*aa**(beta-1)*sum(left[k]*right[j-k] for k in range(j+1)) for j in range(N)]
    h=coefficients(90)
    outer=mp.quad(lambda y:density(y)/y**m,[-aa,-delta])+mp.quad(lambda y:density(y)/y**m,[delta,bb])
    def local(N):
        return sum(2*h[k]*delta**(k-m+1)/(k-m+1) for k in range(N) if (k-m)%2==0)
    fp=outer+local(80);fp2=outer+local(90)
    Q=aa**(-alpha)*bb**(-beta)
    wanted=mp.cos(mp.pi*alpha)*Q
    derivative=mp.factorial(m-1)*h[m-1]
    desired=mp.factorial(m-1)*mp.sin(mp.pi*alpha)*Q/mp.pi
    errors=[abs(fp-wanted),abs(fp-fp2),abs(derivative-desired)]
    assert all(e<mp.mpf('1e-30') for e in errors),(m,alpha,errors)
    return dict(m=m,A=str(aa),B=str(bb),alpha=str(alpha),beta=str(beta),finite_part=str(fp),closed_finite_part=str(wanted),finite_part_error=str(errors[0]),local_refinement=str(errors[1]),density_derivative_error=str(errors[2]),passed=True)
cases=[]
for m,alpha in [(1,mp.mpf('0.5')),(2,mp.mpf('0.8')),(3,mp.mpf('1.3')),(4,mp.mpf('1.2')),(5,mp.mpf('2.4')),(7,mp.mpf('3.2'))]:
    for complex_part in [mp.mpf(0),mp.mpf('0.17')]:
        cases.append(affine_numeric(m,mp.mpf(7)/5,mp.mpf(9)/4,alpha+mp.j*complex_part))
        print('Independent scalar finite part',m,'complex',bool(complex_part),'PASS',flush=True)
# Check raw principal logarithms against the crossing formula at several
# factors, sign chambers and complex balanced orders, rather than using a
# phase formula to construct both sides.
phase=[]
for theta,alpha in [([-mp.mpf('.5'),mp.mpf('.5')],[mp.mpf('.5'),mp.mpf('.5')]),
                    ([-mp.mpf('.5'),mp.mpf('.5'),mp.mpf('1.5')],[mp.mpf(1)/3]*3),
                    ([-mp.mpf('1.2'),mp.mpf('.4'),mp.mpf('2.7')],[mp.mpc('0.7','0.2'),mp.mpc('1.1','-0.3'),mp.mpc('1.2','0.1')])]:
    m=int(mp.nint(mp.re(sum(alpha))))
    assert abs(sum(alpha)-m)<mp.mpf('1e-85')
    for n in range(-5,6):
        actual=mp.fprod(mp.exp(-p*mp.log(2*mp.pi*mp.j*(n+t))) for t,p in zip(theta,alpha))
        sigma=sum((p for t,p in zip(theta,alpha) if n+t<0),mp.mpf(0))
        Q=mp.fprod(abs(n+t)**(-p) for t,p in zip(theta,alpha))
        mixture=mp.cos(mp.pi*sigma)*Q/(2*mp.pi*mp.j)**m
        correction=mp.j*mp.sin(mp.pi*sigma)*Q/(2*mp.pi*mp.j)**m
        error=abs(actual-mixture-correction)
        assert error<mp.mpf('1e-80')
        phase.append(dict(factors=len(theta),mode=n,error=str(error),passed=True))
ordinary=[]
for r,t,q in [(1,1,2),(1,1,4),(1,1,6),(1,2,3),(2,1,4),(2,2,4),(2,3,5),(3,2,6),(4,4,8)]:
    m=r+t;pol=s.Poly(s.prod(j+u for j in range(1,r))*s.prod(j-u for j in range(1,t)),u)
    expected=2*(-1)**(r+1)*mp.factorial(q)/mp.factorial(m-1)*sum(mp.zeta(2*k)*mp.mpf(str(pol.nth(q-2*k))) for k in range(1,q//2+1))
    f=lambda z:z**q*((-1)**m*mp.exp(-t*z)+(-1)**q*mp.exp(-r*z))/(-mp.expm1(-z))**m
    actual=mp.quad(f,[0,1,mp.inf]);error=abs(actual-expected)
    assert error<mp.mpf('1e-75'),(r,t,q,error)
    ordinary.append(dict(r=r,s=t,q=q,mellin_value=str(actual),finite_even_zeta_value=str(expected),absolute_error=str(error),passed=True))
out=dict(status='PASS',imports_delivered_code=False,affine_density_polynomials=polynomials,balanced_jet_checks=jets,chamber_rank_checks=chambers,ordinary_moment_coefficient_checks=moments,corruption_controls=dict(omitted_half_twist_rejected=True,omitted_balanced_first_jet_rejected=True),numerical_diagnostics=dict(working_digits=90,local_taylor_orders=[80,90],local_radius_fraction='1/4',scalar_cases=cases,principal_log_phase_cases=phase,ordinary_mellin_cases=ordinary,interval_certified=False),elapsed_seconds=round(time.monotonic()-started,3),scope='Independent exact finite density polynomials, analytic jet coefficients, actual cut-matrix kernels and binomial-multiplicity reductions. Numerical affine finite parts, principal-log phases and ordinary Mellin integrals are diagnostics, not interval certificates; the manuscript proves all-degree identities.')
(V/'beta-crossing-independent.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print('Independent beta-crossing audit PASS',flush=True)
