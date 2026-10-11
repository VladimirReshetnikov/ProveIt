"""Independent normalization and primary-source correction certificates."""
from pathlib import Path
from fractions import Fraction as Q
import json,math
import sympy as S
V=Path(__file__).resolve().parent
G,Z2,Z3,Z4,G1,Eta,Theta,Chi,Om,JP,Z2p,Z3p=S.symbols('gamma z2 z3 z4 gamma1 eta theta chi Omega4 Jprime zeta2prime zeta3prime')
raw=30*G**2*Z2-60*G*Z3+S.Rational(35,3)*Z4-120*Chi+120*G*Theta+60*(Z2-G**2)*Eta-20*(G**3-3*G*Z2+Z3)*G1+10*Om+10*Z2*Z2p-20*G*Z3p
compact=30*G**2*Z2-60*G*Z3+S.Rational(35,3)*Z4-120*Chi+120*G*Theta-60*(G**2-Z2)*Eta-20*(G**3-3*G*Z2+2*Z3)*G1+10*JP
change=Om+2*Z3*G1-2*G*Z3p+Z2*Z2p
assert S.expand(raw-compact.subs(JP,change))==0
wrong=S.expand(raw-compact.subs(JP,change-2*Z3*G1));assert wrong==20*Z3*G1
Q2=2*G1-2*Z2;Q3=3*Z2-6*Eta-6*G*G1;Q4=12*Z3-12*G*Z2+18*Z4+4*Z3p-24*Theta+24*G*Eta+12*(G**2-Z2)*G1
comb=S.expand(raw+5*G*Q4+10*(G**2+Z2)*Q3+10*(G**3+3*G*Z2+Z3)*Q2)
for symbol in [Theta,Eta,G1,Z3p]:assert comb.coeff(symbol)==0
expected=-120*Chi+10*Om+10*Z2*Z2p+S.Rational(260,3)*Z4-60*G*Z4-20*G**3*Z2-20*Z2*Z3
assert S.expand(comb.subs(Z2**2,S.Rational(5,2)*Z4)-expected)==0
assert S.expand(10*Z3*Q2-(20*Z3*G1-20*Z2*Z3))==0
regcomb=S.expand(compact+5*G*Q4+10*(G**2+Z2)*Q3+10*(G**3+3*G*Z2+2*Z3)*Q2)
for symbol in [Theta,Eta,G1]:assert regcomb.coeff(symbol)==0
assert S.expand(regcomb.subs(JP,change)-comb-10*Z3*Q2)==0
z,r=S.symbols('z r');N=16;poly=S.Integer(1);rhos=[]
for n in range(1,N+1):
 poly=S.expand(poly*(r+n-1));rho=S.integrate(poly,(r,0,1))/math.factorial(n-1);assert rho>0 and rho<=n;rhos.append(rho)
f=S.series(-z/((1-z)*S.log(1-z)),z,0,N+1).removeO();h=S.series(S.log(-S.log(1-z)/z),z,0,N+1).removeO()
for n,rho in enumerate(rhos,1):assert S.expand(f).coeff(z,n)==rho/n and S.expand(h).coeff(z,n)==rho/n**2
# Exact rational log intervals, with the geometric atanh remainder.
def log_bounds(n,K=128):
 q=Q(n-1,n+1);val=sum((2*q**(2*k+1)/Q(2*k+1) for k in range(K)),Q(0));tail=2*q**(2*K+1)/Q(2*K+1)/(1-q*q);return val,val+tail
Ncut=10;bounds=[log_bounds(n) for n in range(1,Ncut+1)];loL,hiL=bounds[-1];assert loL>Q(3,2)
slo=sum((p[0]/Q(n) for n,p in enumerate(bounds,1)),Q(0));shi=sum((p[1]/Q(n) for n,p in enumerate(bounds,1)),Q(0))
# gamma1 = sum_{n<=N} log(n)/n - log(N)^2/2 - log(N)/(2N)
#          + (log(N)-1)/(12 N^2) + R;
# |R| <= (log(N)-1)/(12 N^2), since f''=(2 log x-3)/x^3 >=0 for x>=N.
c_lo=slo-hiL**2/2-hiL/Q(2*Ncut)+(loL-1)/Q(12*Ncut**2)
c_hi=shi-loL**2/2-loL/Q(2*Ncut)+(hiL-1)/Q(12*Ncut**2)
rad=(hiL-1)/Q(12*Ncut**2);lower=c_lo-rad;upper=c_hi+rad
assert -Q(3,40)<lower<upper<-Q(7,100)
record=dict(status='PASS',fifth_coordinate_identity=True,missing_stieltjes_control=str(wrong),fifth_polynomial_cancellations=4,canonical_fifth_scalar_verified=True,regular_pole_polynomial_difference_verified=True,positive_Cauchy_coefficients_checked=N,independent_binomial_and_log_series_equalities=2*N,gamma1_sign_certificate=dict(N=Ncut,atanh_terms=128,exact_lower=str(lower),exact_upper=str(upper),simple_lower='-3/40',simple_upper='-7/100',error_bound=str(rad),method='One Euler-Maclaurin correction, periodic Bernoulli remainder <= integral |f second derivative|/12, and exact rational atanh log intervals.'),source_index_counterexample=dict(m=0,a=1,printed_limit_minus_correct_limit=-1),scope='Independent exact coordinate conversion and polynomial cancellation, with a rejected missing-Stieltjes correction; finite rational Cauchy identities; rigorous negative gamma1 enclosure supporting the primary-source coefficient-description counterexample. Infinite identities and all-depth sign reversal rest on the manuscript proofs.')
(V/'digamma-coordinate-source-audit.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8');print('Independent coordinate, Cauchy and source-sign audits: PASS')
