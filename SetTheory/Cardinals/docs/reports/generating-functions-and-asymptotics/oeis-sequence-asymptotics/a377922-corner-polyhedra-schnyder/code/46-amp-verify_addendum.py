"""Exact algebra checks only; limiting assertions are proved in the addendum."""
from pathlib import Path
import json
import sympy as s
ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'results'
OUT.mkdir(exist_ok=True)
p,theta,delta,t=s.symbols('p theta delta t', positive=True)
CB=2**(1-p)/(theta*s.gamma(p+1)*s.sqrt(delta))
beta=2**(1-p/2)*s.gamma(p/2)/(s.pi*s.gamma(p))
# Angular and radial integrals with theta*p=pi and physical Jacobian sqrt(delta).
angular=s.Rational(2)/p
radial=2**(p/2)*t**(p/2+1)*s.gamma(p/2+1)
survival=s.simplify((CB*t**(-p-1)*s.sqrt(delta)*angular*radial).subs(theta,s.pi/p))
assert s.simplify(survival-beta*t**(-p/2))==0
# Semigroup-reduced entrance-density integral at a general positive split s0.
s0=s.symbols('s0', positive=True)
integral=CB**2*s.sqrt(delta)*theta*s.gamma(p+1)/4*(2*s0)**(-p-1)*s0**(-p-1)*(4*s0/3)**(p+1)
assert s.simplify(s.powsimp(integral/(CB*(3*s0)**(-p-1)),force=True))==1
# Multiplying two cycle-normalization factors 2^(p/2) produces the pullback coefficient.
assert s.simplify(2*CB*2**p-4/(theta*s.gamma(p+1)*s.sqrt(delta)))==0
SP=s.Matrix([[s.Rational(16,5),-s.Rational(9,5)],[-s.Rational(9,5),s.Rational(16,5)]])
SS=s.Matrix([[s.Rational(36,7),-s.Rational(88,21)],[-s.Rational(88,21),s.Rational(36,7)]])
assert SP.det()==7 and SS.det()==s.Rational(80,9)
assert s.simplify(CB.subs({p:1,theta:s.pi,delta:1}))==1/s.pi
assert s.simplify(beta.subs(p,1))==s.sqrt(2/s.pi)
assert s.simplify(CB.subs({p:2,theta:s.pi/2,delta:1}))==1/(2*s.pi)
assert s.simplify(beta.subs(p,2))==1/s.pi
mu=s.Rational(16,3)
assert (mu/4)*(1+1/mu)**2==s.Rational(361,192)
assert (1+1/mu)**-3==s.Rational(16,19)**3
z=s.symbols('z')
series=s.series((1+z)**-3,z,0,25).removeO()
assert all(series.coeff(z,j)==(-1)**j*s.binomial(j+2,2) for j in range(25))
# The signed-convolution inequality is algebraically exact for 0<=j<=n.
n,j=s.symbols('n j', integer=True, nonnegative=True)
assert s.expand((j+1)*(n-j+1)-n)==s.expand(j*(n-j)+1)
# Inverse transformation in logarithms, with positive parameters and eta>1
# selecting the large branch. Positivity makes the expanded logarithms valid.
alpha,lam,gamma,eta=s.symbols('alpha lam gamma eta', positive=True)
r=alpha*eta/lam
logY=s.log(gamma)+lam*r-alpha*s.log(r)
log_abs_argument=s.expand_log(s.log(lam/alpha)+(s.log(gamma)-logY)/alpha,force=True)
assert s.simplify(log_abs_argument-(s.log(eta)-eta))==0
# Therefore the Lambert argument equals -eta*exp(-eta), whose W_-1 is -eta for eta>1.
report={
 'status':'PASS', 'arithmetic':'exact symbolic and rational',
 'brownian_survival_normalization':'PASS',
 'entrance_semigroup_integral':'PASS',
 'cycle_to_physical_harmonic_factor':'PASS',
 'covariance_determinants':{'P':'7','S':'80/9'},
 'half_plane_normalization':{'C_B':'1/pi','beta_B':'sqrt(2/pi)'},
 'quadrant_normalization_u_2xy':{'C_B':'1/(2*pi)','beta_B':'1/pi'},
 's_amplitude_from_fixed_endpoint':'361/192',
 'rigid_to_s_amplitude':'4096/6859 = (16/19)^3',
 'signed_inverse_cubic_coefficients_checked':25,
 'convolution_majorant_identity':'(j+1)(n-j+1)-n = j(n-j)+1',
 'Lambert_inverse_log_identity':'PASS; the real branch W_-1 is selected by eta>1',
 'scope':'Algebraic normalization checks only. No numerical counting amplitude, limiting theorem, convergence rate, or rounding rule is certified by finite computation.'
}
(OUT/'addendum-symbolic-checks.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
