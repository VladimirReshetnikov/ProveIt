"""Independent exact algebra for the proportional-mask TV correction.

This reconstructs the density polynomials from Gamma cumulants and a general
fixed slack's first two moments. It imports no other verification scripts.
SymPy is used only for polynomial identities, never numerical tolerances.
"""
import sympy as s

eta = s.symbols('eta', positive=True)
z, c, y = s.symbols('z c y', real=True)
vH, vO, bs, ws = s.symbols('vH vO bs ws', real=True)
alpha = 1-eta  # The mathematical domain is 0 < eta < 1.
H = s.hermite_prob
A0 = lambda x: H(3,x)/3
B0 = lambda x: H(4,x)/4+H(6,x)/18
Q1 = A0(z)/s.sqrt(alpha)
Q2 = (B0(z)+vO*H(2,z)/2)/alpha

# The slack is centered at zero relative to the hidden-block mean, so its
# raw second moment is ws+bs**2. This also reconstructs Exp(1) by bs=ws=1.
AH = lambda x: A0(x)+bs*x
BH = lambda x: B0(x)+bs*H(4,x)/3+(vH+ws+bs**2)*H(2,x)/2
W1 = -alpha**s.Rational(3,2)*z**3/(3*eta**2)-(bs-1)*s.sqrt(alpha)*z/eta
W2 = BH(s.sqrt(alpha/eta)*z)/eta
normal = s.Rational(1,12)-bs+(vH+vO+ws+bs**2)/2
P2 = s.expand(Q2+W2+Q1*W1+normal)

# Reconstruct the even Hermite basis. The constant coefficient must be zero.
remaining = s.Poly(s.simplify(P2.subs(z,s.sqrt(eta)*y)),y)
coefficients = {}
for degree in (6,4,2,0):
    value = s.factor(remaining.coeff_monomial(y**degree))
    coefficients[degree] = value
    remaining = s.Poly(s.expand(remaining.as_expr()-value*H(degree,y)),y)
if coefficients[0] != 0 or remaining.as_expr() != 0:
    raise RuntimeError('Second-order density is not normalized')

# Gaussian boundary integration, divided by phi(c). At the leading crossing,
# phi_eta(c)=phi(c). All Hermite degrees here are positive and even.
P_integral = -2*s.sqrt(eta)*sum(
    coefficients[j]*H(j-1,c/s.sqrt(eta)) for j in (2,4,6))
Q_integral = -2*(vO*H(1,c)/(2*alpha)+H(3,c)/(4*alpha)+H(5,c)/(18*alpha))
# The two moving endpoints together contribute the following positive term.
endpoint = s.simplify(W1.subs(z,c)**2*eta/(c*alpha))
expected = c*(vO-alpha*vH/eta
    +(2*c**4-c**2-3*eta*alpha)/(18*eta**2)
    +(bs-1)**2+2*(bs-1)*c**2/(3*eta)-alpha*(ws-1)/eta)
if s.factor(P_integral-Q_integral+endpoint-expected) != 0:
    raise RuntimeError('TV coefficient mismatch')

# The exponential slack's second positive crossing displacement.
w1 = W1.subs({bs:1,ws:1})
bb = (W2+normal).subs({bs:1,ws:1})
first_shift = -s.sqrt(alpha)*c**2/(3*eta)
gprime, gsecond = -alpha*c/eta, -alpha/eta
second_shift = s.factor(-(
    gsecond*first_shift**2/2+s.diff(w1,z).subs(z,c)*first_shift
    +bb.subs(z,c)-w1.subs(z,c)**2/2)/gprime)
expected_shift = alpha*c**3/(36*eta**2)-1/(12*c) \
    +vH*c/(2*eta)-vH/(2*c)+eta*vO/(2*alpha*c)
if s.factor(second_shift-expected_shift) != 0:
    raise RuntimeError('Second crossing displacement mismatch')

# Check the explicit polynomial form of the c=1 Gamma perturbation.
x=s.symbols('x',real=True)
A1=A0(x)+x
B1=B0(x)+x*A0(x)
if s.expand(A1-x**3/3)!=0:
    raise RuntimeError('Gamma shape m+1 first correction mismatch')
if s.expand(B1-(x**6/18-x**4/4-s.Rational(1,12)))!=0:
    raise RuntimeError('Gamma shape m+1 second correction mismatch')

print('PASS: Gamma correction polynomials, density normalization, general-slack TV coefficient,')
print('exponential-slack TV coefficient, moving-endpoint term, and second crossing displacement.')
