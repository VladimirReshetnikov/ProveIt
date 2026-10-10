from pathlib import Path
import sympy as s
u,z,t,l=s.symbols('u z t lambda')
g1,g2,g3,c,d,e=s.symbols('g1 g2 g3 c d e')
# z=1/m; n=(m+1)t-1. Expansion S0+z*S1+z**2*S2.
x=l*z*s.exp(-u)
S0=l*s.exp(-u)*(c+g1*t/(t+u))
S1=(l*s.exp(-u)*g1*(t-1)/(t+u)
      +l*l*s.exp(-2*u)*(d+t*(g2/(t+u)-g1*g1/(2*(t+u)**2))))
S2=(l*l*s.exp(-2*u)*(t-1)*(g2/(t+u)-g1*g1/(2*(t+u)**2))
      +l**3*s.exp(-3*u)*(e+t*(g3/(t+u)-g1*g2/(t+u)**2+g1**3/(3*(t+u)**3))))
# E U^2=t*z-t*z^2+..., EU^3=2t*z^2+..., EU^4=3t^2*z^2+...
# R/e^(lambda delta)=h0 + z*h1 + z^2*h2 with derivatives of h0 to4.
D0=[s.simplify(s.diff(S0,u,j).subs(u,0)) for j in range(1,5)]
D1=[s.simplify(s.diff(S1,u,j).subs(u,0)) for j in range(0,3)]
a1,a2,a3,a4=D0
b0,b1,b2=D1
C1=s.expand(b0+t*(a2+a1*a1)/2)
C2=s.expand(S2.subs(u,0)+b0*b0/2-t*(a2+a1*a1)/2
            +t*(b2+2*a1*b1+(a2+a1*a1)*b0)/2
            +t*(a3+3*a1*a2+a1**3)/3
            +t*t*(a4+4*a1*a3+3*a2*a2+6*a1*a1*a2+a1**4)/8)
C1=s.factor(C1)
C2=s.collect(s.factor(C2),l)
print('General C1:',C1)
print('General C2:',C2)
# e=coefficient log[B/(a*x)] degree3=zeta4/(4a)-c*zeta3/(3a)+c**3/3;
# retain g3=-zeta3/3=-a*(d+c*c/2), e independent.
a=s.symbols('a')
gamma_sub={g1:-a,g2:a*c,g3:-a*(d+c*c/2)}
G1=s.factor(C1.subs(gamma_sub))
G2=s.expand(C2.subs(gamma_sub))
delta,eps=s.symbols('delta epsilon')
eta=e+a**3/2-a*a*delta/2+a*delta*delta/2-5*a*eps
claim1=t*delta*l*(1+delta*l)/2-2*a*l+eps*l*l
claim2=(l*(delta*t*t/8-(a+5*delta/6)*t)
 +l*l*(7*delta*delta*t*t/8+(-3*a*delta-3*delta*delta/2+2*eps)*t+15*a*a/2+3*a*delta)
 +l**3*(3*delta**3*t*t/4+(-a*delta*delta-delta**3/3+5*delta*eps/2)*t+eta)
 +l**4*(delta**4*t*t/8+delta*delta*eps*t/2+eps*eps/2))
sub={c:delta+a,d:eps-a*a}
assert s.expand(G1.subs(sub)-claim1)==0
assert s.expand(G2.subs(sub)-claim2)==0
print('PASS: independent centered-gamma derivation agrees with P1 and P2 exactly.')
print('Gamma C1:',G1)
for degree in range(1,5):print('Gamma C2 coefficient lambda^',degree,':',s.factor(G2.coeff(l,degree)))
Path(__file__).with_name('correction_symbolic.txt').open('w').write('General C1: '+str(C1)+'\nGeneral C2: '+str(C2)+'\nGamma C1: '+str(G1)+'\nGamma C2: '+str(s.collect(G2,l))+'\n')
