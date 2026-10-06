import sympy as s
import argparse
ap=argparse.ArgumentParser();ap.add_argument('--order',type=int,default=4);args=ap.parse_args()
q,a,y,h,z=s.symbols('q a y h z', positive=True)
x=a/q**2+y/q
def field(e):
    e=s.cancel(e)
    num,den=s.fraction(e)
    P=s.Poly(4*a**3-1,a)
    return s.cancel((s.Poly(num,a).rem(P)*s.invert(s.Poly(den,a),P)).rem(P).as_expr())
order=args.order
# Keep log q separate; polynomial normalized phase enough.
phase=3*x*(1-s.log(1+y*q/a))-s.log(1+y*q/a)
for r in range(1,(order+2)//4+1):
    phase-=s.bernoulli(2*r)/(2*r*(2*r-1)) * ((2*x)**(1-2*r)+x**(1-2*r))
for m in range(1,order+3):
    phase-=2*s.summation(h**m,(h,0,z-1)).subs(z,x)*q**(3*m)/m
phase=s.series(phase,q,0,order+1).removeO().expand()
print('phase coefficients:')
for k in range(-2,order+1):print(k,s.factor(phase.coeff(q,k)))
b=-2*a*a/3; v=a/3
# Gaussian raw moments at y mean b variance v
mom={0:s.Integer(1),1:b}
for k in range(2,3*order+4):mom[k]=s.expand(b*mom[k-1]+(k-1)*v*mom[k-2])
def expectation(p):
    p=s.Poly(s.expand(p),y)
    return field(sum(c*mom[int(m[0])] for m,c in p.terms()))
H={k:phase.coeff(q,k) for k in range(1,order+1)}
R={0:s.Integer(1)}
for k in range(1,order+1):
    R[k]=s.expand(sum(j*H[j]*R[k-j] for j in range(1,k+1))/k)
c={0:s.Integer(1)}
for k in range(1,order+1):
    c[k]=expectation(R[k]); print('c',k,c[k])
L={}
for k in range(1,order+1):
    L[k]=field(c[k]-sum(j*L[j]*c[k-j] for j in range(1,k))/k)
    print('logc',k,L[k])
# normalized moments y expanded then J=aN2+yN
momnum={r:[expectation(y**r*R[k]) for k in range(order+1)] for r in (1,2)}
E={}
for r in (1,2):
    vals={}
    for k in range(order+1):
        vals[k]=field(momnum[r][k]-sum(c[j]*vals[k-j] for j in range(1,k+1)))
    E[r]=vals
print('E y',E[1])
print('Var y',{k:field(E[2][k]-sum(E[1][j]*E[1][k-j] for j in range(k+1))) for k in range(order+1)})
