import sympy as s
x,z,t=s.symbols('x z t'); b=1-x
D=(b*(z-b)+x*t*(x-z))**2-4*x*t*(1-z)*b*z
P=z**3-5*z**2+6*z-1
rho=3*z*z-10*z+2
red=lambda f:s.factor(s.rem(s.rem(s.together(f).as_numer_denom()[0],P,z)*s.invert(s.rem(s.together(f).as_numer_denom()[1],P,z),P,z),P,z))
sub=lambda f:f.subs(t,1/z).subs(x,rho)
op=lambda f:-z*s.diff(f,z)+t*s.diff(f,t)
alpha=red(sub(z*s.diff(D,z)/(x*s.diff(D,x))))
v=red(sub(op(op(D))/(x*s.diff(D,x))))
nu=red(v/alpha)
print('rho=',rho,'alpha=',alpha,'v=',v,'nu=',nu)
print('−zc*D_z=',red(sub(-z*s.diff(D,z))))
print('−rho*D_x=',red(sub(-x*s.diff(D,x))))
print('Cq² π=',red(sub(-z*s.diff(D,z)/(16*x*x*t*t*(1-z)**2))))
print('Cℓ² π=',red(sub(-x*s.diff(D,x)/(16*x*x*t*t*(1-z)**2))))
for label,f in [('rho',rho),('alpha',alpha),('v',v),('nu',nu)]:
 print(label,s.N(f.subs(z,s.CRootOf(P,0)),30))
ops=[lambda f:z*s.diff(f,z),op]
lx=lambda f:x*s.diff(f,x)
means=[alpha,s.Integer(0)]
Sigma=s.Matrix(2,2,lambda i,j:red(sub(ops[i](ops[j](D))-ops[i](lx(D))*means[j]-ops[j](lx(D))*means[i]+lx(lx(D))*means[i]*means[j])/sub(lx(D))))
print('Sigma=',Sigma)
print('detSigma=',red(Sigma.det()))
print('q_cond_d_var=',red(Sigma.det()/v))
print('d_cond_q_var=',red(Sigma.det()/Sigma[0,0]))
print('Sigma numeric=',Sigma.subs(z,s.CRootOf(P,0)).evalf(20))
kappa=red((-21*alpha**2+17*alpha+5)/29)
print('kappa=',kappa)
Cq=s.sqrt(-16*z*z+55*z-10)/(2*s.sqrt(s.pi))
Cl=s.sqrt(7*z*z-24*z+5)/(2*s.sqrt(s.pi))
C_joint=Cl/(s.sqrt(2*s.pi*v))
print('Cq',s.N(Cq.subs(z,s.CRootOf(P,0)),30))
print('Cl',s.N(Cl.subs(z,s.CRootOf(P,0)),30))
print('Cjoint',s.N(C_joint.subs(z,s.CRootOf(P,0)),30))
print('Cstar',s.N((3*s.pi**2*alpha**2/(2*v)).subs(z,s.CRootOf(P,0))**s.Rational(1,3),30))
# Independent Stirling-amplitude check.
a,d,u=s.symbols('a d u',positive=True)
L=lambda y:y*s.log(y)
S=2*L(a+u)-L(a)-2*L(u)-L(d-u)-L(a-d+u)+L(1+a)-L(1-d-u)-L(a+d+u)
T0=s.sqrt(a*(1-d-u)*(a+d+u))/((2*s.pi)**2*u*u*s.sqrt((d-u)*(a-d+u))*(1+a)**s.Rational(3,2))
Suu=s.diff(S,u,2)
pt={a:alpha,d:alpha,u:kappa}
stirling=T0.subs(pt)*s.sqrt(2*s.pi/(-Suu.subs(pt)))/(1-z)
algebraic=Cl/(2*s.pi*s.sqrt(Sigma.det()))
print('local constant by Stirling',s.N(stirling.subs(z,s.CRootOf(P,0)),20))
print('local constant by algebraic',s.N(algebraic.subs(z,s.CRootOf(P,0)),20))
print('q_shift_coefficient',red(Sigma[0,1]/v))
# Exact independent entropy-Hessian verification.
w=s.symbols('w')
St=S.subs(d,a+w)
H=s.hessian(St,(a,w,u)).subs({a:alpha,w:0,u:kappa}).applyfunc(red)
den=red((-H).det())
Hi=(-H).adjugate().applyfunc(red).applyfunc(lambda e:red(e/den))
assert all(red(Hi[i,j]-Sigma[i,j])==0 for i in range(2) for j in range(2))
amp_ratio_square=s.cancel((T0**2*2*s.pi/(-Suu)).subs(pt)/(1-z)**2 / (Cl**2/(4*s.pi**2*Sigma.det())))
assert red(amp_ratio_square-1)==0
assert red(alpha*nu-v)==0
print('PASS: exact entropy Hessian, Stirling amplitude and ν α=v checks')
