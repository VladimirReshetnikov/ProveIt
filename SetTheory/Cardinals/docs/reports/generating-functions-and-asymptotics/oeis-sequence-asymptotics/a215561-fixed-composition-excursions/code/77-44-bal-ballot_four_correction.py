import sympy as S
from itertools import product
q=4;h=2;sig=S.Integer(5);steps=[-3,-1,1,3];ss=steps[:h]
u,t=S.symbols('u t');T=t**4-2*t**3-2*t**2-2*t+1
alpha=-2*t/(1+t);g=u*u-alpha*u+t
P=sum(u**s for s in steps);Pr=S.diff(P,u);Prr=S.diff(P,u,2)
def red(f):
 nu,de=S.fraction(S.cancel(f));nu=S.rem(nu,T,t);de=S.rem(de,T,t)
 return S.rem(nu*S.invert(de,T,t),T,t).expand()
def trace(f):
 nu,de=S.fraction(S.cancel(f));nu=S.rem(nu,g,u);de=S.rem(de,g,u)
 z=S.rem(nu*S.invert(de,g,u),g,u)
 return red(S.diff(z,u)*alpha+2*z.subs(u,0))
v=[-S.Rational(s,q)/sig for s in ss]
v2=S.Matrix(h,h,lambda i,j: -((ss[i] if i==j else 0)+ss[i]**2*v[j]+ss[j]**2*v[i])/(q*sig))
lam2=S.Matrix(h,h,lambda i,j:S.KroneckerDelta(i,j)-S.Rational(ss[i]*ss[j],q)/sig)
H=lam2/q-S.ones(h,h)/q**2;C=H.inv()
k3={}
for i,j,k in product(range(h),repeat=3):
 l3=int(i==j==k)+(ss[i]*v[k] if i==j else 0)+(ss[i]*v[j] if i==k else 0)+(ss[j]*v[i] if j==k else 0)+ss[i]**2*v[j]*v[k]+ss[j]**2*v[i]*v[k]+ss[k]**2*v[i]*v[j]
 k3[i,j,k]=S.simplify(l3/q-(lam2[i,j]+lam2[i,k]+lam2[j,k])/q**2+S.Rational(2,q**3))
r1=[S.cancel((1-u**s)/Pr) for s in ss]
r2=S.Matrix(h,h,lambda i,j:S.cancel((lam2[i,j]-(u**ss[i] if i==j else 0)-ss[i]*u**(ss[i]-1)*r1[j]-ss[j]*u**(ss[j]-1)*r1[i]-Prr*r1[i]*r1[j])/Pr))
g1=[red(S.Rational(1,q)+v[i]+trace(r1[i]/u)-int(i==0)) for i in range(h)]
g2=S.Matrix(h,h,lambda i,j:red(H[i,j]+v2[i,j]+trace(r2[i,j]/u-r1[i]*r1[j]/u**2)))
E2=g2+S.Matrix(g1)*S.Matrix(g1).T
b1=[-S.Rational(1,2)*(s*s-sig)/(q*sig) for s in ss]
amp=-S.Rational(1,2)*sum(E2[i,j]*C[i,j]+2*b1[i]*g1[j]*C[i,j] for i,j in product(range(h),repeat=2))
amp+=S.Rational(1,2)*sum(g1[i]*k3[j,k,l]*C[i,j]*C[k,l] for i,j,k,l in product(range(h),repeat=4))
alpha2=S.Rational(2*q,1)/S.diff(P,u,2).subs(u,1)
beta=-S.diff(P,u,3).subs(u,1)*alpha2/(6*S.diff(P,u,2).subs(u,1))
c2=beta+1+q*trace(1/(u*Pr))
univ=red(-S.Rational(3,2)*c2+alpha2/2)
amp=red(amp);delta=red(univ+amp)
ratio=red(delta/q);full=red(ratio+(S.Rational(1,q)-q)/12)
phi=(1+S.sqrt(5))/2;t0=phi-S.sqrt(phi)
for k,z in [('H',H),('detH',H.det()),('g1',g1),('g2',g2),('univariate_difference_Ninv',univ),('saddle_difference_Ninv',amp),('fixed_content_ratio_ninv',ratio),('full_relative_ninv',full)]:print(k,':',z, ' approx ', z.subs(t,t0).evalf() if hasattr(z,'evalf') else '')
