import sympy as S
from itertools import product
q=5;h=3;sig=S.Integer(2);steps=[-2,-1,0,1,2];ss=steps[:h]
r=(-3+S.sqrt(5))/2
u=S.symbols('u');P=sum(u**s for s in steps);Pr=S.simplify(S.diff(P,u).subs(u,r));Prr=S.simplify(S.diff(P,u,2).subs(u,r))
v=[-S.Rational(s,q)/sig for s in ss]
v2=S.Matrix(h,h,lambda i,j: S.simplify(-((ss[i] if i==j else 0)+ss[i]**2*v[j]+ss[j]**2*v[i])/(q*sig)))
lam2=S.Matrix(h,h,lambda i,j:S.KroneckerDelta(i,j)-S.Rational(ss[i]*ss[j],q)/sig)
H=lam2/q-S.ones(h,h)/q**2;C=H.inv()
k3={}
for i,j,k in product(range(h),repeat=3):
 l3=int(i==j==k)+(ss[i]*v[k] if i==j else 0)+(ss[i]*v[j] if i==k else 0)+(ss[j]*v[i] if j==k else 0)+ss[i]**2*v[j]*v[k]+ss[j]**2*v[i]*v[k]+ss[k]**2*v[i]*v[j]
 k3[i,j,k]=S.simplify(l3/q-(lam2[i,j]+lam2[i,k]+lam2[j,k])/q**2+S.Rational(2,q**3))
r1=[S.simplify((1-r**s)/Pr) for s in ss]
r2=S.Matrix(h,h,lambda i,j:S.simplify((lam2[i,j]-(r**ss[i] if i==j else 0)-ss[i]*r**(ss[i]-1)*r1[j]-ss[j]*r**(ss[j]-1)*r1[i]-Prr*r1[i]*r1[j])/Pr))
g1=[S.simplify(S.Rational(1,q)+v[i]+r1[i]/r-int(i==0)) for i in range(h)]
g2=S.Matrix(h,h,lambda i,j:S.simplify(H[i,j]+v2[i,j]+r2[i,j]/r-r1[i]*r1[j]/r**2))
E2=g2+S.Matrix(g1)*S.Matrix(g1).T
b1=[-S.Rational(1,2)*(s*s-sig)/(q*sig) for s in ss]
amp=-S.Rational(1,2)*sum(E2[i,j]*C[i,j]+2*b1[i]*g1[j]*C[i,j] for i,j in product(range(h),repeat=2))
amp+=S.Rational(1,2)*sum(g1[i]*k3[j,k,l]*C[i,j]*C[k,l] for i,j,k,l in product(range(h),repeat=4))
alpha2=S.Rational(2*q,1)/S.diff(P,u,2).subs(u,1)
beta=-S.diff(P,u,3).subs(u,1)*alpha2/(6*S.diff(P,u,2).subs(u,1))
c2=beta+1+q/(r*Pr)
univ=S.simplify(-S.Rational(3,2)*c2+alpha2/2)
amp=S.simplify(amp);delta=S.simplify(univ+amp)
# ratio to Ecrit/(qn) * multinomial: coefficient of 1/n = delta/q.
# multinomial relative Stirling coefficient is (1/q-q)/12n.
ratio=S.simplify(delta/q);full=S.simplify(ratio+(S.Rational(1,q)-q)/12)
for k,z in [('H',H),('detH',H.det()),('g1',g1),('g2',g2),('univariate_difference_Ninv',univ),('saddle_difference_Ninv',amp),('fixed_content_ratio_ninv',ratio),('full_relative_ninv',full)]:print(k,':',z, ' approx ', z.evalf() if hasattr(z,'evalf') else '')
