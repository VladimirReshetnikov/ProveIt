import sympy as s
k,v,z,u=s.symbols('k v z u',positive=True)
rho=1-v;c=k*v-k+1
# D=z d/dz with e^-z represented by u
D=lambda f:s.expand(z*(s.diff(f,z)-u*s.diff(f,u)))
K=[None,z/(1-u)]
for i in range(2,5):K.append(s.factor(D(K[-1])))
K=[None]+[s.factor(x.subs({z:k*v,u:1-v})) for x in K[1:]]
print('cumulants=',K)
s1=-1/(2*K[2])-K[3]/(2*K[2]**2)+K[4]/(8*K[2]**2)-5*K[3]**2/(24*K[2]**3)
t1=s.factor(s.Rational(13,12)/k-s.Rational(1,12)+s1)
print('t1=',t1)
Q=lambda f:s.factor(-rho*v/c*s.diff(f,v))
M=[1/c]
for i in range(1,4):M.append(Q(M[-1]))
print('M=',M)
c1=s.factor(k*rho*v/(2*c))
c2base=s.factor(-c*c*(k*(k-1)*M[3]/24-(k+2)*M[2]/24+t1*M[1])-c*c1*M[1]/2)
print('c1=',c1)
print('c2base=',c2base)
print('c2k2=',s.factor(c2base.subs(k,2)-c.subs(k,2)*v**2))
open(__import__('pathlib').Path(__file__).resolve().parent.parent / 'data' / 'coefficient_symbolics.txt','w').write('\n'.join(['K='+str(K),'t1='+str(t1),'M='+str(M),'c1='+str(c1),'c2base='+str(c2base),'c2k2='+str(s.factor(c2base.subs(k,2)-c.subs(k,2)*v**2))]))
import mpmath as mp
mp.mp.dps=50
for kk in [2,3,4]:
 vv=1+mp.lambertw(-kk*mp.exp(-kk))/kk
 t=s.lambdify((k,v),t1,'mpmath')(kk,vv)
 c2=s.lambdify((k,v),c2base,'mpmath')(kk,vv)
 if kk==2:c2-=(kk*vv-kk+1)*vv**2
 print(kk, 't1',t,'c2',c2)
