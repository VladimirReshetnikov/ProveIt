import sympy as s
N=9
d,t=s.symbols('d t'); q=1-d
tr=lambda x:s.series(x,d,0,N).removeO().expand()
Q=[s.Integer(1),s.Integer(2)]
for j in range(1,(N+1)//2+1): Q.append(s.expand(2*Q[-1]-(1-q**j)**2*Q[-2]))
h=s.Rational(1,2); pp=s.Integer(1)
for j in range(1,(N+1)//2):
 pp=tr(pp*(1-q**j)**2)
 h-=tr(pp/(Q[j]*Q[j+1]))
T=s.Integer(1); term=s.Integer(1)
for j in range(N-1):
 term=tr(-term*q**j*(1-q**(j+1))/(1+q**(2*j+3)))
 T+=term
F=tr(4*h*T/(1+q))
print('h(delta)=',h.expand())
print('T(delta)=',T.expand())
print('4 h T/(1+q)=',F)
Ft=s.series(F.subs(d,1-s.exp(-t))*s.exp(-t/6),t,0,N)
print('normalized GF multiplier(t)=',Ft)
print('without modular e(-t/6)=',s.series(F.subs(d,1-s.exp(-t)),t,0,N))

expected=list(map(s.Rational,['1','-1/6','-35/72','755/1296','-29375/31104','1772639/933120','-31514551/6718464','3808743271/282175488','-85931514901/1934917632']))
if tr(T/(1+q)-h)!=0: raise RuntimeError('h and alternating multiplier expansions differ')
actual=[Ft.removeO().expand().coeff(t,j) for j in range(N)]
if actual!=expected: raise RuntimeError('normalized multiplier coefficients differ')
print('All multiplier coefficient checks pass')
