"""Independent finite Taylor-jet / undetermined-coefficient audit. No producer imports."""
import sympy as s
q,x,L,z=s.symbols('q x L z')
k=q+1
N=5
zero=s.Integer(0)
def deriv(pair):
    a,b=pair
    return (s.diff(a,x)+2*(x+L)*b/q,a+s.diff(b,x))
def clean(v): return tuple(s.factor(t) for t in v)
def conv(a,b):
    out=[zero]*(N+1)
    for i,av in enumerate(a):
        for j,bv in enumerate(b):
            if i+j<=N: out[i+j]+=av*bv
    return [s.expand(v) for v in out]
# Direct coefficient division, rather than a symbolic rational-series command.
u=[zero]*(N+1)
num={0:q*q,2:-q*q*x,3:q*q*(q+2)}
for r in range(N+1):
    u[r]=s.expand((num.get(r,0)-(x*u[r-2] if r>=2 else 0)+(u[r-3] if r>=3 else 0))/q)
phi=[(s.Integer(1),zero)]
sc={0:k,2:k*L}
def residual(order):
    out=[zero,zero]
    for m,v in enumerate(phi):
        # (epsilon tau)^m = epsilon^m(1+m epsilon^3/3)+O(epsilon^(m+6))
        time=[zero]*(N+1);time[m]=1
        if m+3<=N:time[m+3]=s.Rational(m,3)
        for jump,weight in [(-1,u),(q,[s.Integer(1)]+[zero]*N)]:
            # Exact dilation jet tau=1+epsilon^3/3+O(epsilon^6).
            delta=[zero,s.sympify(jump),zero,x/3,s.sympify(jump)/3,zero]
            power=[s.Integer(1)]+[zero]*N
            dv=v
            pref=conv(time,weight)
            for d in range(N-m+1):
                coeff=conv(pref,power)[order]/s.factorial(d)
                for c in range(2): out[c]+=coeff*dv[c]
                power=conv(power,delta);dv=deriv(dv)
        for r,sv in sc.items():
            if m+r==order:
                for c in range(2):out[c]-=sv*v[c]
    return clean(out)
for m in range(1,4):
    order=m+2
    R=residual(order)
    deg=max(s.degree(R[0],x),s.degree(R[1],x))+2
    aa=s.symbols('a1:'+str(deg+1));bb=s.symbols('b1:'+str(deg+1));sig=s.Symbol('sigma')
    A=sum(a*x**(i+1) for i,a in enumerate(aa));B=sum(b*x**(i+1) for i,b in enumerate(bb))
    eq0=s.expand(k*(q*s.diff(A,x,2)/2+2*(x+L)*s.diff(B,x)+B)+R[0]-sig)
    eq1=s.expand(k*(q*s.diff(A,x)+q*s.diff(B,x,2)/2)+R[1])
    eqs=s.Poly(eq0,x).all_coeffs()+s.Poly(eq1,x).all_coeffs()
    sol=s.solve(eqs,aa+bb+(sig,),dict=True)
    assert len(sol)==1 and all(t in sol[0] for t in aa+bb+(sig,))
    A,B=clean((A.subs(sol[0]),B.subs(sol[0])))
    phi.append((A,B));sc[order]=s.factor(sol[0][sig])
    print('sigma_'+str(order)+' =',sc[order])
    print('phi_'+str(m)+' =',A,'; ',B)
    # Independent full recurrence residual after inserting both new unknowns.
    assert residual(order)==(0,0)
# Check every coefficient, including the lower-order cancellations.
for r in range(N+1): assert residual(r)==(0,0), (r,residual(r))
beta=s.factor(sc[3]/k)
h1=s.factor(-3*(sc[4]/k-L**2/2))
h2=s.factor(s.Rational(3,2)*(L/3-sc[5]/k+L*beta))
e2=s.factor(L/(3*q)+s.diff(phi[1][0],x).subs(x,0)+s.diff(phi[2][1],x).subs(x,0))
assert h1==L**2*(3*q*q+27*q+23)/(45*q)
assert s.factor(h2+e2-L*(4*q**3+321*q*q+429*q+126)/(270*q))==0
print('h1 =',h1)
print('h2 =',h2)
print('e2 =',e2)
print('h2+e2 =',s.factor(h2+e2))
print('PASS: symbolic general-q recurrence through epsilon^5, unique boundary/gauge solution, c1 and c2.')
