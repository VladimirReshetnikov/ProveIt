"""Independent coefficient generator through n^-1, using formal root powers.

No use of the hand-expanded H1 or Fourier correction in first_correction.py.
"""
import sympy as S
import mpmath as M
import json, math
from pathlib import Path
M.mp.dps=55
k,x,z,r,c,e,h,u=S.symbols('k x z r c e h u')
p={1:k*(k-1)/2,2:k*(k-1)*(4*k-5)/6,
   3:k*(k-1)*(9*k*k-25*k+18)/8,
   4:k*(k-1)*(64*k**3-291*k*k+459*k-251)/30}
logR=sum(-p[j].subs(k,x/e)*e**(2*j)/j*(1+z*e)**(-j) for j in p)
ser=S.series(logR,e,0,4).removeO().expand()
ells={j:S.expand(ser.coeff(e,j)) for j in range(1,4)}
print('ell3=',S.factor(ells[3]),flush=True)
out={}
for eta in [1,-1]:
    kind='unrestricted' if eta==1 else 'distinct'
    rho=lambda v,C:1/(M.exp(C*v+v*v/2)-eta)
    C=M.findroot(lambda C:M.quad(lambda v:v*rho(v,C),[0,1,M.inf])-1,M.mpf('.76') if eta==1 else M.mpf('-.32'))
    kap={1:r}
    for j in range(2,7):kap[j]=S.expand(r*(1+eta*r)*S.diff(kap[j-1],r))
    delta=sum(ells[j]*e**j for j in ells)
    F=S.expand(sum(kap[j]*delta**j/S.factorial(j) for j in range(1,4)))
    fj={j:S.expand(F.coeff(e,j)) for j in range(1,4)}
    cache={}
    def integral(a,b):
        assert a>=b and b>=1,(a,b)
        key=(a,b)
        if key not in cache:
            cache[key]=M.quad(lambda v:v**a*rho(v,C)**b,[0,1,M.inf])
        return cache[key]
    def integrate_poly(expr):
        vals={}
        for (a,b,j),coeff in S.Poly(expr,x,r,z).terms():
            vals[j]=vals.get(j,M.mpf(0))+M.mpf(str(coeff))*integral(a,b)
        return sum(S.Float(str(v),55)*z**j for j,v in vals.items())
    def dc(expr):return S.expand(-x*r*(1+eta*r)*S.diff(expr,r))
    bnd={0:S.Integer(0),1:-c/24-5/(24*c) if eta==1 else c/24,
         2:5*z/(24*c)+S.Rational(1,48)-1/(24*c*c) if eta==1 else -S.Rational(1,48)}
    H={}
    for j,maxder in [(0,4),(1,2),(2,0)]:
        expr=fj[j+1]
        for d in range(maxder+1):
            H[j,d]=integrate_poly(expr)+S.diff(bnd[j],c,d).subs(c,S.Float(str(C),55))
            expr=dc(expr)
    J={j:(-1)**j*integrate_poly(x**j*kap[j]) for j in range(2,7)}
    V=M.mpf(str(J[2])); alpha=integral(2,1)/2
    dd={j: S.Float(str(((-1)**(j-1))*M.factorial(j-1)/(2*C**j)),55) if eta==1 else 0 for j in range(1,5)}
    Q={j:S.Integer(0) for j in range(1,5)}
    for j in range(3,7):Q[j-2]+=J[j]*(-S.I*u)**j/S.factorial(j)
    for j in range(1,5):Q[j]+=(dd[j]+H[0,j])*(-S.I*u)**j/S.factorial(j)
    for j in range(3):Q[j+2]+=H[1,j]*(-S.I*u)**j/S.factorial(j)
    Q[4]+=H[2,0]-z**4/4-S.Rational(1,12)
    Q[2]+=z**3/3
    P1=S.expand(Q[2]+Q[1]**2/2)
    P2=S.expand(Q[4]+Q[1]*Q[3]+Q[2]**2/2+Q[1]**2*Q[2]/2+Q[1]**4/24)
    def normal_z(j):return sum(M.binomial(j,2*l)*M.factorial(2*l)/(2**l*M.factorial(l))*alpha**(j-2*l) for l in range(j//2+1))
    def expectation(poly):
        val=M.mpc(0)
        for (i,j),coeff in S.Poly(poly,u,z).terms():
            if i%2:continue
            re,im=coeff.as_real_imag()
            a=M.mpc(str(re),str(im))
            mu=M.factorial(i)/(2**(i//2)*M.factorial(i//2)*V**(i//2))
            val+=a*mu*normal_z(j)
        assert abs(val.imag)<M.mpf('1e-40')
        return val.real
    a1=expectation(P1);a2=expectation(P2)
    out[kind]={'a1':str(a1),'a2':str(a2),'c':str(C),'quadratures':len(cache),'ell3':str(ells[3])}
    print(kind,'a1',M.nstr(a1,45),'a2',M.nstr(a2,45),'quadratures',len(cache),flush=True)
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2))
