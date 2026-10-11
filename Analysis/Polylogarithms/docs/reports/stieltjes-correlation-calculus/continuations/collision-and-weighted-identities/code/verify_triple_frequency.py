"""Independent exact-Bernoulli versus weighted-Tornheim Fourier checks."""
from pathlib import Path
import json
import time
import sympy as sp
import mpmath as mp

mp.mp.dps=60
HERE=Path(__file__).resolve().parent
p=(1,2,3)
a=(sp.Rational(0),sp.Rational(1,5),sp.Rational(1,7))
x=sp.symbols('x')


def mpq(q):
    q=sp.Rational(q)
    return mp.mpf(int(q.p))/int(q.q)


def exact_integral(lam):
    points={sp.Rational(0),sp.Rational(1)}
    for pi,ai in zip(p,a):
        for k in range(-1,pi+2):
            z=(sp.Rational(k)-ai)/pi
            if 0<z<1: points.add(z)
    points=sorted(points)
    total=sp.Rational(0)
    pieces=[]
    for lo,hi in zip(points[:-1],points[1:]):
        mid=(lo+hi)/2
        integrand=sp.Integer(1)
        for pi,ai,li in zip(p,a,lam):
            f=pi*x+ai-sp.floor(pi*mid+ai)
            integrand*=-sp.bernoulli(li,f)/li
        poly=sp.Poly(integrand,x)
        anti=sp.integrate(poly.as_expr(),x)
        val=sp.factor(anti.subs(x,hi)-anti.subs(x,lo))
        pieces.append({'interval':[str(lo),str(hi)],'integral':str(val),'polynomial':str(poly.as_expr())})
        total+=val
    return sp.factor(total),pieces


def weighted_T(A,B,C,pi,pj,X,Y):
    def f(t):
        return t**(C-1)*mp.polylog(A,X*mp.exp(-pi*t))*mp.polylog(B,Y*mp.exp(-pj*t))
    return mp.quad(f,[0,mp.mpf('.5'),1,3,mp.inf])/mp.gamma(C)


def spectral(lam):
    subtotal=mp.mpf(0)
    cones=[]
    for k in range(3):
        i,j=[q for q in range(3) if q!=k]
        phase=mp.exp(-mp.j*mp.pi*(lam[i]+lam[j]-lam[k])/2)
        filtered=mp.mpc(0)
        terms=[]
        for h in range(p[k]):
            thetaX=sp.factor(a[i]-sp.Rational(p[i],p[k])*a[k]+sp.Rational(h*p[i],p[k]))
            thetaY=sp.factor(a[j]-sp.Rational(p[j],p[k])*a[k]+sp.Rational(h*p[j],p[k]))
            X=mp.exp(2*mp.j*mp.pi*mpq(thetaX))
            Y=mp.exp(2*mp.j*mp.pi*mpq(thetaY))
            assert thetaX.q!=1 and thetaY.q!=1
            T=weighted_T(lam[i],lam[j],lam[k],p[i],p[j],X,Y)
            filtered+=T
            terms.append({'h':h,'X_phase':str(thetaX),'Y_phase':str(thetaY),'T_real':mp.nstr(mp.re(T),55),'T_imag':mp.nstr(mp.im(T),55)})
        # The opposite cone is the conjugate because all spectral orders
        # and shifts in this independent check are real.
        cone=mp.power(p[k],lam[k]-1)*2*mp.re(phase*filtered)
        subtotal+=cone
        cones.append({'negative_frequency':k+1,'positive_frequencies':[i+1,j+1],'cone_pair_value':mp.nstr(cone,55),'filter_terms':terms})
        print('lambda',lam,'cone',k+1,'done',flush=True)
    pref=mp.fprod(mp.gamma(li) for li in lam)/mp.power(2*mp.pi,sum(lam))
    return pref*subtotal,cones


def main():
    started=time.time()
    results=[]
    for lam in [(2,2,2),(2,3,2)]:
        exact,pieces=exact_integral(lam)
        numeric,cones=spectral(lam)
        error=abs(numeric-mpq(exact))
        results.append({'lambda':lam,'exact_integral':str(exact),'exact_decimal':mp.nstr(mpq(exact),55),'spectral_decimal':mp.nstr(numeric,55),'absolute_error':mp.nstr(error,8),'pieces':pieces,'cones':cones})
        print('RESULT',lam,str(exact),mp.nstr(error,8),flush=True)
    report={'p':p,'a':[str(z) for z in a],'working_decimal_digits':mp.mp.dps,'certificate':False,'method':'Exact rational integration of piecewise Bernoulli polynomials compared with independent Mellin integrals for weighted Tornheim sums and congruence filters','elapsed_seconds':time.time()-started,'results':results}
    (HERE.parent/'results'/ 'triple_frequency_results.json').write_text(json.dumps(report,indent=2)+'\n')
    print('DONE',time.time()-started,flush=True)

if __name__=='__main__':main()
