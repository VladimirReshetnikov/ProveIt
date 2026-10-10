"""Exact parity reductions of all four purported new mixed candidates.

The full run also performs independent 60-digit quadrature.  It writes a
JSON record; numerical residuals are not rigorous interval error bounds.
"""
import argparse
import json
from pathlib import Path
import sympy as s
import mpmath as mp

pi,I=s.pi,s.I
G,B4,B6,C2,C4,C6,Z3,Z5,l2,l3=s.symbols(
    'G beta4 beta6 C2 C4 C6 zeta3 zeta5 log2 log3',real=True)

gauss={(4,1):-s.Rational(587,1024)*Z5+pi**2*Z3/64+3*pi**4*l2/512,
       (5,1):3*B6-pi**2*B4/6-pi**4*G/90-5*pi**5*l2/3072}
eis={(4,1):-s.Rational(281,162)*Z5+2*pi**2*Z3/27+2*pi**4*l3/243,
     (5,1):-3*C6+pi**2*C4/6+pi**4*C2/90+pi**5*l3/729}

def single_gauss(n):
    if n==1:return -l2/2-I*pi/4
    zz={2:pi**2/6,3:Z3,4:pi**4/90,5:Z5,6:pi**6/945}[n]
    be={2:G,3:pi**3/32,4:B4,5:5*pi**5/1536,6:B6}[n]
    return -s.Rational(1,2**n)*(1-s.Rational(1,2**(n-1)))*zz-I*be

def single_eis(n):
    if n==1:return -l3/2+I*pi/6
    zz={2:pi**2/6,3:Z3,4:pi**4/90,5:Z5,6:pi**6/945}[n]
    # Odd imaginary components are not used by the parity projection, but
    # the exact Bernoulli formula records them and verifies realness too.
    cc={2:C2,4:C4,6:C6}.get(n)
    if cc is None:
        cc=-(2*pi*I)**n*s.bernoulli(n,s.Rational(1,3))/(2*I*s.factorial(n))
    return (s.Rational(1,3**(n-1))-1)*zz/2+I*cc

def direct(a,b,single,x_fraction):
    w=a+b
    p=-s.zeta(w)
    for r in range(0,w//2+1):
        mu=w-2*r
        if mu<1:continue
        C=lambda ind:s.binomial(mu-1,ind-1) if mu>=ind else 0
        B=(2*pi*I)**(2*r)*s.bernoulli(2*r)/s.factorial(2*r)
        p+=(-1)**a*(C(a)+C(b))*single(mu)*B
    p-=single(b)*(2*pi*I)**a*s.bernoulli(a,x_fraction)/s.factorial(a)
    zzmap={s.zeta(3):Z3,s.zeta(5):Z5}
    p=s.expand(p.subs(zzmap))
    if w%2:
        assert s.simplify(s.im(p))==0
        return s.expand(p/2)
    assert s.simplify(s.re(p))==0
    return s.expand(p/(2*I))

def run(output,symbolic_only=False):
    symbolic=[]
    for key,expected in gauss.items():
        got=direct(*key,single_gauss,s.Rational(1,4))
        assert s.expand(got-expected)==0
        print('Gaussian',key,got,flush=True)
        symbolic.append({'tower':'Gaussian','a':key[0],'b':key[1],
                         'exact_difference':'0','expression':str(got)})
    for key,expected in eis.items():
        got=direct(*key,single_eis,s.Rational(2,3))
        assert s.expand(got-expected)==0
        print('Eisenstein',key,got,flush=True)
        symbolic.append({'tower':'Eisenstein','a':key[0],'b':key[1],
                         'exact_difference':'0','expression':str(got)})
    if symbolic_only:
        output.parent.mkdir(parents=True,exist_ok=True)
        output.write_text(json.dumps({'status':'Exact symbolic checks.',
            'symbolic_identity_checks':4,'symbolic_checks':symbolic,
            'numerical_checks':[]},indent=2)+'\n')
        return
    mp.mp.dps=60
    rho=mp.e**(2j*mp.pi/3)
    be=lambda n:mp.im(mp.polylog(n,1j))
    cl=lambda n:mp.im(mp.polylog(n,rho))
    env={G:be(2),B4:be(4),B6:be(6),C2:cl(2),C4:cl(4),C6:cl(6),
         Z3:mp.zeta(3),Z5:mp.zeta(5),l2:mp.log(2),l3:mp.log(3)}
    numerical=[]
    for tower,x,table in [('Gaussian',1j,gauss),('Eisenstein',rho**2,eis)]:
        for (a,b),expr in table.items():
            val=mp.quad(lambda t:x*(-mp.log(t))**(a-1)*mp.polylog(b,t)/(1-x*t),
                        [0,mp.mpf('.1'),mp.mpf('.7'),1])/mp.factorial(a-1)
            val=mp.re(val) if (a+b)%2 else mp.im(val)
            expected=s.lambdify(list(env),expr,'mpmath')(*env.values())
            err=abs(val-expected)
            print(tower,(a,b),mp.nstr(val,40),'residual',mp.nstr(err,8),flush=True)
            assert err<mp.mpf('1e-55')
            numerical.append({'tower':tower,'a':a,'b':b,
                'component':'real' if (a+b)%2 else 'imag',
                'quadrature_value':mp.nstr(val,58),
                'formula_value':mp.nstr(expected,58),
                'absolute_residual':mp.nstr(err,12)})
    assert len(numerical)==4
    output.parent.mkdir(parents=True,exist_ok=True)
    output.write_text(json.dumps({
        'status':'Exact symbolic checks and independent numerical quadrature; '
                 'numerical residuals are not interval certificates.',
        'mpmath_dps':60,'symbolic_identity_checks':4,
        'symbolic_checks':symbolic,'numerical_checks':numerical},indent=2)+'\n')


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--symbolic-only',action='store_true')
    parser.add_argument('--output',type=Path,default=
        Path(__file__).resolve().parents[3]/'results'/'independent'/'parity'/'mixed_checks.json')
    args=parser.parse_args()
    run(args.output,args.symbolic_only)
