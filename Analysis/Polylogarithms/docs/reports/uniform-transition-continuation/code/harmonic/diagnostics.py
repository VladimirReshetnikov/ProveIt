"""High-precision diagnostics for proved asymptotic theorems.

The quadratures in this file are NOT outward-rounded certificates.
They evaluate the exact positive integral after a stable change of scale.
"""
from pathlib import Path
import argparse,json
import mpmath as mp

def ell(x):
    t=mp.exp(-x)
    if not t:return mp.mpf(0)
    return mp.log(mp.log1p(t)/t)

def w(x):
    t=mp.exp(-x)
    return 1/((1+t)*(mp.log1p(t)/t))

def saddle(p,h,a):
    p,h,a=map(mp.mpf,(p,h,a))
    alpha,eps=p/h,a/h
    lo=alpha/(1+eps)
    hi=alpha/(1/(2*mp.log(2))+eps)
    x=mp.findroot(lambda x:x*(w(x)+eps)-alpha,(lo,hi))
    B=1+x*x*mp.diff(w,x)/alpha
    rx=1/(1+mp.exp(x))
    ap=-1+x*rx
    app=2-2*x*rx+x*x*(2*rx*rx-rx)
    phi3=2-x**3*mp.diff(w,x,2)/alpha
    phi4=-6-x**4*mp.diff(w,x,3)/alpha
    E1=app/(2*B)+phi3*ap/(2*B**2)+phi4/(8*B**2)+5*phi3**2/(24*B**3)
    k=(1+eps)/(w(x)+eps)
    lgstar=mp.loggamma(p)-(p-mp.mpf('.5'))*mp.log(p)+p-mp.log(2*mp.pi)/2
    logs=p*(mp.log1p(k-1)-(k-1))+h*ell(x)-mp.log1p(mp.exp(-x))-mp.log(B)/2-lgstar
    return {'p':p,'h':h,'a':a,'alpha':alpha,'eps':eps,'x':x,'B':B,'k':k,'E1':E1,'logS':logs}

def exact_ratio(d):
    p,x,B,alpha,k=d['p'],d['x'],d['B'],d['alpha'],d['k']
    root=mp.sqrt(p*B)
    ex=ell(x)
    gx=1+mp.exp(-x)
    def f(u):
        if not mp.isfinite(u):return mp.mpf(0)
        delta=u/root
        if delta<=-1:return mp.mpf(0)
        z=1+delta
        # Exact saddle-normalized phase, evaluated with cancellation removed.
        psi=mp.log1p(delta)-delta+(1-k)*delta+(ell(x*z)-ex)/alpha
        return mp.exp(p*psi)*gx/(z*(1+mp.exp(-x*z)))
    cuts=[-root]+[mp.mpf(v) for v in (-20,-12,-8,-4,0,4,8,12,20) if v>-root]+[mp.inf]
    return mp.quad(f,cuts)/mp.sqrt(2*mp.pi)

def R(p,h,a):
    d=saddle(p,h,a)
    return mp.exp(d['logS'])*exact_ratio(d)

def qpolys(L,v,a):
    q0=(a-v/2+mp.mpf('.5'))*L+2-5*v/6
    q1=(v*v/8-v/4)*L*L+(v*v/3-v/3-mp.mpf(1)/12)*L-5*a*v/6+2*a+3*v*v/8-v/12-1
    return q0,q1

def run_inverse(h,a,theta):
    h,a,theta=map(mp.mpf,(h,a,theta))
    v=-mp.log(theta); L=mp.log(h)-mp.log(2*v)
    q0,q1=qpolys(L,v,a)
    lead=h*L; one=lead+q0; two=one+q1/h
    true=mp.findroot(lambda p:R(p,h,a)-theta,(two-mp.mpf('.03'),two+mp.mpf('.03')),solver='secant',tol=mp.mpf('1e-30'))
    return {'h':str(h),'a':str(a),'theta':str(theta),'p_true':mp.nstr(true,35),'leading_error':mp.nstr(lead-true,15),'Q0_error':mp.nstr(one-true,15),'Q1_error':mp.nstr(two-true,15),'scaled_Q1_error':mp.nstr((two-true)*h*h/(1+L)**3,15)}

def main():
    pa=argparse.ArgumentParser();pa.add_argument('--output',type=Path,default=Path(__file__).with_name('harmonic_diagnostics.json'));pa.add_argument('--dps',type=int,default=50);pa.add_argument('--inverse-only',action='store_true');args=pa.parse_args()
    mp.mp.dps=args.dps
    cases=[(40,40**3,mp.mpf('.5')),(80,80**3,mp.mpf('.5')),(160,160**3,mp.mpf('.5')),
           (40,40,mp.mpf('.5')),(80,80,mp.mpf('.5')),(160,160,mp.mpf('.5')),
           (40,1,mp.mpf('.5')),(80,1,mp.mpf('.5')),(160,1,mp.mpf('.5')),
           (40,40,40**2),(80,80,80**2),(160,160,160**2),
           (100*mp.log(100),100,mp.mpf('.5')),(400*mp.log(400),400,mp.mpf('.5'))]
    records=[]
    if not args.inverse_only:
        for p,h,a in cases:
            d=saddle(p,h,a);ratio=exact_ratio(d);err=ratio-1-d['E1']/p
            row={key:mp.nstr(d[key],30) for key in ('p','h','a','x','B','E1','logS')}
            row.update({'integral_over_S':mp.nstr(ratio,35),'leading_relative_error':mp.nstr(ratio-1,20),'corrected_relative_error':mp.nstr(err,20),'p_squared_corrected_error':mp.nstr(p*p*err,20)})
            records.append(row);print(json.dumps(row),flush=True)
    inverses=[]
    for h in (50,200,800):
        row=run_inverse(h,mp.mpf('.5'),mp.mpf('.5'));inverses.append(row);print(json.dumps(row),flush=True)
    data={'status':'numerical diagnostics, not interval certificates','mpmath_version':mp.__version__,'dps':args.dps,'saddle':records,'inverse':inverses}
    args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_text(json.dumps(data,indent=2)+'\n')

if __name__=='__main__':main()
