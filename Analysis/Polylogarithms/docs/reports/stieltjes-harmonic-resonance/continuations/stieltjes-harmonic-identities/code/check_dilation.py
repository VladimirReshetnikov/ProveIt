import mpmath as mp
import json
from pathlib import Path

mp.mp.dps = 60

def gamma0(x):
    return -mp.digamma(x)

def shifted(a):
    return a-mp.floor(a)

def constant_part00(p,q,a,b):
    lefts = []
    for j in range(p):
        lefts.append((shifted((j-a)/p),p,q,'first'))
    for j in range(q):
        lefts.append((shifted((j-b)/q),q,p,'second'))
    lefts.sort(key=lambda z:z[0])
    result=mp.mpf('0')
    for i,(left,freq,otherfreq,label) in enumerate(lefts):
        right=lefts[(i+1)%len(lefts)][0]
        if right<=left:
            right+=1
        length=right-left
        if label == 'first':
            c=shifted(q*left+b)
        else:
            c=shifted(p*left+a)
        h0=gamma0(c)
        def integrand(t):
            if t < mp.mpf('1e-31'):
                return -otherfreq*mp.polygamma(1,c)/freq+mp.euler*h0
            h=gamma0(c+otherfreq*t)
            return gamma0(1+freq*t)*h+(h-h0)/(freq*t)
        result+=mp.quad(integrand,[0,length/2,length])+h0/freq*mp.log(length)
    return result

def base00(c):
    # Independent base evaluation by stable endpoint subtraction.
    return constant_part00(1,1,mp.mpf('0'),c)

def dilation00(p,q,a,b,base):
    from math import gcd
    d=gcd(p,q);P=p//d;Q=q//d
    c=shifted(P*b-Q*a)
    lp,lq=mp.log(P),mp.log(Q)
    pull=base-lq*gamma0(c)-lp*gamma0(1-c)-lp*lq
    intrinsic=pull-mp.log(p)*(gamma0(c)+lp)-mp.log(q)*(gamma0(1-c)+lq)
    return intrinsic,pull,c

def loggamma_numeric(p,q,a,b):
    sing = sorted(set([mp.mpf('0'),mp.mpf('1')]+[shifted((j-a)/p) for j in range(p)]+[shifted((j-b)/q) for j in range(q)]))
    return sum(mp.quad(lambda x:mp.loggamma(shifted(p*x+a))*mp.loggamma(shifted(q*x+b)),[l,(l+r)/2,r]) for l,r in zip(sing,sing[1:]))

def loggamma_formula(p,q,a,b):
    from math import gcd
    d=gcd(p,q);P=p//d;Q=q//d
    c=shifted(P*b-Q*a);z=mp.exp(2j*mp.pi*c)
    lp,lq=mp.log(P),mp.log(Q);kappa=mp.euler+mp.log(2*mp.pi)
    h=mp.mpf('1e-7')
    f={j:mp.polylog(2+j*h,z) for j in range(-2,3)}
    first=(f[-2]-8*f[-1]+8*f[1]-f[2])/(12*h)
    second=(-f[2]+16*f[1]-30*f[0]+16*f[-1]-f[-2])/(12*h*h)
    value=second-(2*kappa+lp+lq)*first+((kappa+lp)*(kappa+lq)+mp.pi**2/4)*f[0]
    return mp.log(2*mp.pi)**2/4+mp.re(value)/(2*mp.pi**2*P*Q)+(lp-lq)*mp.im(f[0])/(4*mp.pi*P*Q)

if __name__=='__main__':
    records=[]
    cases=[(1,2,'0','0.3'),(2,3,'0.1','0.27'),(4,6,'0.1','0.27'),(3,2,'0.2','0.11')]
    for p,q,aa,bb in cases:
        a,b=mp.mpf(aa),mp.mpf(bb)
        from math import gcd
        c=shifted((p//gcd(p,q))*b-(q//gcd(p,q))*a)
        base=base00(c)
        numerical=constant_part00(p,q,a,b)
        predicted,pull,c=dilation00(p,q,a,b,base)
        gn=loggamma_numeric(p,q,a,b);gf=loggamma_formula(p,q,a,b)
        row={'p':p,'q':q,'a':aa,'b':bb,'c':mp.nstr(c,30),'ct00_numeric':mp.nstr(numerical,50),'ct00_formula':mp.nstr(predicted,50),'ct00_error':mp.nstr(abs(numerical-predicted),8),'loggamma_numeric':mp.nstr(gn,50),'loggamma_formula':mp.nstr(gf,50),'loggamma_error':mp.nstr(abs(gn-gf),8)}
        row['passed']=bool(abs(numerical-predicted)<mp.mpf('1e-45') and abs(gn-gf)<mp.mpf('1e-25'))
        assert row['passed'],row
        records.append(row)
        print(json.dumps(row),flush=True)
    (Path(__file__).resolve().parent.parent / 'data' / 'dilation_checks.json').write_text(json.dumps({'dps':mp.mp.dps,'polylog_order_difference_step':'1e-7','thresholds':{'ct00':'1e-45','loggamma':'1e-25'},'checks':records},indent=2)+'\n')
