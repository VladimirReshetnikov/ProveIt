"""Numerical orientation for the analytically proved Gaussian prefactors.

This script is not part of the proof. Requires mpmath.
"""
import mpmath as mp
import json
from pathlib import Path
mp.mp.dps=70
T=mp.findroot(lambda t:mp.tan(t/2)-t,2.3)
Tc=mp.findroot(lambda t:mp.exp(t)-1-t-t*t,1.8)
F=lambda t:(1+1/t)*(1-mp.exp(-t))
rhoc=F(Tc)

def exact_b(M,d):
    p=[1]+[0]*d
    for j in range(M):
        c=d-j
        for h in range(d,0,-1):p[h]=c*p[h]+p[h-1]
        p[0]*=c
    return p[d]

def saddle(rho):
    if rho<rhoc:return mp.findroot(lambda t:F(t)-rho,(mp.mpf('0.01'),Tc/2))
    t=-1j*T
    for j in range(1,81):
        r=2+(rho-2)*j/80
        t=mp.findroot(lambda x:F(x)-r,(t,t+mp.mpf('0.00001')))
    return t

records=[]
for rho in map(mp.mpf,['1.1','1.4','1.8','2.5','5']):
    t=saddle(rho)
    L=mp.log(t)+t-rho*mp.log(mp.exp(t)-1)
    Ltt=-1/t**2+rho*mp.exp(t)/(mp.exp(t)-1)**2
    z=mp.tanh(t/2)
    if abs(mp.im(t))<mp.pi/2:
        C=mp.sinh(t)**2*Ltt
        P=1/((1-z)*mp.sqrt(C)); contour='tanh'
    else:
        P=-1j*mp.exp(t)/(mp.exp(t)-1)/mp.sqrt(-Ltt); contour='horizontal'
    for d in (100,200,400):
        M=int(mp.nint(rho*d));value=exact_b(M,d)
        pair=2 if rho>rhoc else 1
        logamp=mp.loggamma(M+1)-mp.loggamma(d+1)+d*mp.re(L)+mp.log(pair*abs(P))-mp.log(2*mp.pi*d)/2
        normalized=mp.sign(value)*mp.exp(mp.log(abs(value))-logamp) if value else mp.mpf(0)
        prediction=mp.cos(d*mp.im(L)+mp.arg(P)) if pair==2 else 1
        records.append({'rho':str(rho),'d':d,'M':M,'contour':contour,
            't_real':str(mp.re(t)),'t_imag':str(mp.im(t)),
            'normalized':str(normalized),'prediction':str(prediction),
            'scaled_error':str(d*(normalized-prediction))})
result={'scope':'numerical orientation, not a proof','T':str(T),'T_fold':str(Tc),
        'rho_fold':str(rhoc),'records':records}
Path(__file__).with_name('saddle_normalization.json').write_text(json.dumps(result,indent=2)+'\n')
for r in records:print(r['rho'],r['d'],r['contour'],'d*error',mp.nstr(mp.mpf(r['scaled_error']),8))
