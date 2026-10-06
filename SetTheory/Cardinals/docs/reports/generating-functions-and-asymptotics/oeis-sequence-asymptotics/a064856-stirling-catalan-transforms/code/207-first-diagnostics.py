#!/usr/bin/env python3
"""Floating-point diagnostics, not certificates. Requires mpmath 1.3.0.
The exact checker is independent of this optional numerical dependency.
"""
import json, math
from pathlib import Path
import mpmath as mp
mp.mp.dps=90
root=Path(__file__).resolve().parent
polys=json.loads((root/'exact_results.json').read_text())['gamma_ratio_polynomials']
R=[[mp.mpf(v) for v in row] for row in polys]
def polyval(p,x):
    y=mp.mpf(0)
    for a in reversed(p):y=y*x+a
    return y
def h(y):
    if y==4:return mp.mpf(0)
    return mp.rgamma(4-y)/mp.sqrt(4-y)
def fj(L,j,derivative=0):
    return mp.quad(lambda y: mp.exp(-L*y)*mp.sqrt(y)*h(y)*polyval(R[j],4-y)*(-y)**derivative,[0,1,2,3,4])
def zexact(n):
    L=mp.log(n)
    def integrand(y):
        if y==0 or y==4:return mp.mpf(0)
        return mp.sqrt(y/(4-y))*mp.rgamma(4-y)*mp.exp(mp.loggamma(n+4-y)-mp.loggamma(n+1)-3*L)
    return mp.quad(integrand,[0,1,2,3,4])
def text(x):return mp.nstr(x,35)

# Fixed-log coefficients from the exact logarithmic recurrence.
M=180
ell=[mp.mpf(0),mp.digamma(4)+mp.mpf(1)/8]
for m in range(2,M+1):
    ell.append(mp.mpf(1)/(2*m*4**m)-mp.zeta(m,4)/m)
alpha=[mp.mpf(1)]
for k in range(1,M+1):alpha.append(sum(m*ell[m]*alpha[k-m] for m in range(1,k+1))/k)
c=[mp.rf(mp.mpf('1.5'),k)*alpha[k] for k in range(M+1)]
d=[mp.mpf(0)]
# Logarithm recurrence: k*c_k=sum j*d_j*c_(k-j).
for k in range(1,7): d.append(c[k]-sum(mp.mpf(j)/k*d[j]*c[k-j] for j in range(1,k)))

output={'classification':'Floating-point diagnostics only; neither interval certification nor proof of asymptotic remainders.',
        'mpmath_version':mp.__version__,'precision_decimal_digits':mp.mp.dps,
        'c_first_six':[text(x) for x in c[:6]],'d_first_six':[text(x) for x in d[1:]],
        'counts':[],'completion':[],'large_order':[],'inverse':[],'total_variation':[]}
exactvals=json.loads((root/'exact_results.json').read_text())['terms_through_80']
for n in [20,50,100,1000,100000]:
    n=mp.mpf(n);L=mp.log(n);Z=zexact(n)
    fs=[fj(L,j) for j in range(4)]
    approximations=[sum(fs[j]/n**j for j in range(J+1)) for J in range(3)]
    entry={'n':int(n),'normalized_scalar':text(Z*24/mp.sqrt(mp.pi)*L**mp.mpf('1.5')),
           'resummed_relative_errors':[text(a/Z-1) for a in approximations],
           'scaled_sector_errors':[text((approximations[J]/Z-1)*n**(J+1)) for J in range(3)]}
    if n<=80:
        ref=mp.mpf(exactvals[int(n)])/(mp.factorial(n)*n**3)*2*mp.pi
        entry['integral_vs_exact_relative']=text(Z/ref-1)
    output['counts'].append(entry)
    y=mp.loggamma(n+1)+3*L+mp.log(Z/(2*mp.pi))
    t0=y/mp.lambertw(y/mp.e); l0=mp.log(t0)
    v0=t0-mp.mpf('3.5')+(mp.mpf('1.5')*mp.log(l0)+mp.log(24*mp.sqrt(2)))/l0
    v1=v0-c[1]/l0**2
    output['inverse'].append({'n':int(n),'v0_minus_n':text(v0-n),'v1_minus_n':text(v1-n)})

for L in [mp.mpf(1),mp.mpf(5),mp.mpf(12)]:
    exact=fj(L,0)
    sums=[]
    for K in [10,30,80,160]:
        a=sum(alpha[k]*mp.gammainc(k+mp.mpf('1.5'),0,4*L)/L**(k+mp.mpf('1.5')) for k in range(K+1))/12
        sums.append({'terms':K+1,'relative_error':text(a/exact-1)})
    output['completion'].append({'L':str(L),'truncations':sums})
for k in [20,40,80,120,160]:
    target=-24/mp.pi*mp.gamma(k)*mp.mpf(4)**(-k)
    output['large_order'].append({'k':k,'c_over_large_order_equivalent':text(c[k]/target)})

# Positive floating recurrence, truncated at 220 cycles. Truncation and rounding
# are deliberately not claimed rigorous; mass residual is printed explicitly.
q=[1.0]+[0.0]*220
H=[float(mp.gamma(k+mp.mpf('0.5'))/(mp.sqrt(mp.pi)*mp.gamma(k+2))) for k in range(221)]
for n in range(1,100001):
    p=4.0/(n+3)
    for k in range(min(n,220),0,-1):q[k]=(1-p)*q[k]+p*q[k-1]
    q[0]*=1-p
    if n in [100,1000,10000,100000]:
        norm=sum(q[k]*H[k] for k in range(221))
        tv=.5*sum(q[k]*abs(H[k]/norm-1) for k in range(221))
        output['total_variation'].append({'n':n,'probability_mass_residual':sum(q)-1,
          'tv':tv,'sqrt_log_n_times_tv':math.sqrt(math.log(n))*tv,
          'limiting_constant':3*math.sqrt(2/math.pi)/8})
print(json.dumps(output,indent=2,sort_keys=True))
