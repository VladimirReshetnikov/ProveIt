from __future__ import annotations

import json
import math
from fractions import Fraction
from pathlib import Path

import mpmath as mp
import matplotlib.pyplot as plt

mp.mp.dps = 100
ROOT = Path(__file__).resolve().parents[1]
OUT = Path(__file__).resolve().parent
FIG = ROOT / 'figures'
FIG.mkdir(parents=True, exist_ok=True)


def sinc(z: mp.mpf | mp.mpc) -> mp.mpf | mp.mpc:
    return mp.mpf(1) if z == 0 else mp.sin(z) / z


def Qm(t, m: int):
    p = mp.mpf(1)
    for k in range(1, m + 1):
        p *= sinc(t / (2 ** k))
    return p


def Qinf(t, extra: int = 180):
    p = mp.mpf(1)
    for k in range(1, extra + 1):
        p *= sinc(t / (2 ** k))
    return p


def Pm(z, m: int):
    p = mp.mpf(1)
    for j in range(m):
        p *= 1 - z ** (2 ** j)
    return p


def Gm_minus(s, m: int):
    p = mp.mpf(1)
    for k in range(1, m + 1):
        v = s / (2 ** k)
        p *= -mp.expm1(-v) / v if v != 0 else mp.mpf(1)
    return p


def Ginf_minus(s, extra: int = 200):
    p = mp.mpf(1)
    for k in range(1, extra + 1):
        v = s / (2 ** k)
        p *= -mp.expm1(-v) / v if v != 0 else mp.mpf(1)
    return p


def a(r: int, t):
    return mp.zeta(2 * r) * t ** (2 * r) / (r * mp.pi ** (2 * r) * (4 ** r - 1))


def Qcorr(t, m: int, N: int):
    return Qm(t, m) * mp.e ** (-sum(a(r, t) * 4 ** (-r * m) for r in range(1, N + 1)))


def qpoch(q: Fraction, n: int) -> Fraction:
    p = Fraction(1, 1)
    for k in range(1, n + 1):
        p *= 1 - q ** k
    return p


def rich_weights(p: int, q: Fraction = Fraction(1, 4)) -> list[Fraction]:
    ans = []
    for j in range(p + 1):
        exponent = (p - j + 1) * (p - j) // 2
        ans.append(((-1) ** (p - j)) * q ** exponent / (qpoch(q, j) * qpoch(q, p - j)))
    return ans


def rich(t, m: int, p: int):
    ws = rich_weights(p)
    return sum(mp.mpf(w.numerator) / w.denominator * Qm(t, m + j) for j, w in enumerate(ws))


def fmt(x, digits=8):
    return mp.nstr(x, digits)

# Exact identity verification
identity_rows = []
for m, t in [(1, mp.mpf('0.37')), (3, mp.mpf('2.125')), (7, mp.mpf('5.75')), (10, mp.mpf('-3.4'))]:
    lhs = Pm(mp.e ** (1j * t / 2 ** (m - 1)), m)
    rhs = (-1j) ** m * t ** m * 2 ** (-m * (m - 1) // 2) * mp.e ** (1j * t * (1 - 2 ** (-m))) * Qm(t, m)
    rel = abs(lhs-rhs) / max(abs(lhs), mp.mpf('1e-90'))
    identity_rows.append({'kind':'oscillatory','m':m,'argument':str(t),'relative_residual':fmt(rel,12)})
for m, s in [(1, mp.mpf('0.37')), (4, mp.mpf('3.2')), (8, mp.mpf('11.5')), (12, mp.mpf('0.019'))]:
    lhs = Gm_minus(s,m)
    rhs = 2 ** (m*(m+1)//2) / s ** m * Pm(mp.e ** (-s / 2**m),m)
    rel = abs(lhs-rhs)/max(abs(lhs),mp.mpf('1e-90'))
    identity_rows.append({'kind':'Laplace','m':m,'argument':str(s),'relative_residual':fmt(rel,12)})

# Coefficients
h1 = Fraction(1,18)
h2 = Fraction(1,2700) + Fraction(1,2)*h1*h1
h3 = Fraction(1,178605)+Fraction(1,18)*Fraction(1,2700)+Fraction(1,6)*Fraction(1,18)**3

# Cumulants and moments using exact fractions
k2 = Fraction(1,9)
k4 = Fraction(-2,225)
k6 = Fraction(16,3969)
k8 = Fraction(-16,3825)  # checked from Bernoulli formula
mu2 = k2
mu4 = k4 + 3*k2*k2
mu6 = k6 + 15*k4*k2 + 15*k2**3
mu8 = k8 + 28*k6*k2 + 35*k4*k4 + 210*k4*k2*k2 + 105*k2**4

# Error plot at t=5
t = mp.mpf(5)
qin = Qinf(t)
ms = list(range(2, 15))
series = {}
series['raw finite product'] = [abs(Qm(t,m)/qin-1) for m in ms]
for N in [1,2,3]:
    series[f'zeta correction N={N}'] = [abs(Qcorr(t,m,N)/qin-1) for m in ms]
for p in [1,2,3]:
    series[f'q-Richardson p={p}'] = [abs(rich(t,m,p)/qin-1) for m in ms]

plt.figure(figsize=(8.2,5.2))
for label, vals in series.items():
    plt.plot(ms, [float(mp.log10(v)) if v else -100 for v in vals], marker='o', markersize=3, label=label)
plt.xlabel('truncation level m')
plt.ylabel(r'$\log_{10}$ relative error at $t=5$')
plt.title('Arbitrary-order convergence from one finite Thue-Morse block')
plt.grid(True, alpha=.25)
plt.legend(fontsize=8, ncol=2)
plt.tight_layout()
plt.savefig(FIG/'spectral_convergence.png', dpi=220)
plt.close()

# Slopes from final 5 points
slopes = {}
for label, vals in series.items():
    ys=[float(mp.log(v)) for v in vals[-5:]]
    xs=ms[-5:]
    n=len(xs)
    sx=sum(xs); sy=sum(ys); sxx=sum(x*x for x in xs); sxy=sum(x*y for x,y in zip(xs,ys))
    slope=(n*sxy-sx*sy)/(n*sxx-sx*sx)
    slopes[label]={'natural_log_slope_per_m':slope,'base4_order':-slope/math.log(4)}

# Weak expansion table for phi=e^y
# M_m(a0)=product sinh(a0/2^k)/(a0/2^k); exact M_inf
a0=mp.mpf('1.0')
Minf=Qinf(1j*a0)
weak_rows=[]
for m in [2,3,4,5,6,8,10]:
    Mm=Qm(1j*a0,m)
    approx0=Mm
    approx1=Mm*(1+mp.mpf(mu2.numerator)/mu2.denominator/mp.factorial(2)*a0**2*4**(-m))
    approx2=Mm*(1+mp.mpf(mu2.numerator)/mu2.denominator/mp.factorial(2)*a0**2*4**(-m)
                    +mp.mpf(mu4.numerator)/mu4.denominator/mp.factorial(4)*a0**4*16**(-m))
    approx3=Mm*(1+mp.mpf(mu2.numerator)/mu2.denominator/mp.factorial(2)*a0**2*4**(-m)
                    +mp.mpf(mu4.numerator)/mu4.denominator/mp.factorial(4)*a0**4*16**(-m)
                    +mp.mpf(mu6.numerator)/mu6.denominator/mp.factorial(6)*a0**6*64**(-m))
    weak_rows.append({
        'm':m,
        'raw_rel_error':fmt(abs(approx0/Minf-1),10),
        'order1_rel_error':fmt(abs(approx1/Minf-1),10),
        'order2_rel_error':fmt(abs(approx2/Minf-1),10),
        'order3_rel_error':fmt(abs(approx3/Minf-1),10),
    })

# Lambert-W truncation plot, x=1e-8
x=mp.mpf('1e-8'); L=mp.log(2)
lam=-mp.lambertw(-L*x,-1)/L
s=2**lam
hs=[h/4 for h in range(0,49)]
raw_err=[]; centered_err=[]; us=[]; levels=[]
for h in hs:
    m=int(mp.ceil(lam+h))
    u=s/(2**m)
    g=Ginf_minus(u)
    c=mp.e**(u/2)*g
    raw_err.append(abs(g-1))
    centered_err.append(abs(c-1))
    us.append(u); levels.append(m)
plt.figure(figsize=(8.2,5.1))
plt.plot(hs,[float(mp.log10(v)) for v in raw_err],marker='o',markersize=2,label='raw tail $G(-u)-1$')
plt.plot(hs,[float(mp.log10(v)) for v in centered_err],marker='o',markersize=2,label='centered tail $e^{u/2}G(-u)-1$')
plt.xlabel(r'excess depth $h$ in $m=\lceil\lambda(x)+h\rceil$')
plt.ylabel(r'$\log_{10}$ absolute relative tail error')
plt.title(r'Lambert-$W$ truncation law on the leading saddle scale ($x=10^{-8}$)')
plt.grid(True,alpha=.25)
plt.legend()
plt.tight_layout()
plt.savefig(FIG/'lambert_truncation.png',dpi=220)
plt.close()

# G-tail expansion check
G_rows=[]
for u in [mp.mpf('0.02'),mp.mpf('0.2'),mp.mpf('1.0'),mp.mpf('3.0')]:
    exact=mp.log(Ginf_minus(u))
    vals=[]
    for N in [0,1,2,3]:
        ap=-u/2
        for r in range(1,N+1):
            # (-1)^(r+1) zeta coefficient
            ap += (-1)**(r+1)*mp.zeta(2*r)*u**(2*r)/(r*mp.pi**(2*r)*4**r*(4**r-1))
        vals.append(fmt(abs(exact-ap),10))
    G_rows.append({'u':str(u),'N0':vals[0],'N1':vals[1],'N2':vals[2],'N3':vals[3]})

# Richardson weight string
weights={str(p):[f'{w.numerator}/{w.denominator}' if w.denominator!=1 else str(w.numerator) for w in rich_weights(p)] for p in range(1,6)}

# Exact moment/cumulant values
moments={
    'kappa2':str(k2),'kappa4':str(k4),'kappa6':str(k6),'kappa8':str(k8),
    'mu2':str(mu2),'mu4':str(mu4),'mu6':str(mu6),'mu8':str(mu8),
    'h1':str(h1),'h2':str(h2),'h3':str(h3),
}

report={
    'identity_checks':identity_rows,
    'slopes':slopes,
    'weak_rows':weak_rows,
    'lambert':{'x':str(x),'lambda':fmt(lam,30),'s':fmt(s,30),'sample':[
        {'h':hs[i],'m':levels[i],'u':fmt(us[i],10),'raw':fmt(raw_err[i],10),'centered':fmt(centered_err[i],10)}
        for i in [0,4,8,12,16,24,32,40,48]
    ]},
    'G_tail_rows':G_rows,
    'weights':weights,
    'moments':moments,
}
payload = json.dumps(report, indent=2)
(OUT/'verification.json').write_text(payload + '\n', encoding='utf-8')
(OUT/'verification.txt').write_text(payload + '\n', encoding='utf-8')
print(payload)
