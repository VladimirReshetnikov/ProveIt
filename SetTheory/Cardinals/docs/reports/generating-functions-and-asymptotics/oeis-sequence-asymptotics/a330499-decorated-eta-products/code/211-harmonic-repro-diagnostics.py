"""Portable finite diagnostics. Exact integer numerators; mpmath, no NumPy.
The decimal outputs are not interval enclosures or asymptotic error bounds.
"""
from pathlib import Path
from math import factorial
import json
import mpmath as mp
import sympy as sp

ROOT = Path(__file__).resolve().parent
SELECTED = (100, 200, 400, 800, 1500, 2000)
B, MVAR = sp.symbols('b M')
P = [sp.lambdify((B, MVAR), sp.sympify(p), 'mpmath')
     for p in json.loads((ROOT / 'coefficients.json').read_text())['P']]

def require(ok, message):
    if not ok:
        raise RuntimeError(message)

def exact_values():
    N = max(SELECTED)
    h = [0]*(N+1)
    for d in range(1, N+1):
        for k in range(d, N+1, d):
            h[k] += 1 if d % 2 else -1
    fixture = dict(tuple(map(int, line.split())) for line in
                   (ROOT/'b330498.txt').read_text().splitlines() if line and not line.startswith('#'))
    require(set(fixture) == set(range(401)), 'fixture must contain exactly n=0..400')
    require(fixture[0] == 0, 'a(0)')
    # q[n,k] = unsigned_stirling(n,k)*(k-1)!; no factorial multiplications
    # inside the dot product. This is distinct from verify_exact.py.
    row = [0, 1]
    values = {}
    for n in range(1, N+1):
        if n > 1:
            row = [0] + [(n-1)*(row[k] if k < n else 0) +
                         (k-1)*row[k-1] for k in range(1, n+1)]
        if n <= 400 or n in SELECTED:
            a = sum(row[k]*h[k] for k in range(1, n+1))
            if n <= 400:
                require(a == fixture[n], 'weighted recurrence mismatch at n='+str(n))
            if n in SELECTED:
                values[n] = a
    return values

def odd_tau(m):
    while m % 2 == 0:
        m //= 2
    return sum(m % d == 0 for d in range(1, m+1))

def modes(t, cutoff):
    M = mp.e-1
    H = [mp.mpf(0) for _ in range(4)]
    for m in range(1, cutoff+1):
        b = mp.pi*mp.sqrt(2*m/M)
        K = odd_tau(m)*(8*M/m)**mp.mpf('.25')*mp.exp(-mp.pi**2*m/M)
        phi = 2*b*mp.sqrt(t)-mp.pi/4
        for j in range(4):
            H[j] += K*P[j](b,M)*mp.sin(phi+j*mp.pi/2)
    return H

def evaluate(n, a, dps, cutoff):
    with mp.workdps(dps):
        rho = 1-1/mp.e
        U = mp.mpf(a)/factorial(n)*rho**n*n
        H = modes(n, cutoff)
        rem = U-mp.log(2)
        errors = []
        for j in range(5):
            errors.append(rem*n**(mp.mpf('.25')+mp.mpf(j)/2))
            if j < 4:
                rem -= n**(-mp.mpf('.25')-mp.mpf(j)/2)*H[j]
        return U, H, errors

def inverse_offsets(n, a):
    computed = []
    for dps, cutoff in ((80,40),(100,60)):
        with mp.workdps(dps):
            rho = 1-1/mp.e
            target = mp.log(mp.mpf(a))
            offsets = []
            for J in (1,4):
                def logA(t):
                    H = modes(t,cutoff)
                    core = mp.log(2)+sum(t**(-mp.mpf('.25')-mp.mpf(j)/2)*H[j] for j in range(J))
                    return mp.loggamma(t)-t*mp.log(rho)+mp.log(core)
                t = mp.findroot(lambda x: logA(x)-target, (n-mp.mpf('.1'),n+mp.mpf('.1')))
                require(abs(logA(t)-target) < mp.mpf('1e-65'), 'inverse residual')
                offsets.append(t-n)
            computed.append(offsets)
    with mp.workdps(100):
        require(max(abs(x-y) for x,y in zip(*computed)) < mp.mpf('1e-68'),
                'inverse precision or mode-cutoff stability')
        return {'n':n,'offsets':[{'J':J,'t_minus_n':mp.nstr(x,30)}
                               for J,x in zip((1,4),computed[0])]}

values = exact_values()
rows = []
with mp.workdps(100):
    for n in SELECTED:
        U,H,E = evaluate(n,values[n],80,40)
        V,G,F = evaluate(n,values[n],100,60)
        require(max(abs(x-y) for x,y in zip([U]+H+E,[V]+G+F)) < mp.mpf('1e-68'),
                'precision or mode-cutoff stability failed at '+str(n))
        rows.append({'n':n,'normalized':mp.nstr(U,45),
                     'H':[mp.nstr(h,35) for h in H],
                     'scaled_errors_after_J_terms':[mp.nstr(x,35) for x in E]})
    output = {'scope':'Finite diagnostics, not interval enclosures or certified asymptotic error bounds.',
              'exact_arithmetic':'weighted unsigned-Stirling recurrence through 2000; all 401 b-file terms checked',
              'precision_digits':80,'mode_cutoff':40,
              'stability_check':'100 digits and 60 modes agree within 1e-68 for every saved scalar',
              'scaled_error_definition':'E_J(n)=n^(1/4+J/2)*(n*rho^n*a(n)/n!-log(2)-sum_(j<J)n^(-1/4-j/2)*H_j(sqrt(n)))',
              'rows':rows,
              'inverse_offsets':[inverse_offsets(n,values[n]) for n in (100,400,2000)]}
print(json.dumps(output,indent=2,sort_keys=True))
