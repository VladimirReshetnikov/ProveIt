#!/usr/bin/env python3
"""Reproduce exact coefficients and numerical saddle checks (not interval proofs).

Python 3.10+, mpmath. Run from any directory. Output is written to ../data.
No network access is needed. DP is exact for positive integral s; saddle sums
use arbitrary precision with a conservative exponential cutoff. The analytic
error estimates in the article, rather than these experiments, prove theorems.
"""
from __future__ import annotations
import argparse
import csv
import json
import math
from pathlib import Path
import mpmath as mp

OUT = Path(__file__).resolve().parent.parent / 'data'

def coefficients(nmax: int, s: int) -> list[int]:
    if nmax < 0 or s < 1 or int(s) != s:
        raise ValueError('nmax >= 0 and integral s >= 1 required')
    a = [0] * (nmax + 1)
    a[0] = 1
    for k in range(1, nmax + 1):
        w = k ** s
        for n in range(nmax, k - 1, -1):
            a[n] += w * a[n-k]
    return a

def bernoulli_polynomials(order: int) -> list[list[int]]:
    """P_1=p; P_{j+1}=p(1-p)P_j'. Coefficients ascending."""
    polys = [[], [0, 1]]
    for j in range(1, order):
        p = polys[-1]
        q = [0] * (len(p) + 1)
        for i in range(1, len(p)):
            q[i] += i * p[i]
            q[i+1] -= i * p[i]
        polys.append(q)
    return polys

POLYS = bernoulli_polynomials(12)

def saddle_sums(t: mp.mpf, s: int | mp.mpf, order: int = 8,
                guard: int = 0) -> tuple[mp.mpf, list[mp.mpf], int]:
    """Phi and cumulants; the omitted tail is tested by increasing guard.

The cutoff forces t*K/2 larger than the working precision in natural logs,
with further margin for polynomial factors. This is a numerical safeguard,
not a directed-rounding certificate.
"""
    t = mp.mpf(t)
    if not isinstance(s, int):
        s = mp.mpf(s)
    if t <= 0 or s <= 0 or not 1 <= order <= 12:
        raise ValueError('positive t,s and 1 <= order <= 12 required')
    target = (mp.mp.dps + 20 + guard) * mp.log(10)
    K = max(32, int(mp.ceil(2 * (target + (s+order+2)*mp.log(2+1/t))/t)))
    phi = mp.mpf(0)
    kap = [mp.mpf(0) for _ in range(order+1)]
    # Repeated multiplication avoids an exponential evaluation at every k.
    base, power = mp.exp(-t), mp.exp(-t)
    for k in range(1, K+1):
        r = k**s * power
        p = r/(1+r)
        phi += mp.log1p(r)
        kp = mp.mpf(k)
        for j in range(1, order+1):
            val = mp.mpf(0)
            for c in reversed(POLYS[j]):
                val = val*p + c
            kap[j] += kp*val
            kp *= k
        power *= base
    return phi, kap, K

def saddle(n: int | mp.mpf, s: int, order: int = 8,
           guess: mp.mpf | None = None) -> tuple[mp.mpf, mp.mpf, list[mp.mpf], int]:
    n = mp.mpf(n)
    if n <= 0:
        raise ValueError('n must be positive')
    t = mp.mpf(guess) if guess is not None else s*mp.log(mp.sqrt(2*n))/mp.sqrt(2*n)
    if t <= 0:
        t = mp.mpf(1)
    for _ in range(30):
        _, kap, _ = saddle_sums(t, s, 2)
        delta = (kap[1]-n)/kap[2]
        new_t = t+delta
        if new_t <= 0:
            new_t = t/2
        if abs(new_t-t) < mp.power(10, -mp.mp.dps+12) * max(1, t):
            t = new_t
            break
        t = new_t
    else:
        raise ArithmeticError('saddle Newton iteration failed')
    phi, kap, K = saddle_sums(t, s, order)
    return t, phi, kap, K

def multiindices(weight: int, j: int = 3):
    if weight == 0:
        yield {}
        return
    if j-2 > weight:
        return
    for m in range(weight//(j-2)+1):
        for rest in multiindices(weight-m*(j-2), j+1):
            yield ({j:m} | rest) if m else rest

def edgeworth(kap: list[mp.mpf], r: int) -> mp.mpf:
    if r == 0:
        return mp.mpf(1)
    total = mp.mpf(0)
    for ms in multiindices(2*r):
        q = sum(j*m for j,m in ms.items())
        df = math.prod(range(1, q, 2))
        val = mp.mpf((-1)**(q//2) * df)
        for j,m in ms.items():
            val *= (kap[j]/(mp.factorial(j)*kap[2]**(mp.mpf(j)/2)))**m/mp.factorial(m)
        total += val
    return total

def evaluate(n: int, s: int, exact: int) -> dict[str, str | int]:
    t, phi, k, cutoff = saddle(n, s, 8)
    L = -mp.lambertw(-t/s, -1).real
    M = mp.exp(L)
    psi = n*t+phi-mp.log(2*mp.pi*k[2])/2
    loga = mp.log(exact)
    vals = [edgeworth(k, r) for r in range(4)]
    row: dict[str, str | int] = {'s':s, 'n':n, 'cutoff':cutoff}
    for name,val in [('t',t),('L',L),('log_a',loga),('epsilon',1/(s*M*L))]:
        row[name]=mp.nstr(val,35)
    cumulative = mp.mpf(0)
    for j,val in enumerate(vals):
        cumulative += val
        row[f'E{j}'] = mp.nstr(val,35)
        row[f'relative_error_J{j}'] = mp.nstr(mp.expm1(psi-loga)*cumulative+cumulative-1,35)
    # Newton linearized displacement of the Gaussian inverse at A=a_s(n).
    slope = t-k[3]/(2*k[2]**2)
    row['inverse_linear_displacement'] = mp.nstr((loga-psi)/slope,35)
    row['inverse_displacement_scaled'] = mp.nstr((loga-psi)/slope * (-8*s*s*L*L/3),35)
    N=mp.sqrt(2*n); ell=mp.log(N); P=mp.pi**2/s**2
    terms=[ell-1, P/(6*ell), P/(6*ell**2), (P/6-P**2/72)/ell**3,
           (P/6+P**2/40)/ell**4, (P/6+41*P**2/180+P**3/432)/ell**5]
    for j in [0,1,3,5]:
        row[f'log_expansion_error_{j}']=mp.nstr(s*N*sum(terms[:j+1])-loga,35)
    print(s,n,'errors:',*[mp.nstr(mp.mpf(row[f'relative_error_J{j}']),8) for j in range(4)], flush=True)
    return row

def main() -> None:
    parser=argparse.ArgumentParser()
    parser.add_argument('--exact', action='store_true', help='build exact tables')
    parser.add_argument('--s', type=int, default=1)
    parser.add_argument('--nmax', type=int, default=10000)
    parser.add_argument('--samples', type=str, default='100,500,1000,2500,5000,10000')
    parser.add_argument('--dps', type=int, default=50)
    args=parser.parse_args()
    if args.s < 1 or args.nmax < 0 or args.dps < 25:
        parser.error('require s >= 1, nmax >= 0 and dps >= 25')
    OUT.mkdir(exist_ok=True)
    path=OUT/f'exact_s{args.s}.json'
    if args.exact:
        arr=coefficients(args.nmax,args.s)
        if args.s==1:
            initial=[1,1,2,5,7,15,25,43,64,120,186,288,463,695,1105,1728,2525,3741,5775,8244,12447]
            count=min(len(arr),len(initial))
            assert arr[:count]==initial[:count]
        path.write_text(json.dumps([str(x) for x in arr]),encoding='utf-8')
        failures=[n for n in range(1,len(arr)-1) if arr[n]**2<=arr[n-1]*arr[n+1]]
        info={'s':args.s,'nmax':args.nmax,'strict_log_concavity_failures':failures,
              'monotonic_from_1':all(arr[n+1]>arr[n] for n in range(1,len(arr)-1))}
        (OUT/f'exact_audit_s{args.s}.json').write_text(json.dumps(info,indent=2))
        print({'s':args.s,'nmax':args.nmax,
               'strict_log_concavity_failure_count':len(failures),
               'last_tested_failure':failures[-1] if failures else None,
               'monotonic_from_1':info['monotonic_from_1']},flush=True)
    else:
        if not path.exists():
            parser.error(f'{path.name} is missing; run --exact first')
        arr=[int(v) for v in json.loads(path.read_text())]
        try:
            samples=list(map(int,args.samples.split(',')))
        except ValueError:
            parser.error('--samples must be comma-separated integers')
        if not samples or any(n < 1 or n >= len(arr) for n in samples):
            parser.error(f'--samples must lie between 1 and {len(arr)-1}')
        mp.mp.dps=args.dps
        rows=[evaluate(n,args.s,arr[n]) for n in samples]
        dest=OUT/f'saddle_s{args.s}_dps{args.dps}.csv'
        if dest.exists():
            with dest.open(newline='') as f:
                old=list(csv.DictReader(f))
            by_n={int(r['n']):r for r in old}
            by_n.update({int(r['n']):r for r in rows})
            rows=[by_n[n] for n in sorted(by_n)]
        with dest.open('w',newline='') as f:
            wr=csv.DictWriter(f,fieldnames=list(rows[0]));wr.writeheader();wr.writerows(rows)
        print(dest)
if __name__=='__main__':
    main()
