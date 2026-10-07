#!/usr/bin/env python3
"""Optional mpmath diagnostics, separated from all exact arithmetic.

No OEIS b-file is read. Exact counts are recomputed from finite products.
Reported residuals are numerical checks, never rigorous error certificates.
"""
import argparse
import json
from pathlib import Path
from exact import radial_coefficients, coefficient_transfer, partition_counts, nonnegative_cli


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path, help='new output JSON; otherwise stdout')
    parser.add_argument('--max-n', type=nonnegative_cli, default=10000)
    parser.add_argument('--dps', type=nonnegative_cli, default=80)
    parser.add_argument('--radial', action='store_true', help='also evaluate finite-product radial sums')
    args = parser.parse_args()
    if args.dps < 30:
        parser.error('--dps must be at least 30')
    if args.out is not None and args.out.exists():
        parser.error('--out must not already exist')
    try:
        import mpmath as mp
    except ImportError as error:
        raise SystemExit('Optional diagnostics require mpmath; the exact build does not.') from error
    mp.mp.dps = args.dps
    def rational(q):
        return mp.mpf(q.numerator)/q.denominator
    def field(q):
        return rational(q.a)+rational(q.b)*mp.sqrt(5)
    def text(value):
        return mp.nstr(value, min(args.dps-10, 50))
    A = mp.pi**2/30
    B = 2*mp.sqrt(A)
    C = 1/mp.sqrt(5+mp.sqrt(5))
    phi = (1+mp.sqrt(5))/2
    lam = mp.sqrt(2*mp.pi/(mp.sqrt(5)*phi))
    exact_cs = radial_coefficients(4)
    cs = [field(c) for c in exact_cs]
    ds = [mp.fsum(field(v)*mp.sqrt(A)**k for k,v in p.items())
          for p in coefficient_transfer(exact_cs)]
    logs = [mp.mpf(0)]
    for r in range(1, 5):
        logs.append(ds[r]-mp.fsum(k*logs[k]*ds[r-k] for k in range(1,r))/r)
    alpha = [logs[r]*B**r for r in range(5)]
    counts = partition_counts(args.max_n)
    samples = sorted({n for n in (1000,2000,5000,10000,args.max_n) if 10 <= n <= args.max_n})
    rows = []
    for n in samples:
        y = mp.mpf(counts[n])
        lead = C*mp.exp(B*mp.sqrt(n))/mp.sqrt(n)
        row = {'n': n, 'exact_a_n': str(counts[n]),
               'relative_error': {str(j): text(lead*mp.fsum(ds[r]/mp.sqrt(n)**r for r in range(j+1))/y-1)
                                  for j in range(5)},
               'd4_scaled_residual_after_d3': text((y/lead-mp.fsum(ds[r]/mp.sqrt(n)**r for r in range(4)))*n*n)}
        T = mp.log(y/(C*B))
        inverse_errors = {}
        # The inverse is tested only where the large positive branch is clear.
        if T > 2:
            for order in (3,4):
                equation = lambda s: s-mp.log(s)+mp.fsum(alpha[r]/s**r for r in range(1,order+1))-T
                derivative = lambda s: 1-1/s-mp.fsum(r*alpha[r]/s**(r+1) for r in range(1,order+1))
                root = mp.findroot(equation, T+mp.log(T), df=derivative, solver='newton')
                if root <= 0 or derivative(root) <= 0:
                    raise ArithmeticError('numerical inverse did not reach the large positive branch')
                inverse_errors[str(order)] = text((root/B)**2-n)
        row['implicit_inverse_index_error'] = inverse_errors
        rows.append(row)
    output = {'diagnostic_only': True, 'mpmath_version': mp.__version__, 'decimal_precision': args.dps,
              'count_origin': 'exact integer finite-product DP, independently checked through n=400',
              'counts_max_n': args.max_n, 'c': [text(v) for v in cs], 'd': [text(v) for v in ds],
              'coefficient_comparisons': rows}
    if args.radial:
        radial = []
        for ts in ('0.002','0.001','0.0005','0.00025'):
            t = mp.mpf(ts)
            cutoff = int(mp.ceil(4/t))
            logs = [mp.mpf(0)]
            for j in range(1,2*cutoff+1):
                logs.append(logs[-1]-mp.log(-mp.expm1(-t*j)))
            normalized = mp.fsum(mp.exp(-3*k*t+logs[2*k]-logs[k-1]-A/t)
                                 for k in range(1,cutoff+1))*mp.sqrt(t)/lam
            residual = (normalized-mp.fsum(cs[j]*t**j for j in range(4)))/t**4
            radial.append({'t': ts, 'finite_sum_k_max': cutoff,
                           'c4_scaled_residual_after_c3': text(residual),
                           'residual_minus_c4': text(residual-cs[4])})
        output['radial_finite_sum_comparisons'] = radial
        output['radial_caveat'] = 'Finite k cutoff only; no certified truncation or rounding error bound.'
    data = json.dumps(output, sort_keys=True, indent=2)+'\n'
    if args.out is None:
        print(data, end='')
    else:
        with args.out.open('x', encoding='utf-8') as handle:
            handle.write(data)


if __name__ == '__main__':
    main()
