#!/usr/bin/env python3
"""Numerical diagnostics for the first asymptotic correction.
Uses only standard-library Decimal arithmetic (70 significant digits).
These are diagnostics, not certified real-arithmetic bounds.
"""
from decimal import Decimal, localcontext
from pathlib import Path
import csv
from verify import full_sets, defect_count

PI = Decimal('3.1415926535897932384626433832795028841971693993751058209749445923078164')

def main() -> None:
    u = full_sets(16)
    out = Path(__file__).parent / 'data' / 'asymptotic_checks.csv'
    records = []
    with localcontext() as ctx:
        ctx.prec = 70
        for d in range(3):
            for q in (8, 10, 12, 14):
                n = 3 * (1 << (q-2))
                m, T = q+d, 1 << (q+d)
                p = Decimal(n) / T
                H = -p*p.ln() - (1-p)*(1-p).ln()
                exact_log = Decimal(defect_count(n,d,u)).ln()
                main_log = (Decimal(u[m]).ln() + T*H + m*p.ln()
                            - (2*PI*T*p*(1-p)).ln()/2)
                c1 = -(1-p)*m*(m-1)/(2*p) + (1-1/p-1/(1-p))/12
                err0 = (main_log-exact_log).exp()-1
                err1 = (main_log-exact_log).exp()*(1+c1/T)-1
                assert abs(err1) < abs(err0)
                records.append([n,d,q,m,T,str(p),str(err0),str(err1)])
    with out.open('w',newline='') as f:
        w=csv.writer(f)
        w.writerow(['n','defect','q','m','T','p','relative_error_leading',
                    'relative_error_first_corrected'])
        w.writerows(records)
    print(f'{len(records)} checks passed: first correction improves every test.')
    for r in records:
        print(f'n={r[0]:5} d={r[1]}  leading={float(r[6]): .4e}'
              f'  corrected={float(r[7]): .4e}')

if __name__=='__main__':
    main()
