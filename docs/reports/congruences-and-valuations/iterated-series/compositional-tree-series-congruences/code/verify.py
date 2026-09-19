#!/usr/bin/env python3
"""Reproduce the report's finite checks. Standard library only."""
from __future__ import annotations
import csv, json, time
from pathlib import Path
from iterative_series import (coefficients, rational_fixed_point,
    small_core_weights, prufer_core_weights, predicted_mod3, predicted_mod4,
    predicted_multiple5, core_residue)

ROOT = Path(__file__).resolve().parent.parent
DATA = ROOT/'data'
DATA.mkdir(exist_ok=True)
checks = 0

def check(ok: bool, label: str) -> None:
    global checks
    if not ok: raise AssertionError(label)
    checks += 1

def main() -> None:
    started = time.monotonic()
    target = 516114659489378430688740267292635767160672734031357
    exact = coefficients(5,40)
    independent = rational_fixed_point(5,23)
    for n in range(24): check(exact[n] == independent[n],f'independent coefficient {n}')
    check(exact[23] == target,'published a5(23)')
    check(next(n for n in range(1,41) if (exact[n]-n)%5) == 23,'first counterexample')
    with (DATA/'a396805_first40.csv').open('w',newline='') as f:
        writer = csv.writer(f); writer.writerow(['n','a5(n)','mod5','n_mod5','conjecture_holds'])
        for n in range(1,41): writer.writerow([n,exact[n],exact[n]%5,n%5,(exact[n]-n)%5==0])
    # Every check below computes the original series rather than reducing
    # ell or n by the modular-periodicity theorems being tested.
    byell = {ell:coefficients(ell,260,420) for ell in range(13)}
    for ell,a in byell.items():
        for n in range(1,261):
            check(a[n]%2 == n%2,f'parity ell={ell}, n={n}')
            check(a[n]%3 == predicted_mod3(ell,n),f'mod3 ell={ell}, n={n}')
            check(a[n]%4 == predicted_mod4(ell,n),f'mod4 ell={ell}, n={n}')
        for mod,period in [(2,2),(3,6),(4,4),(5,20),(7,42)]:
            for n in range(mod,261-period):
                check(a[n+period]%mod == a[n]%mod,f'period {ell},{mod},{n}')
    core_rows = []
    for ell in range(9):
        for r in range(1,5):
            w = small_core_weights(ell,r)
            check(w == prufer_core_weights(ell,r),f'Pruefer core {ell},{r}')
            check(sum(w.values()) == coefficients(ell,r)[r],f'core count {ell},{r}')
            for p,alpha in [(2,1),(2,2),(2,3),(3,1),(3,2),(5,1),(5,2),(7,1)]:
                m = p**alpha
                if r >= m: continue
                a = coefficients(ell,m*5+r,m)
                for q in range(6):
                    check(a[m*q+r] == core_residue(w,q,p,alpha),f'prime power core {ell},{r},{p},{alpha},{q}')
            if ell in (4,5):
                freq = [sum(v for s,v in w.items() if s%5 == j) for j in range(5)]
                core_rows.append({'ell':ell,'r':r,'frequencies':freq,
                                  'frequencies_mod5':[v%5 for v in freq],
                                  'q_0_to_4':[core_residue(w,q,5) for q in range(5)]})
    for h in range(7):
        a = coefficients(5*h,125,5)
        for n in range(1,126):
            check(a[n] == predicted_multiple5(h,n),f'multiple 5 {h},{n}')
    for n in range(1,261): check(byell[4][n]%5 != 3,f'A396804 avoidance {n}')
    # Nontrivial prime-power and parameter-period tests.
    for ell,m,period in [(2,9,18),(3,16,16),(4,8,8),(5,25,100)]:
        a = coefficients(ell,2*period+m+10,m)
        for n in range(m,len(a)-period): check(a[n+period] == a[n],f'prime power period {ell},{m},{n}')
    for ell,m in [(1,4),(2,5),(3,7),(2,8),(1,9)]:
        left = coefficients(ell,85,m); right = coefficients(ell+m*m,85,m)
        for n in range(1,86): check(left[n] == right[n],f'parameter period {ell},{m},{n}')
    # Explicit infinite-family witnesses for several primes.
    witnesses = []
    for p in [5,7,11,13]:
        n = p*(p-1)+3
        a = coefficients(p,n,p)
        check(a[n] == (3-6)%p,f'general prime witness {p}')
        witnesses.append({'p':p,'ell':p,'n':n,'residue':a[n],'expected':n%p})
    with (DATA/'residues_ell0_to12_n1_to260.csv').open('w',newline='') as f:
        writer=csv.writer(f); writer.writerow(['ell','n','mod2','mod3','mod4','mod5','mod7'])
        for ell,a in byell.items():
            for n in range(1,261): writer.writerow([ell,n]+[a[n]%m for m in [2,3,4,5,7]])
    (DATA/'core_certificates.json').write_text(json.dumps(core_rows,indent=2)+'\n')
    (DATA/'prime_witnesses.json').write_text(json.dumps(witnesses,indent=2)+'\n')
    summary={'status':'all checks passed','assertions':checks,
             'independent_exact_check':'Bell recurrence vs ordinary Fraction fixed point through n=23',
             'first_counterexample':{'ell':5,'n':23,'value':str(target),'residue_mod5':2},
             'broad_grid':{'ell_min':0,'ell_max':12,'n_max':260},
             'wall_seconds':round(time.monotonic()-started,3),
             'scope':'Finite corroboration only. Infinite statements are proved in article.tex.'}
    (DATA/'verification_summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2))

if __name__ == '__main__': main()
