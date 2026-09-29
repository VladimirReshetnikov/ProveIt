"""Independent exact checks. Run with Python 3.10+; no third-party packages."""
from collections import Counter
from fractions import Fraction
from itertools import permutations
from pathlib import Path
import json
from model import (catalan, first_entry, cumulative, scalar_coefficients,
                   eval_poly, isolate_root, component, avoiders, avoids_132)

ROOT = Path(__file__).resolve().parents[1]

def main() -> None:
    report = {'arithmetic': 'integers and fractions only', 'checks': {}}
    checks = report['checks']
    # Independent triple test against recursive Catalan generation.
    for n in range(8):
        direct = {p for p in permutations(range(1,n+1)) if avoids_132(p)}
        assert direct == set(avoiders(n))
    checks['independent_avoidance_sizes'] = '0 through 7'
    cases = 0
    for k in range(1,11):
        blocks = [p for p in avoiders(k) if p[-1] == k]
        counts = Counter(k-p[0] for p in blocks)
        for j in range(k):
            assert counts[j] == first_entry(k,j)
            cases += 1
    checks['first_entry_counts'] = cases
    # Catalan renewal identity and actual V-row coefficientwise domination.
    rows = 0
    for m in range(2,31):
        K = scalar_coefficients(m)
        H = [[catalan(j) for j in range(q+1)] for q in range(m)]
        for q in range(m):
            residual = H[q]+[0]*(m+1-len(H[q]))
            for k in range(1,q+1):
                for j,v in enumerate(H[q-k]):
                    residual[k+j] -= catalan(k-1)*v
            for j,v in enumerate(H[m-1]):
                residual[j+1] -= v
            assert residual == [1]+[-a for a in K[1:]]
        states, edges = component(m,'V')
        actual = [[0]*(m+1) for _ in states]
        for i,j,k,a in edges:
            for h,v in enumerate(H[states[j][1]]):
                actual[i][k+h] += a*v
        for i,(_,q) in enumerate(states):
            # H_q - W v - (1-K_m) has nonnegative coefficients.
            diff = [0]*(m+1)
            for j,v in enumerate(H[q]):
                diff[j] += v
            for j in range(m+1):
                diff[j] -= actual[i][j]
                diff[j] += K[j]
            diff[0] -= 1
            assert all(v >= 0 for v in diff)
            rows += 1
    checks['actual_V_row_polynomial_comparisons'] = rows
    # Uniform Catalan tail inequality, including k <= d+1 boundary cases.
    cases = 0
    for k in range(1,301):
        C = catalan(k-1)
        for d in range(1,31):
            assert 2**d*(C-cumulative(k,d)) <= (d+2)*C
            cases += 1
    checks['uniform_tail_inequalities'] = cases
    # Exact U-submatrix row-sum lower certificate.
    cases = 0
    for m in range(2,31):
        for d in range(1,m):
            for p in range(d,m):
                for k in range(1,m-d+1):
                    assert cumulative(k,p) >= cumulative(k,d)
                    assert m-k >= d
                    cases += 1
    checks['U_submatrix_coefficient_comparisons'] = cases
    # Rational endpoints for scalar corridors (all-m validity is analytic).
    certs = []
    for m,d in [(5,1),(10,2),(20,3),(50,5),(100,7)]:
        klo,khi = isolate_root(scalar_coefficients(m), 42)
        blo,bhi = isolate_root(scalar_coefficients(m,d), 42)
        rec = {'m':m,'d':d,'r_interval':[str(klo),str(khi)],
               's_interval':[str(blo),str(bhi)],
               'alpha_interval':[str(1/bhi),str(1/klo)]}
        assert klo <= khi <= blo <= bhi
        certs.append(rec)
    checks['rational_scalar_corridors'] = len(certs)
    (ROOT/'data'/'rational_certificates.json').write_text(json.dumps(certs,indent=2)+'\n')
    report['result'] = 'PASS (finite checks only; not a proof-assistant certification)'
    (ROOT/'data'/'verification_report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__ == '__main__':
    main()
