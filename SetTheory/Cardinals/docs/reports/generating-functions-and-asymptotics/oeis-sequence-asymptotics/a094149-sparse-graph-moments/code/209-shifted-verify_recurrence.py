"""Independent exact recurrence check of Bauer--Golinelli (2001), Eq. (8).
All code authored locally. No source-repository code is used.
"""
from collections import defaultdict
from math import comb
from pathlib import Path
import json

import argparse
CHECKS = 0
def require(condition, message):
    global CHECKS
    CHECKS += 1
    if not condition:
        raise RuntimeError(str(message))

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--self-test-failure', action='store_true')
args = parser.parse_args()
if args.self_test_failure:
    require(False, 'intentional failure: explicit checks remain active')

N = 16
F = [defaultdict(int) for _ in range(N + 1)]
F[0][0, 0] = 1
for k in range(1, N + 1):
    for q in range(1, k + 1):
        for a in range(k - q + 1):
            b = k - q - a
            for (la, ma), va in F[a].items():
                for (lb, mb), vb in F[b].items():
                    F[k][la + lb + 1, q + mb] += va * vb * comb(ma + q - 1, q - 1) * comb(mb + q - 1, q - 1)
S = [[0] * (N + 1) for _ in range(N + 1)]
S[0][0] = 1
for k in range(1, N + 1):
    for l in range(1, k + 1):
        S[k][l] = S[k - 1][l - 1] + l * S[k - 1][l]
C = [comb(2 * l, l) // (l + 1) for l in range(N + 1)]
rows = []
for k in range(N + 1):
    I = [sum((v for (ell, m), v in F[k].items() if ell == l)) for l in range(k + 1)]
    if not all((S[k][l] <= I[l] <= C[l] * S[k][l] for l in range(k + 1))):
        raise ValueError((k, I))
    rows.append({'k': k, 'edge_coefficients': I, 'M2k': sum(I), 'Bell': sum(S[k]), 'SC': sum((C[l] * S[k][l] for l in range(k + 1)))})
oeis = [1, 3, 12, 57, 303, 1747, 10727, 69331, 467963, 3280353, 23785699, 177877932, 1368977132]
if [r['M2k'] for r in rows[1:14]] != oeis:
    raise ValueError('OEIS prefix mismatch')
expected_k10 = [0, 1, 1022, 31740, 227030, 654395, 968544, 828495, 426360, 125970, 16796]
if rows[10]['edge_coefficients'] != expected_k10:
    raise ValueError('BG table mismatch')
result = {'status': 'passed', 'scope': 'Finite recurrence checks only; these do not replace the report proofs.', 'max_k': N, 'OEIS_A094149_terms_checked': 13, 'Bauer_Golinelli_table_k10_checked': True, 'rows': rows}
data = Path(__file__).parent / 'data'
data.mkdir(exist_ok=True)
(data / 'recurrence_reference.json').write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
for r in rows:
    print(r['k'], r['Bell'], r['M2k'], r['SC'])
