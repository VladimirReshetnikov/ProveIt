"""Independent exact audit of the complete-core group-basis identity."""
from functools import lru_cache
from itertools import combinations
from math import comb
from pathlib import Path
import json
import sympy as S

@lru_cache(None)
def match(rows):
    if not rows:
        return True
    row = min(rows, key=int.bit_count)
    if row == 0:
        return False
    rest = list(rows)
    rest.remove(row)
    while row:
        bit = row & -row
        row -= bit
        if match(tuple(r & ~bit for r in rest)):
            return True
    return False

def check(n, m):
    left, right = n + 2, m + 2
    total = left + right
    rows = [(1 << right) - 1] * 2 + [3] * n
    actual = set()
    for I in range(1 << left):
        indices = [i for i in range(left) if I >> i & 1]
        for cols in combinations(range(right), len(indices)):
            J = sum(1 << j for j in cols)
            if match(tuple(rows[i] & J for i in indices)):
                actual.add((((1 << left) - 1) ^ I) | (J << left))
    A = {0, 1} | set(range(left + 2, total))
    expected = {
        sum(1 << i for i in basis)
        for basis in combinations(range(total), left)
        if len(set(basis) & A) <= 2
    }
    assert actual == expected, (n, m, actual ^ expected)
    by_group = [sum(1 for b in actual if sum(bool(b >> i & 1) for i in A) == k)
                for k in range(3)]
    formula = [comb(m + 2, k) * comb(n + 2, k) for k in range(3)]
    assert by_group == formula, (n, m, by_group, formula)
    return {'n': n, 'm': m, 'basis_count': len(actual), 'group_coefficients': by_group}

if __name__ == '__main__':
    records = [check(n, m) for n in range(7) for m in range(7)]
    M, N = S.symbols('M N')
    assert S.expand(M*M*N*N-M*(M-1)*N*(N-1)-M*N*(M+N-1)) == 0
    report = {'graphs_checked': len(records), 'basis_identity': True,
              'group_diagonal_coefficients': True, 'discriminant_identity': True,
              'records': records}
    path = Path(__file__).with_name('complete_core_verification.json')
    path.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items() if k != 'records'}))
