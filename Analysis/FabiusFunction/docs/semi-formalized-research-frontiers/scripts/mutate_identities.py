"""Mutation-test check_identities.py: does it actually reject wrong statements?

A gate that never fails is indistinguishable from a gate that cannot fail.  Every entry in
check_identities.py currently passes, which is consistent with two very different situations:
the manuscript's closed forms are right, or the checks are circular and would pass whatever
the formulas said.  Reading the code cannot settle that -- the circularity would be in how a
value is produced, not in anything a reader would notice.

So: perturb the FORMULA UNDER TEST, one mutation at a time, in a scratch copy, and confirm the
gate reports a failure.  A mutation that still passes marks a check with no power over the
statement it claims to verify.

Each mutation is a minimal, plausible transcription slip -- a sign, an off-by-one in a
factorial or binomial, a wrong constant -- of the kind the gate exists to catch.  The real
file is never modified.
"""
import io
import os
import shutil
import subprocess
import sys
import tempfile

if hasattr(sys.stdout, 'reconfigure'):
    sys.stdout.reconfigure(encoding='utf-8', errors='replace')

SRC = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'check_identities.py')

# (label, exact text to replace, replacement)  -- each is a single deliberate error
MUTATIONS = [
    ('second-parity bitwise: & -> |',
     'if (S2[n][k] % 2 == 1) != (((n - k) & w) == 0):',
     'if (S2[n][k] % 2 == 1) != (((n - k) | w) == 0):'),

    ('reverse-row: (i-2)! -> (i-1)!',
     'rhs = sum((factorial(i - 2) * (-1) ** i * comb(m + i, i) if i >= 2 else 0)',
     'rhs = sum((factorial(i - 1) * (-1) ** i * comb(m + i, i) if i >= 2 else 0)'),

    ('reverse-column: drop the sign',
     'rhs = sum((-1) ** j * comb(n, j) * (S2[n - j + 1][k] if n - j + 1 >= k else 0)',
     'rhs = sum(comb(n, j) * (S2[n - j + 1][k] if n - j + 1 >= k else 0)'),

    ('reduced Stirling: shift by d instead of d-1',
     'if _S_reduced(n, k, d) != S2[n - d + 1][k - d + 1]:',
     'if _S_reduced(n, k, d) != S2[n - d][k - d]:'),

    ('det-traces: drop the (-1)^n',
     'if _det(A) != F((-1) ** n, factorial(n)) * bell_complete(tr):',
     'if _det(A) != F(1, factorial(n)) * bell_complete(tr):'),

    ('Bell determinant K: subdiagonal -(i-1) -> -i',
     "else (F(-(i - 1)) if j == i - 1 else F(0)))",
     "else (F(-i) if j == i - 1 else F(0)))"),

    ('Mobius: (m-1)! -> m!',
     'prod *= (-1) ** (m - 1) * factorial(m - 1)',
     'prod *= (-1) ** (m - 1) * factorial(m)'),

    ('Eulerian A(n,1): 2^n-(n+1) -> 2^n-n',
     'if E[n][1] != 2 ** n - (n + 1):',
     'if E[n][1] != 2 ** n - n:'),

    ('modified Bernoulli: 2n^2 -> n^2',
     'if half[n] != Bn[n] / (2 * n * n * factorial(n - 1)):',
     'if half[n] != Bn[n] / (n * n * factorial(n - 1)):'),

    ('harmonic expansion: -1/252 -> -1/250',
     'if abs(float(ratio) - (-1.0 / 252)) >= 1e-6:',
     'if abs(float(ratio) - (-1.0 / 250)) >= 1e-6:'),

    ('Beta integral: n! -> (n+1)!',
     '!= F(factorial(n)) / _poch(a, n + 1):',
     '!= F(factorial(n + 1)) / _poch(a, n + 1):'),

    ('binomial series: (a)_n/n! -> (a)_n/(n+1)!',
     'if c[n] != _poch(a, n) / factorial(n):',
     'if c[n] != _poch(a, n) / factorial(n + 1):'),

    ('associahedral: sign (-1)^m -> +1',
     'tot += F(-1) * a[r - 1] * comp[k]',
     'tot += a[r - 1] * comp[k]'),

    ('near-diagonal: x_{i+1}/(i+1) -> x_{i+1}/i',
     'y = [xs[i] / F(i + 1) for i in range(1, max(a, 1) + 1)]',
     'y = [xs[i] / F(i) for i in range(1, max(a, 1) + 1)]'),

    ('Lagrange-Good: drop the Good determinant',
     '_g_mul(_g_pow(phi2, n2), det))',
     '_g_mul(_g_pow(phi2, n2), _g_one()))'),

    ('inverse-derivative operator: iterate n instead of n-1',
     'cur = _o_mul(invfp, _o_der(cur))',
     'cur = _o_mul(invfp, _o_der(_o_mul(invfp, _o_der(cur))))'),
]

base = io.open(SRC, encoding='utf-8').read()
tmp = tempfile.mkdtemp(prefix='mut_')
survived, killed, skipped = [], [], []

for label, old, new in MUTATIONS:
    if base.count(old) != 1:
        skipped.append((label, base.count(old)))
        continue
    path = os.path.join(tmp, 'check_identities.py')
    io.open(path, 'w', encoding='utf-8', newline='\n').write(base.replace(old, new))
    r = subprocess.run([sys.executable, path], capture_output=True, text=True,
                       encoding='utf-8', errors='replace')
    if r.returncode == 0:
        survived.append(label)
    else:
        killed.append(label)

shutil.rmtree(tmp, ignore_errors=True)

print('mutation test of check_identities.py')
print('  mutations applied : %d' % (len(killed) + len(survived)))
print('  killed (gate FAILED, good) : %d' % len(killed))
print('  SURVIVED (gate still passed, bad) : %d' % len(survived))
if skipped:
    print('  skipped (anchor not unique) : %d' % len(skipped))
    for lab, c in skipped:
        print('     %-52s %d matches' % (lab, c))
print()
for lab in killed:
    print('  killed    %s' % lab)
for lab in survived:
    print('  SURVIVED  %s   <-- this check has no power over its statement' % lab)
print()
print('PASS' if not (survived or skipped) else 'FAIL')

# Exit nonzero if any mutation survived -- and also if an anchor stopped matching, because a
# silently skipped mutation is a mutation that is no longer testing anything.  Reporting a
# problem while exiting 0 is the defect this whole directory exists to avoid.
raise SystemExit(1 if (survived or skipped) else 0)
