"""Lemma 13.1 reuses Proposition 6.1's fourth-moment count.

`Proofs13Basic` (Lemma 13.1) restated seven private declarations of `Proofs05_10`
(Proposition 6.1) up to renaming: `prop131G` is `prop61G`, and the quadruple predicates, the
alternative count, the two product sums and the fourth-moment count are the `prop61_…` proofs
with `sigma` for `phi`. They move, public, to a new module `Proofs06PhiAdditiveFourier`, imported
by both. It imports only `Proofs01_03`, which both already import, so no other closure changes.
"""
import re

from foldlib import Fold, GS

F = Fold()
P6, P13, NEW = 'Proofs05_10', 'Proofs13Basic', 'Proofs06PhiAdditiveFourier'
CORE = ['prop61G', 'prop61QuadMem', 'prop61AltAdditive', 'prop61_alt_count_eq', 'prop61_g_product',
        'prop61_sum_g_product', 'prop61_g_fourth_eq_count']
moved = [F.take(P6, n) for n in CORE]
body = '\n'.join(b.replace('private ', '', 1) for b in moved)
other = set(re.findall(r'\bprop61\w*', body)) - set(CORE)
assert not other, other
assert 'private' not in body, body[:200]
header = '''import GowersSzemeredi.Proofs01_03

/-! The fourth moment of `x ↦ 1_B(x)·e(φ(x)·u)`, summed over `u`.

With `prop61G B φ u = 1_B · e(φ·u)`, the fourth moments of the Fourier
transforms count the `φ`-additive quadruples of `B`:
`∑_u ∑_r ‖(prop61G B φ u)^(r)‖⁴ = N²·phiAdditiveCount B φ`
(`prop61_g_fourth_eq_count`). Proposition 6.1 (`Proofs05_10`) and Lemma 13.1
(`Proofs13Basic`) both use it. -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise ZMod Combinatorics.Additive
open Finset

namespace LeanProofs.GowersSzemeredi

'''
F.text[NEW] = header + body.rstrip('\n') + '\n\nend LeanProofs.GowersSzemeredi\n'
assert not (GS / f'{NEW}.lean').exists()

for n in ['prop131G', 'prop131QuadMem', 'prop131AltAdditive', 'prop131_alt_count_eq', 'prop131_g_product',
          'prop131_sum_g_product', 'prop131_g_fourth_eq_count']:
    F.delete_decl(P13, n)
s = F.get(P13)
for a in ['prop131G', 'prop131QuadMem', 'prop131AltAdditive', 'prop131_alt_count_eq', 'prop131_g_product',
          'prop131_sum_g_product', 'prop131_g_fourth_eq_count']:
    s = re.sub(r"(?<![\w'])" + a + r"(?![\w'])", a.replace('prop131', 'prop61'), s)
F.text[P13] = s
for m in (P6, P13):
    s = F.get(m)
    line = 'import GowersSzemeredi.Proofs01_03\n'
    assert s.count(line) == 1, m
    F.text[m] = s.replace(line, line + f'import GowersSzemeredi.{NEW}\n', 1)
F.commit()
print('new module', NEW, '- add it to the facade when publishing')
