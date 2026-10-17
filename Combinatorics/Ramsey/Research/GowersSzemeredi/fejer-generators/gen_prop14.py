"""Proposition 14.1 reuses Proposition 12.1's fourth-moment identity.

`Proofs14Fourier` restated four private declarations of `Proofs12` up to renaming: `prop141B` is
`prop121B`, and `prop141_b_product`, `prop141_sum_b_product`, `prop141_fourthB_eq_weight` are the
`prop121_…` proofs with `sigma` for `phi`. They were copies because the originals were private.
`prop121B` and `prop121_fourthB_eq_weight` become public, `Proofs14Fourier` imports `Proofs12` (its
only new module; the two global simp attributes of `Proofs12` are already set by `Proofs01_03`),
and the copies are deleted.
"""
import re

from foldlib import Fold

F = Fold()
P12, P14 = 'Proofs12', 'Proofs14Fourier'
s = F.get(P12)
for pat in ['private def prop121B ', 'private lemma prop121_fourthB_eq_weight ']:
    assert s.count(pat) == 1, pat
    s = s.replace(pat, pat.replace('private ', '', 1))
F.text[P12] = s
for n in ['prop141B', 'prop141_b_product', 'prop141_sum_b_product', 'prop141_fourthB_eq_weight']:
    F.delete_decl(P14, n)
t = F.get(P14)
for a, b in [('prop141B', 'prop121B'), ('prop141_fourthB_eq_weight', 'prop121_fourthB_eq_weight')]:
    t = re.sub(r"(?<![\w'])" + a + r"(?![\w'])", b, t)
assert not re.search(r'\bprop141_(sum_)?b_product\b', t)
line = 'import GowersSzemeredi.Proofs01_03\n'
assert t.count(line) == 1
t = t.replace(line, line + 'import GowersSzemeredi.Proofs12\n', 1)
F.text[P14] = t
F.commit()
