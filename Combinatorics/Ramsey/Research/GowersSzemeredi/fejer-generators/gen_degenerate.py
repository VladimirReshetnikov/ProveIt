"""Degenerate family: Lemma 15.4 becomes the case m = 1 of the range count.

  DegenerateRange         : no longer imports DegenerateArrangements; hosts the eight
                            coefficient-independent helpers it used from there (verbatim)
  DegenerateArrangements  : imports DegenerateRange; only lemma_15_4_holds, derived from
                            degenerate_count_within_le at m = 1 via isDegenerateWithin_one_iff
"""
import re
from pathlib import Path

GS = Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean\GowersSzemeredi')
rd = lambda m: (GS / f'{m}.lean').read_text(encoding='utf8')


def wr(m, s):
    (GS / f'{m}.lean').write_text(s, encoding='utf8', newline='\n')


da, dr = rd('Proofs15DegenerateArrangements'), rd('Proofs15DegenerateRange')
HD = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:private |protected )?(?:noncomputable )?(?:theorem|lemma|def|abbrev|structure|instance)\s+([^\s(:{\[]+)", re.M)
hs = list(HD.finditer(da))
DOC = re.compile(r'/--(?:(?!-/).)*-/\s*$', re.S)


def span(k):
    h = hs[k]
    st = h.start()
    m = DOC.search(da[:st])
    if m:
        st = m.start()
    e = hs[k + 1].start() if k + 1 < len(hs) else da.rindex('end LeanProofs')
    m2 = DOC.search(da[:e])
    if m2 and m2.start() > h.start():
        e = m2.start()
    return st, e


MOVE = ['lemma154_double_except_card', 'lemma154_vertex_castSucc', 'lemma154BooleanCoefficient',
        'lemma154_booleanWalshMoment_multilinear', 'lemma154_parity_cube_sum', 'lemma154_append_product',
        'lemma154_vertex_product_univ', 'lemma154_full_moment_eq']
moved = []
for k, h in enumerate(hs):
    if h.group(1) in MOVE:
        a, e = span(k)
        moved.append(da[a:e].rstrip('\n') + '\n')
assert len(moved) == len(MOVE), len(moved)

# --- DegenerateRange
imp = 'import GowersSzemeredi.Proofs15DegenerateArrangements\n'
assert imp in dr
dr = dr.replace(imp, '')
old = ('At `m = 1` this is the printed Lemma 15.4 (`isDegenerateWithin_one_iff`).\n'
       'The file is a copy of `Proofs15DegenerateArrangements` with the coefficient\n'
       'alphabet `Fin (2m+1)` in place of `Fin 3`. -/')
new = ('At `m = 1` this is the printed Lemma 15.4 (`isDegenerateWithin_one_iff`);\n'
       '`Proofs15DegenerateArrangements` derives `lemma_15_4_holds` from it. The\n'
       'helpers `lemma154_*` do not depend on the coefficient alphabet. -/')
assert old in dr
dr = dr.replace(old, new)
anchor = 'namespace LeanProofs.GowersSzemeredi\n\n'
i = dr.index(anchor) + len(anchor)
dr = dr[:i] + '\n'.join(moved) + '\n' + dr[i:]
wr('Proofs15DegenerateRange', dr)

# --- DegenerateArrangements
wr('Proofs15DegenerateArrangements', '''import GowersSzemeredi.Proofs15DegenerateRange

/-!
# Degenerate higher-dimensional arrangements

This file proves Lemma 15.4 as the case `m = 1` of the range count
`degenerate_count_within_le` (`Proofs15DegenerateRange`): with coefficients
in `[−1, 1]` the dependences are exactly the ternary ones
(`isDegenerateWithin_one_iff`).
-/

set_option autoImplicit false

namespace LeanProofs.GowersSzemeredi

/-- Lemma 15.4: the corrected odd-prime bound for degenerate arrangements. -/
theorem lemma_15_4_holds : lemma_15_4 := by
  intro N k d _ hprime hodd hk hd
  have h := degenerate_count_within_le N 1 k d hprime hodd hk hd
  rwa [show degenerateGeneralArrangementCountWithin (N := N) (k := k) 1 d =
      degenerateGeneralArrangementCount d by
    simp only [degenerateGeneralArrangementCountWithin, degenerateGeneralArrangementCount,
      isDegenerateWithin_one_iff], show (2 * ((1 : Nat) : Real) + 1) = 3 by norm_num] at h

end LeanProofs.GowersSzemeredi
''')
print('moved', len(moved), 'declarations')
