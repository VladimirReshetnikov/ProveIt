"""The singleton case of Lemma 13.5, once, at independent length and precision exponents.

`Proofs13PolyRecurrence.stage135_singleton_at` re-proved
`Proofs13SingletonRecurrence.lemma_13_5_singleton_scale_positive` at one exponent `e` for both the
length (`|P|^e ≤ 2`) and the precision (`2q·e ≤ 1`). The printed lemma uses `1/2^(12q)` for the
first and `1/2^(11q)` for the second, so `stage135_singleton_at` takes the two exponents `eL`, `eP`
separately; it moves upstream together with `IsStage135At` (unchanged body) and
`isStage135Data_iff_at`, and the printed lemma becomes its instance. Its one use (the poly case)
infers `eL = eP = e`.
"""
from foldlib import Fold

F = Fold()
SR, PR = 'Proofs13SingletonRecurrence', 'Proofs13PolyRecurrence'


def sub1(m, a, b):
    s = F.get(m)
    assert s.count(a) == 1, (m, s.count(a), a[:80])
    F.text[m] = s.replace(a, b)


sub1(PR, '''/-- **The singleton scale.** One strong critical height, with a nonzero
step making every phase small, is a Stage 13.5 progression whenever
`|P|^e ≤ 2`. -/''', '''/-- **The singleton scale.** One strong critical height, with a nonzero
step making every phase small, is a Stage 13.5 progression at a length
exponent `eL` with `|P|^eL ≤ 2` and a precision exponent `eP` with
`2q·eP ≤ 1`. -/''')
sub1(PR, '''    (h134 : IsStage134Data S theta D) (hL : 0 < D.P.length) {e : Real} (he : 0 < e)
    (hqe : 2 * (D.q : Real) * e ≤ 1) (hscale : (D.P.length : Real) ^ e ≤ 2) :
    ∃ E : Stage135Data N, IsStage135At S D E e e := by''',
     '''    (h134 : IsStage134Data S theta D) (hL : 0 < D.P.length) {eL eP : Real} (he : 0 < eP)
    (hqe : 2 * (D.q : Real) * eP ≤ 1) (hscale : (D.P.length : Real) ^ eL ≤ 2) :
    ∃ E : Stage135Data N, IsStage135At S D E eL eP := by''')
F.move(PR, ['IsStage135At', 'isStage135Data_iff_at', 'stage135_singleton_at'], SR,
       'lemma_13_5_singleton_scale_positive')
F.reprove(SR, 'lemma_13_5_singleton_scale_positive', ''' by
  have hqn : 2 * D.q ≤ 2 ^ (11 * D.q) := by
    have h := Nat.lt_two_pow_self (n := 11 * D.q)
    omega
  exact stage135_singleton_at S D theta h134 hL (eP := (1 : Real) / (2 : Real) ^ (11 * D.q))
    (by positivity)
    (by rw [mul_one_div]; exact (div_le_one (by positivity)).mpr (by exact_mod_cast hqn)) hscale''')
F.commit()
