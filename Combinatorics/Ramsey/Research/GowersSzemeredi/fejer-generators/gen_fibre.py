"""One small-fibre count for Section 10.

`Proofs10Error.small_fibre_card_bound`, `Proofs10Selection.small_anchor_fibre_card_bound` and
`Proofs10Regular.small_eighth_fibre_card_bound` proved the same fact at the thresholds `5ηα²M`,
`α²M/2` and `α²M/8`: at most `T·N` points lie in fibres of size below `T ≥ 0` (each fibre below
the threshold contributes at most `T` points, and there are `N` fibres). `Proofs10Error` (imported
by the other two) gets `small_fibre_count_le` at any `T`, and the three private lemmas become its
instances.
"""
from foldlib import Fold

F = Fold()
E, S, R = 'Proofs10Error', 'Proofs10Selection', 'Proofs10Regular'
general = '''/-- At most `T·N` points lie in fibres of size below `T ≥ 0`. -/
theorem small_fibre_count_le {N : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X]
    (D : MultifunctionDomain N X) {T : Real} (hT : 0 ≤ T) :
    (countWhere (fun x : X => ¬ T ≤ (D.fibreSize x : Real)) : Real) ≤ T * N := by
  let f : ZMod N → Real := fun s =>
    if T ≤ (D.fibre s).card then 0 else 1
  have hcast :
      (countWhere (fun x : X => ¬ T ≤ (D.fibreSize x : Real)) : Real) =
        ∑ x : X, f (D.index x) := by
    rw [countWhere_cast_eq_sum_ite]
    apply Finset.sum_congr rfl
    intro x _
    unfold MultifunctionDomain.fibreSize
    by_cases hx : T ≤ ((D.fibre (D.index x)).card : Real)
    · simp [f, hx]
    · simp [f, hx]
  rw [hcast, sum_comp_index_eq_sum_mul_fibre]
  calc
    (∑ s : ZMod N, f s * (D.fibre s).card) ≤ ∑ _s : ZMod N, T := by
      apply Finset.sum_le_sum
      intro s _
      by_cases hs : T ≤ ((D.fibre s).card : Real)
      · simp [f, hs, hT]
      · have hle : ((D.fibre s).card : Real) ≤ T := le_of_not_ge hs
        simpa [f, hs] using hle
    _ = T * N := by simp [ZMod.card, mul_comm]
'''
assert 'small_fibre_count_le' not in ''.join(F.get(m) for m in (E, S, R))
F.insert(E, general, 'small_fibre_card_bound')
F.reprove(E, 'small_fibre_card_bound', '''
  small_fibre_count_le D (T := 5 * eta * alpha ^ 2 * M) (by positivity)''')
F.reprove(S, 'small_anchor_fibre_card_bound', '''
  (small_fibre_count_le D (T := alpha ^ 2 * M / 2) (by positivity)).trans_eq (by ring)''')
F.reprove(R, 'small_eighth_fibre_card_bound', '''
  (small_fibre_count_le D (T := alpha ^ 2 * M / 8) (by positivity)).trans_eq (by ring)''')
F.commit()
