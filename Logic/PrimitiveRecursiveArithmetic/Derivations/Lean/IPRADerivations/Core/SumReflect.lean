import IPRADerivations.Core.SumLemmas

/-!
# Reflecting a finite sum

For a body `g(i, p)`: `∑_{i<N} g(i, p) = ∑_{i<N} g(N − 1 − i, p)`.

The reflected body needs `N` as well as `p`, so it reads its parameter as a pair `y = ⟨N, p⟩`:
`rflBody g (i, y) = g(fst y ∸ (i + 1), snd y)`. The identity is proved by induction on `N`:
the new last term `g(N, p)` on the left is the new first term on the right (`sum_shift`).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA

open LeanProofs.ConciseIPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `g(fst y ∸ (i + 1), snd y)`. -/
def rflBody (g : PTm 2) : PTm 2 := Syn.subst ![monus (fstT (var 1)) (succ (var 0)), sndT (var 1)] g

theorem inst2_rflBody (g : PTm 2) (i y : PTm n) :
    inst2 (rflBody g) i y = inst2 g (monus (fstT y) (succ i)) (sndT y) := by
  simp only [inst2, rflBody, Syn.subst_subst]
  congr 1; funext j; fin_cases j <;> simp

theorem shift_pairT (a b : PTm n) : Syn.shift (pairT a b) = pairT (Syn.shift a) (Syn.shift b) := by
  simp [Syn.shift]

/-- Variables: `0 = N`, `1 = p`. -/
private abbrev reflF (g : PTm 2) : Fm PTm 2 :=
  ap2 (sumF g) (var 0) (var 1) ≐ ap2 (sumF (rflBody g)) (var 0) (pairT (var 0) (var 1))

private theorem sum_reflect₀ (g : PTm 2) : ([] : List (Fm PTm 2)) ⊢[PRAAx] reflF g := by
  ipra_ind [subst_ap2, subst_pairT]
  · exact (sum_zero _ _).eqTrans (sum_zero _ _).eqSymm
  · refine (sum_succ' g (var 0) (var 1)).eqTrans ((congrAdd Prf.hyp0 (.eqRefl _)).eqTrans ?_)
    refine (add_comm _ _).eqTrans (.eqTrans ?_ (sum_shift (rflBody g) (var 0) _).eqSymm)
    refine congrAdd ?_ ?_
    · rw [inst2_rflBody]
      exact congrInst2 g (((congrMonus (fst_pair _ _) (.eqRefl _)).eqTrans
        ((succ_monus_succ _ _).eqTrans (monus_zero _))).eqSymm) (snd_pair _ _).eqSymm
    · refine sum_congr_bounded (rflBody g) (shiftBody (rflBody g)) _ _ (var 0) (.allI (.impI ?_))
      rw [inst2_shiftBody, inst2_rflBody, inst2_rflBody, shift_pairT, shift_pairT]
      refine congrInst2 g ?_ ((snd_pair _ _).eqTrans (snd_pair _ _).eqSymm)
      exact (congrMonus (fst_pair _ _) (.eqRefl _)).eqTrans ((succ_monus_succ _ _).eqSymm.eqTrans
        (congrMonus (fst_pair _ _).eqSymm (.eqRefl _)))

/-- `∑_{i<N} g(i, p) = ∑_{i<N} g(N − 1 − i, p)`. -/
theorem sum_reflect (g : PTm 2) (N p : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF g) N p ≐ ap2 (sumF (rflBody g)) N (pairT N p) := by
  have h := inst (Γ := Γ) (sum_reflect₀ g) (![N, p] : Fin 2 → PTm n)
  simpa using h

end LeanProofs.IPRA
