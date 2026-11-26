import IPRADerivations.Combinatorics.BinomialTwo

/-!
# Polynomial translation

Packet: `algebra/FTA_iPRA` (the proof of `lem:descent`: "Translation uses only the finite binomial
identity"; writing `P(z + W) = ∑ bᵢ Wⁱ`). For a polynomial `P(X) = ∑_{j ≤ d} a_j X^j` with
coefficients given by a body `a(j, p)`:

  `P(z + w) = ∑_{i ≤ d} wⁱ bᵢ`,  `bᵢ = ∑_{j ≤ d} C(j, i) a_j z^(j−i)`.

The parameter is `x = ⟨⟨z, w⟩, p⟩`. Coefficients and variables are natural numbers; an integer
polynomial is a difference of two such.

* `head_pt`, `tail_pt`: each power `(z + w)^j` is expanded by `Combinatorics/BinomialTwo`, and the
  inner range is extended to `i ≤ d`, where the extra terms carry `C(j, i) = 0`;
* `translation`: `∑_{j ≤ d} a_j (z + w)^j = ∑_{i ≤ d} ∑_{j ≤ d} C(j, i) a_j wⁱ z^(j−i)`, by
  exchanging the two sums (`Core/Fubini`);
* `coef_pt`: the inner sum is `wⁱ bᵢ`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Algebra.PolynomialTranslation

open_ipra
open LeanProofs.IPRA.Combinatorics.Vandermonde (gb congrGb gb_above zB zsum inst2_z)
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrPw)
open LeanProofs.IPRA.Combinatorics.BinomialTwo (bt S bt_at binomial_two)
open LeanProofs.IPRA.Probability.Independence (sum_scale)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

section Bodies

variable (a : PTm 2)

/-- `a_j (z + w)^j`; variables `0 = j`, `1 = x = ⟨⟨z, w⟩, p⟩`. -/
abbrev pB0 : PTm 2 :=
  Syn.subst ![var 0, sndT (var 1)] a * pw (fstT (fstT (var 1)) + sndT (fstT (var 1))) (var 0)
/-- `a_j C(j, i) wⁱ z^(j−i)`; variables `0 = j`, `1 = i`, `2 = x`. -/
abbrev a3 : PTm 3 :=
  Syn.subst ![var 0, sndT (var 2)] a * gb (var 0) (var 1) * pw (sndT (fstT (var 2))) (var 1) *
    pw (fstT (fstT (var 2))) (monus (var 0) (var 1))
/-- `a_j C(j, i) z^(j−i)`; variables `0 = j`, `1 = ⟨i, x⟩`. -/
abbrev bB : PTm 2 :=
  Syn.subst ![var 0, sndT (sndT (var 1))] a * gb (var 0) (fstT (var 1)) *
    pw (fstT (fstT (sndT (var 1)))) (monus (var 0) (fstT (var 1)))

theorem inst2_pB0 (J x : PTm n) :
    inst2 (pB0 a) J x = inst2 a J (sndT x) * pw (fstT (fstT x) + sndT (fstT x)) J := by
  have h : Syn.subst ![J, x] (Syn.subst ![var 0, sndT (var 1)] a) = inst2 a J (sndT x) := by
    simp only [inst2, Syn.subst_subst]; congr 1; funext i; fin_cases i <;> simp
  simp only [inst2, pB0, PTm.subst_mul, h]
  simp [inst2]

theorem inst3_a3 (J I x : PTm n) :
    inst3 (a3 a) J I x = inst2 a J (sndT x) * gb J I * pw (sndT (fstT x)) I * pw (fstT (fstT x)) (monus J I) := by
  have h : Syn.subst ![J, I, x] (Syn.subst ![var 0, sndT (var 2)] a) = inst2 a J (sndT x) := by
    simp only [inst2, Syn.subst_subst]; congr 1; funext i; fin_cases i <;> simp
  simp only [inst3, a3, PTm.subst_mul, h]
  simp [inst2]

theorem inst2_bB (J y : PTm n) :
    inst2 (bB a) J y = inst2 a J (sndT (sndT y)) * gb J (fstT y) * pw (fstT (fstT (sndT y))) (monus J (fstT y)) := by
  have h : Syn.subst ![J, y] (Syn.subst ![var 0, sndT (sndT (var 1))] a) = inst2 a J (sndT (sndT y)) := by
    simp only [inst2, Syn.subst_subst]; congr 1; funext i; fin_cases i <;> simp
  simp only [inst2, bB, PTm.subst_mul, h]
  simp [inst2]

end Bodies

/-! ## Expanding each power -/

section Expand

variable (a : PTm 2)

theorem head_pt (I J x : PTm n) :
    Γ ⊢[PRAAx] inst2 (rowB (a3 a)) I (pairT J x) ≐
      inst2 a J (sndT x) * inst2 bt I (pairT J (pairT (sndT (fstT x)) (fstT (fstT x)))) := by
  rw [inst2_rowB, inst3_a3]
  refine .eqTrans ?_ (congrMul (.eqRefl _) (bt_at _ _ _ _)).eqSymm
  refine (congrMul (congrMul (congrMul (congrInst2 a (fst_pair _ _) (congrSnd (snd_pair _ _)))
    (congrGb (fst_pair _ _) (.eqRefl _))) (congrPw (congrSnd (congrFst (snd_pair _ _))) (.eqRefl _)))
    (congrPw (congrFst (congrFst (snd_pair _ _))) (congrMonus (fst_pair _ _) (.eqRefl _)))).eqTrans ?_
  ipra_ring

theorem tail_pt (I J x : PTm n) :
    Γ ⊢[PRAAx] inst2 (offB (rowB (a3 a))) I (pairT (succ J) (pairT J x)) ≐ zero := by
  rw [inst2_offB, inst2_rowB, inst3_a3]
  have g : Γ ⊢[PRAAx] gb (fstT (sndT (pairT (succ J) (pairT J x))))
      (fstT (pairT (succ J) (pairT J x)) + I) ≐ zero :=
    (congrGb (snd_pair _ _).fstE (congrAdd (fst_pair _ _) (.eqRefl _))).eqTrans
      (gb_above (le_add_right (succ J) I))
  exact (congrMul (congrMul (congrMul (.eqRefl _) g) (.eqRefl _)) (.eqRefl _)).eqTrans
    ((congrMul (congrMul (mul_zero _) (.eqRefl _)) (.eqRefl _)).eqTrans
      ((congrMul (zero_mul _) (.eqRefl _)).eqTrans (zero_mul _)))

/-- `a_J (z + w)^J = ∑_{i ≤ d} a_J C(J, i) wⁱ z^(J−i)` for `J ≤ d`. -/
theorem expand_pt {J d : PTm n} (x : PTm n) (hJ : Γ ⊢[PRAAx] le J d) :
    Γ ⊢[PRAAx] inst2 (pB0 a) J x ≐ inst2 (oB (a3 a)) J (pairT (succ d) x) := by
  rw [inst2_pB0, inst2_oB]
  refine .eqTrans ?_ (congrAp2 (sumF (rowB (a3 a))) (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _))).eqSymm
  have eD : Γ ⊢[PRAAx] succ d ≐ succ J + monus d J := by
    have e := natEq (eq_add_of_le hJ)
    apply deriveNat; ipra_simps; linear_combination e
  refine .eqTrans ?_ (congrAp2 (sumF (rowB (a3 a))) eD (.eqRefl _)).eqSymm
  refine .eqTrans ?_ (sum_split (rowB (a3 a)) (succ J) (monus d J) (pairT J x)).eqSymm
  have H : Γ ⊢[PRAAx] ap2 (sumF (rowB (a3 a))) (succ J) (pairT J x) ≐
      inst2 a J (sndT x) * S J (sndT (fstT x)) (fstT (fstT x)) := by
    refine sum_scale _ _ _ _ _ _ (.allI (.impI ?_))
    have e₁ : Syn.shift (pairT J x) = pairT (Syn.shift J) (Syn.shift x) := by simp [Syn.shift]
    have e₂ : Syn.shift (inst2 a J (sndT x)) = inst2 a (Syn.shift J) (sndT (Syn.shift x)) := by
      simp [Syn.shift, subst_inst2]
    have e₃ : Syn.shift (pairT J (pairT (sndT (fstT x)) (fstT (fstT x)))) =
        pairT (Syn.shift J) (pairT (sndT (fstT (Syn.shift x))) (fstT (fstT (Syn.shift x)))) := by simp [Syn.shift]
    rw [e₁, e₂, e₃]
    exact head_pt a _ _ _
  have Z : Γ ⊢[PRAAx] ap2 (sumF (offB (rowB (a3 a)))) (monus d J) (pairT (succ J) (pairT J x)) ≐ zero := by
    refine (sum_congr_bounded _ zB (pairT (succ J) (pairT J x)) (pairT (succ J) (pairT J x)) _
      (.allI (.impI ?_))).eqTrans (zsum _ _)
    have e : Syn.shift (pairT (succ J) (pairT J x)) = pairT (succ (Syn.shift J)) (pairT (Syn.shift J) (Syn.shift x)) := by
      simp [Syn.shift]
    rw [e, inst2_z]
    exact tail_pt a _ _ _
  refine .eqTrans ?_ (congrAdd H Z).eqSymm
  refine .eqTrans ?_ (add_zero _).eqSymm
  exact congrMul (.eqRefl _) ((congrPw (add_comm _ _) (.eqRefl _)).eqTrans (binomial_two _ _ _).eqSymm)

/-- `∑_{j ≤ d} a_j (z + w)^j = ∑_{i ≤ d} ∑_{j ≤ d} C(j, i) a_j wⁱ z^(j−i)`. -/
theorem translation (d x : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (pB0 a)) (succ d) x ≐ ap2 (sumF (pB (a3 a))) (succ d) (pairT (succ d) x) := by
  refine (sum_congr_bounded (pB0 a) (oB (a3 a)) x (pairT (succ d) x) (succ d) (.allI (.impI ?_))).eqTrans
    (fubini (a3 a) (succ d) (succ d) x)
  have e : Syn.shift (pairT (succ d) x) = pairT (succ (Syn.shift d)) (Syn.shift x) := by simp [Syn.shift]
  have e' : Syn.shift (succ d) = succ (Syn.shift d) := by simp [Syn.shift]
  rw [e]
  rw [e'] at *
  exact expand_pt a _ ((succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0)

/-- The inner sum: `∑_{j ≤ d} C(j, i) a_j wⁱ z^(j−i) = wⁱ bᵢ`. -/
theorem coef_pt (I d x : PTm n) :
    Γ ⊢[PRAAx] inst2 (pB (a3 a)) I (pairT (succ d) x) ≐
      pw (sndT (fstT x)) I * ap2 (sumF (bB a)) (succ d) (pairT I x) := by
  rw [inst2_pB]
  refine (congrAp2 (sumF (colB (a3 a))) (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _))).eqTrans ?_
  refine sum_scale _ _ _ _ _ _ (.allI (.impI ?_))
  have e₁ : Syn.shift (pairT I x) = pairT (Syn.shift I) (Syn.shift x) := by simp [Syn.shift]
  have e₂ : Syn.shift (pw (sndT (fstT x)) I) = pw (sndT (fstT (Syn.shift x))) (Syn.shift I) := by simp [Syn.shift]
  rw [e₁, e₂, inst2_colB, inst3_a3, inst2_bB]
  have fI : (lt (var 0) (Syn.shift (succ d)) :: Γ.map Fm.shift) ⊢[PRAAx]
      fstT (pairT (Syn.shift I) (Syn.shift x)) ≐ Syn.shift I := fst_pair _ _
  have sx : (lt (var 0) (Syn.shift (succ d)) :: Γ.map Fm.shift) ⊢[PRAAx]
      sndT (pairT (Syn.shift I) (Syn.shift x)) ≐ Syn.shift x := snd_pair _ _
  refine (congrMul (congrMul (congrMul (congrInst2 a (.eqRefl _) (congrSnd sx)) (congrGb (.eqRefl _) fI))
    (congrPw (congrSnd (congrFst sx)) fI)) (congrPw (congrFst (congrFst sx)) (congrMonus (.eqRefl _) fI))).eqTrans ?_
  refine .eqTrans ?_ (congrMul (.eqRefl _) (congrMul (congrMul (congrInst2 a (.eqRefl _) (congrSnd sx))
    (congrGb (.eqRefl _) fI)) (congrPw (congrFst (congrFst sx)) (congrMonus (.eqRefl _) fI)))).eqSymm
  ipra_ring

end Expand

end LeanProofs.IPRA.Algebra.PolynomialTranslation
