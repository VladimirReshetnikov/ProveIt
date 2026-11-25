import IPRADerivations.AnalyticNumberTheory.Totatives
import IPRADerivations.AnalyticNumberTheory.LcmBridgeExact
import IPRADerivations.AnalyticNumberTheory.LocalFactor
import IPRADerivations.AnalyticNumberTheory.SumPhi
import IPRADerivations.Combinatorics.BinomialTheorem

/-!
# Pairing along an involution

Framework layer (first use: Euler's criterion and Wilson's product for
`diophantine-number-theory/quadratic_reciprocity_ipra`, §"A square test from an involution", `eq:pair`).

Let `σ` be an involution of `[0, M)`, given as a body `S` with `σ(i) = S(i, x)`: it maps `[0, M)` into itself and
`σ(σ(i)) = i` for `i < M` (the hypotheses `rangeAll`, `invAll`, `retAll` of `Core/Permutation` with `τ = σ`). The
indices split into the `i < σ(i)`, the `i > σ(i)` and the fixed points, with indicators

  `L(i) = [i < σ(i)]`,   `G(i) = [σ(i) < i]`,   `E(i) = [i = σ(i)]`              (`LB`, `GB`, `EB`).

Since `σ` exchanges the first two classes, for every body `F`:

* `pair_count`: `2 Σ_{i<M} L(i) + Σ_{i<M} E(i) = M`;
* `pair_prod`: `∏_{i<M} F(i) = ∏_{i<M} (F(i) F(σ(i)))^{L(i)} · ∏_{i<M} F(i)^{E(i)}`.

The second is the packet's "assign each `x` to the row `min(x, T(x))`": every two-element orbit `{i, σ(i)}`
contributes the product `F(i) F(σ(i))` once, and every fixed point contributes `F(i)`. The proof needs no array:
`∏ F^G = ∏ (F ∘ σ)^{G ∘ σ}` by `Permutation.prod_perm`, and `G ∘ σ = L`.

* `tri`: exactly one of `L`, `G`, `E` is `1`;
* `tri_sum`, `tri_pw`: `L + G + E = 1` and `f^L f^G f^E = f`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.InvolutionPairing

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Signum (sg sg_zero)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (congrSg one_inst inst2_mulB)
open LeanProofs.IPRA.AnalyticNumberTheory.Totatives (sum_perm sg_lt sg_le)
open LeanProofs.IPRA.AnalyticNumberTheory.LcmBridgeExact (prod_mul)
open LeanProofs.IPRA.AnalyticNumberTheory.LocalFactor (pw_mul_base)
open LeanProofs.IPRA.AnalyticNumberTheory.SumPhi (sum_ones)
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrPw)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## The trichotomy -/

/-- Exactly one of `[i < s]`, `[s < i]`, `[i = s]` is `1`. -/
theorem tri (i s : PTm n) :
    Γ ⊢[PRAAx] ((sg (monus s i) ≐ one) ⋏ ((sg (monus i s) ≐ zero) ⋏ (eqb i s ≐ zero))) ⋎
      (((sg (monus s i) ≐ zero) ⋏ ((sg (monus i s) ≐ one) ⋏ (eqb i s ≐ zero))) ⋎
        ((sg (monus s i) ≐ zero) ⋏ ((sg (monus i s) ≐ zero) ⋏ (eqb i s ≐ one)))) := by
  refine .orE (lt_or_le i s) ?_ ?_
  · have h : (lt i s :: Γ) ⊢[PRAAx] lt i s := Prf.hyp0
    have ne : (lt i s :: Γ) ⊢[PRAAx] neg (i ≐ s) :=
      .impI (lt_irrefl i _ (lt_congr (.eqRefl _) (Prf.hyp0 : ((i ≐ s) :: lt i s :: Γ) ⊢[PRAAx] i ≐ s).eqSymm h.wk))
    exact .orI₁ (.andI (sg_lt h) (.andI (sg_le (le_of_lt h)) (eqb_of_ne ne)))
  · refine .orE (lt_or_eq_of_le (Prf.hyp0 : (le s i :: Γ) ⊢[PRAAx] le s i)) ?_ ?_
    · have h : (lt s i :: le s i :: Γ) ⊢[PRAAx] lt s i := Prf.hyp0
      have ne : (lt s i :: le s i :: Γ) ⊢[PRAAx] neg (i ≐ s) :=
        .impI (lt_irrefl s _ (lt_congr (.eqRefl _)
          (Prf.hyp0 : ((i ≐ s) :: lt s i :: le s i :: Γ) ⊢[PRAAx] i ≐ s) h.wk))
      exact .orI₂ (.orI₁ (.andI (sg_le (le_of_lt h)) (.andI (sg_lt h) (eqb_of_ne ne))))
    · have e : ((s ≐ i) :: le s i :: Γ) ⊢[PRAAx] s ≐ i := Prf.hyp0
      have l1 : ((s ≐ i) :: le s i :: Γ) ⊢[PRAAx] le s i := Prf.hyp1
      have l2 : ((s ≐ i) :: le s i :: Γ) ⊢[PRAAx] le i s := le_congr e (.eqRefl _) (le_refl s)
      exact .orI₂ (.orI₂ (.andI (sg_le l1) (.andI (sg_le l2) (eqb_of_eq e.eqSymm))))

theorem v100 : Γ ⊢[PRAAx] (one : PTm n) + zero + zero ≐ one := by ipra_ring
theorem v010 : Γ ⊢[PRAAx] (zero : PTm n) + one + zero ≐ one := by ipra_ring
theorem v001 : Γ ⊢[PRAAx] (zero : PTm n) + zero + one ≐ one := by ipra_ring
theorem m100 (f : PTm n) : Γ ⊢[PRAAx] f * one * one ≐ f := by ipra_ring
theorem m010 (f : PTm n) : Γ ⊢[PRAAx] one * f * one ≐ f := by ipra_ring
theorem m001 (f : PTm n) : Γ ⊢[PRAAx] one * one * f ≐ f := by ipra_ring

/-- `[i < s] + [s < i] + [i = s] = 1`. -/
theorem tri_sum (i s : PTm n) : Γ ⊢[PRAAx] sg (monus s i) + sg (monus i s) + eqb i s ≐ one := by
  refine .orE (tri i s) ?_ (.orE Prf.hyp0 ?_ ?_)
  · exact (congrAdd (congrAdd (Prf.andE₁ Prf.hyp0) (Prf.andE₁ (Prf.andE₂ Prf.hyp0)))
      (Prf.andE₂ (Prf.andE₂ Prf.hyp0))).eqTrans v100
  · exact (congrAdd (congrAdd (Prf.andE₁ Prf.hyp0) (Prf.andE₁ (Prf.andE₂ Prf.hyp0)))
      (Prf.andE₂ (Prf.andE₂ Prf.hyp0))).eqTrans v010
  · exact (congrAdd (congrAdd (Prf.andE₁ Prf.hyp0) (Prf.andE₁ (Prf.andE₂ Prf.hyp0)))
      (Prf.andE₂ (Prf.andE₂ Prf.hyp0))).eqTrans v001

/-- `f^{[i < s]} f^{[s < i]} f^{[i = s]} = f`. -/
theorem tri_pw (f i s : PTm n) :
    Γ ⊢[PRAAx] pw f (sg (monus s i)) * pw f (sg (monus i s)) * pw f (eqb i s) ≐ f := by
  refine .orE (tri i s) ?_ (.orE Prf.hyp0 ?_ ?_)
  · exact (congrMul (congrMul ((congrPw (.eqRefl _) (Prf.andE₁ Prf.hyp0)).eqTrans (pw_one _))
      ((congrPw (.eqRefl _) (Prf.andE₁ (Prf.andE₂ Prf.hyp0))).eqTrans (pw_zero _)))
      ((congrPw (.eqRefl _) (Prf.andE₂ (Prf.andE₂ Prf.hyp0))).eqTrans (pw_zero _))).eqTrans (m100 f)
  · exact (congrMul (congrMul ((congrPw (.eqRefl _) (Prf.andE₁ Prf.hyp0)).eqTrans (pw_zero _))
      ((congrPw (.eqRefl _) (Prf.andE₁ (Prf.andE₂ Prf.hyp0))).eqTrans (pw_one _)))
      ((congrPw (.eqRefl _) (Prf.andE₂ (Prf.andE₂ Prf.hyp0))).eqTrans (pw_zero _))).eqTrans (m010 f)
  · exact (congrMul (congrMul ((congrPw (.eqRefl _) (Prf.andE₁ Prf.hyp0)).eqTrans (pw_zero _))
      ((congrPw (.eqRefl _) (Prf.andE₁ (Prf.andE₂ Prf.hyp0))).eqTrans (pw_zero _)))
      ((congrPw (.eqRefl _) (Prf.andE₂ (Prf.andE₂ Prf.hyp0))).eqTrans (pw_one _))).eqTrans (m001 f)

/-! ## The indicators as bodies -/

section Bodies

variable (S F : PTm 2)

/-- `[i < σ(i)]`. -/
abbrev LB : PTm 2 := sg (monus S (var 0))
/-- `[σ(i) < i]`. -/
abbrev GB : PTm 2 := sg (monus (var 0) S)
/-- `[i = σ(i)]`. -/
abbrev EB : PTm 2 := eqb (var 0) S

theorem inst2_LB (i x : PTm n) : inst2 (LB S) i x = sg (monus (inst2 S i x) i) := by simp [inst2]
theorem inst2_GB (i x : PTm n) : inst2 (GB S) i x = sg (monus i (inst2 S i x)) := by simp [inst2]
theorem inst2_EB (i x : PTm n) : inst2 (EB S) i x = eqb i (inst2 S i x) := by simp [inst2]

theorem inst2_pw (A B : PTm 2) (i x : PTm n) : inst2 (pw A B) i x = pw (inst2 A i x) (inst2 B i x) := by
  simp [inst2]

/-- `L + G + E = 1`, as summands. -/
theorem pt_sum (i x : PTm n) :
    Γ ⊢[PRAAx] inst2 (addBody (addBody (LB S) (GB S)) (EB S)) i x ≐ inst2 (one : PTm 2) i x := by
  rw [inst2_addBody, inst2_addBody, inst2_LB S, inst2_GB S, inst2_EB S, one_inst]
  exact tri_sum _ _

/-- `G(σ(i)) = L(i)` when `σ(σ(i)) = i`. -/
theorem pt_swap (i x : PTm n) (ret : Γ ⊢[PRAAx] inst2 S (inst2 S i x) x ≐ i) :
    Γ ⊢[PRAAx] inst2 (Permutation.FS (GB S) S) i x ≐ inst2 (LB S) i x := by
  rw [Permutation.inst2_FS, inst2_GB S, inst2_LB S]
  exact congrSg (congrMonus (.eqRefl _) ret)

/-- `F = F^L F^G F^E`, as factors. -/
theorem pt_split (i x : PTm n) :
    Γ ⊢[PRAAx] inst2 F i x ≐ inst2 ((pw F (LB S) * pw F (GB S)) * pw F (EB S)) i x := by
  rw [inst2_mulB, inst2_mulB, inst2_pw, inst2_pw, inst2_pw, inst2_LB S, inst2_GB S, inst2_EB S]
  exact (tri_pw _ _ _).eqSymm

/-- `(F^G)(σ(i)) = F(σ(i))^{L(i)}` when `σ(σ(i)) = i`. -/
theorem pt_perm (i x : PTm n) (ret : Γ ⊢[PRAAx] inst2 S (inst2 S i x) x ≐ i) :
    Γ ⊢[PRAAx] inst2 (Permutation.FS (pw F (GB S)) S) i x ≐ inst2 (pw (Permutation.FS F S) (LB S)) i x := by
  rw [Permutation.inst2_FS, inst2_pw, inst2_pw, Permutation.inst2_FS, inst2_GB S, inst2_LB S]
  exact congrPw (.eqRefl _) (congrSg (congrMonus (.eqRefl _) ret))

/-- `F^L (F ∘ σ)^L = (F · F ∘ σ)^L`, as factors. -/
theorem pt_join (i x : PTm n) :
    Γ ⊢[PRAAx] inst2 (pw F (LB S) * pw (Permutation.FS F S) (LB S)) i x ≐
      inst2 (pw (F * Permutation.FS F S) (LB S)) i x := by
  rw [inst2_mulB, inst2_pw, inst2_pw, inst2_pw, inst2_mulB]
  exact (pw_mul_base _ _ _).eqSymm

end Bodies

/-! ## Counting and multiplying along the involution -/

section Pairing

variable {S : PTm 2} {M x : PTm n} (hr : Γ ⊢[PRAAx] Permutation.rangeAll S M x)
  (hinv : Γ ⊢[PRAAx] Permutation.invAll S S M x) (hret : Γ ⊢[PRAAx] Permutation.retAll S S M x)
include hr hinv hret

/-- `Σ_{i<M} G(i) = Σ_{i<M} L(i)`. -/
theorem sum_swap : Γ ⊢[PRAAx] ap2 (sumF (GB S)) M x ≐ ap2 (sumF (LB S)) M x := by
  refine (sum_perm (f := GB S) hr hinv hret).eqSymm.eqTrans (sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_)))
  exact pt_swap S _ _ (Prf.impE hret.allOpen.wk Prf.hyp0)

/-- `2 Σ_{i<M} [i < σ(i)] + Σ_{i<M} [i = σ(i)] = M`. -/
theorem pair_count :
    Γ ⊢[PRAAx] ap2 (sumF (LB S)) M x + ap2 (sumF (LB S)) M x + ap2 (sumF (EB S)) M x ≐ M := by
  have c1 : Γ ⊢[PRAAx] ap2 (sumF (addBody (addBody (LB S) (GB S)) (EB S))) M x ≐ M := by
    refine (sum_congr_bounded _ (one : PTm 2) x x M (.allI (.impI ?_))).eqTrans (sum_ones M x)
    exact pt_sum S _ _
  have c2 : Γ ⊢[PRAAx] ap2 (sumF (addBody (addBody (LB S) (GB S)) (EB S))) M x ≐
      ap2 (sumF (LB S)) M x + ap2 (sumF (GB S)) M x + ap2 (sumF (EB S)) M x :=
    (sum_add (addBody (LB S) (GB S)) (EB S) M x).eqTrans (congrAdd (sum_add (LB S) (GB S) M x) (.eqRefl _))
  have c3 := sum_swap hr hinv hret
  exact (congrAdd (congrAdd (.eqRefl _) c3.eqSymm) (.eqRefl _)).eqTrans (c2.eqSymm.eqTrans c1)

/-- `∏_{i<M} F(i) = ∏_{i<M} (F(i) F(σ(i)))^{[i < σ(i)]} · ∏_{i<M} F(i)^{[i = σ(i)]}`. -/
theorem pair_prod (F : PTm 2) :
    Γ ⊢[PRAAx] ap2 (prodF F) M x ≐
      ap2 (prodF (pw (F * Permutation.FS F S) (LB S))) M x * ap2 (prodF (pw F (EB S))) M x := by
  have d1 : Γ ⊢[PRAAx] ap2 (prodF F) M x ≐
      ap2 (prodF ((pw F (LB S) * pw F (GB S)) * pw F (EB S))) M x := by
    refine prod_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    exact pt_split S F _ _
  have d2 : Γ ⊢[PRAAx] ap2 (prodF ((pw F (LB S) * pw F (GB S)) * pw F (EB S))) M x ≐
      ap2 (prodF (pw F (LB S))) M x * ap2 (prodF (pw F (GB S))) M x * ap2 (prodF (pw F (EB S))) M x :=
    (prod_mul (pw F (LB S) * pw F (GB S)) (pw F (EB S)) M x).eqTrans
      (congrMul (prod_mul (pw F (LB S)) (pw F (GB S)) M x) (.eqRefl _))
  have d3 : Γ ⊢[PRAAx] ap2 (prodF (pw F (GB S))) M x ≐ ap2 (prodF (pw (Permutation.FS F S) (LB S))) M x := by
    refine (Permutation.prod_perm (F := pw F (GB S)) hr hinv hret).eqSymm.eqTrans
      (prod_congr_bounded _ _ _ _ _ (.allI (.impI ?_)))
    exact pt_perm S F _ _ (Prf.impE hret.allOpen.wk Prf.hyp0)
  have d4 : Γ ⊢[PRAAx] ap2 (prodF (pw F (LB S))) M x * ap2 (prodF (pw (Permutation.FS F S) (LB S))) M x ≐
      ap2 (prodF (pw (F * Permutation.FS F S) (LB S))) M x := by
    refine (prod_mul (pw F (LB S)) (pw (Permutation.FS F S) (LB S)) M x).eqSymm.eqTrans
      (prod_congr_bounded _ _ _ _ _ (.allI (.impI ?_)))
    exact pt_join S F _ _
  exact d1.eqTrans (d2.eqTrans (congrMul ((congrMul (.eqRefl _) d3).eqTrans d4) (.eqRefl _)))

end Pairing

end LeanProofs.IPRA.Foundations.InvolutionPairing
