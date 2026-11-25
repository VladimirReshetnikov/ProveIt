import IPRADerivations.AnalyticNumberTheory.MangoldtMobius
import IPRADerivations.Core.CertificateTactics

/-!
# The weighted Vaughan identity

Packet: `analytic-number-theory/prime_distribution_ipra`, `paper/sections/07_sw_bv.tex`, Proposition "Weighted
Vaughan identity": for cutoffs `U, V` and an arbitrary weight `w` on primes,

  `Λ_w = (Λ_w)_{≤V} + μ_{≤U} * L_w − μ_{≤U} * 𝟏 * (Λ_w)_{≤V} + μ_{>U} * 𝟏 * (Λ_w)_{>V}`,

proved there from `μ * 𝟏 = ε` and `𝟏 * Λ_w = L_w`.

Here the two divisor identities are the derived `MangoldtMobius.lambda_mobius` (`Λ_w = μ * L_w`),
`MangoldtMobius.row_lam_mob` (`𝟏 * Λ_w = L_w` in each row) and `MobiusInversion.mobius_inversion` applied to the
truncated function `(Λ_w)_{≤V}`. With `μ = μ⁺ − μ⁻` the identity at `N ≥ 1` is the natural-number equation

  `Λ_w(N) + (μ⁻_{≤U} * L_w)(N) + (μ⁺_{≤U} * 𝟏 * Λ_{≤V})(N) + (μ⁻_{>U} * 𝟏 * Λ_{>V})(N)
     = Λ_{≤V}(N) + (μ⁺_{≤U} * L_w)(N) + (μ⁻_{≤U} * 𝟏 * Λ_{≤V})(N) + (μ⁺_{>U} * 𝟏 * Λ_{>V})(N)`   (`vaughan`).

* `loB`, `hiB`, `sum_split`: a sum over `d` split by the indicators `[d ≤ U]`, `[U < d]` (`U` an arbitrary term);
* `fle`, `fgt`: the truncations `[e ≤ V] Λ_w(e)`, `[V < e] Λ_w(e)`, where the cutoff `V = V(N)` is any body of `N`
  (a numeral, or a primitive recursive function of `N` such as a root);
* `inner_split_P`, `inner_split_N`: `𝟏 * Λ_w = 𝟏 * Λ_{≤V} + 𝟏 * Λ_{>V}` in each row;
* `tail_sum_P`, `tail_sum_N`: `μ^±_{>U} * L_w = μ^±_{>U} * 𝟏 * Λ_{≤V} + μ^±_{>U} * 𝟏 * Λ_{>V}`.

The convolutions are bracketed as `μ * (𝟏 * Λ)`; associativity is `ConvolutionAssoc.conv_assoc`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.VaughanIdentity

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (muP muN)
open LeanProofs.IPRA.AnalyticNumberTheory.MobiusBounds (shift_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.MobiusInversion (aP aN inst3_aP inst3_aN mobius_inversion)
open LeanProofs.IPRA.AnalyticNumberTheory.MangoldtMobius (lamF QLP QLN inst2_lamF row_lam_mob lambda_mobius)
open LeanProofs.IPRA.AnalyticNumberTheory.WeightedMangoldt (Lam Lw)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Splitting by an indicator -/

theorem monus_le_self' (a b : PTm n) : Γ ⊢[PRAAx] le (monus a b) a := by
  refine .orE (le_total b a) ?_ ?_
  · exact le_of_eq_add (d := b) ((eq_add_of_le Prf.hyp0).eqTrans (add_comm _ _))
  · exact le_congr (Prf.hyp0 : (le a b :: Γ) ⊢[PRAAx] monus a b ≐ zero).eqSymm (.eqRefl _) (zero_le a)

/-- `[t = 0] + [t > 0] = 1` for the indicators `1 ∸ t` and `1 ∸ (1 ∸ t)`. -/
theorem ind_split (t : PTm n) : Γ ⊢[PRAAx] monus one t + monus one (monus one t) ≐ one :=
  (eq_add_of_le (monus_le_self' one t)).eqSymm

/-- `X = [t = 0] X + [t > 0] X`. -/
theorem split_term (t X : PTm n) : Γ ⊢[PRAAx] X ≐ monus one t * X + monus one (monus one t) * X :=
  (one_mul X).eqSymm.eqTrans ((congrMul (ind_split t).eqSymm (.eqRefl X)).eqTrans
    (by ipra_ring))

section Outer

variable (B : PTm 2)

/-- `[d ≤ U] B(d, y)` over `0 = d`, `1 = ⟨U, y⟩`. -/
def loB : PTm 2 := monus one (monus (var 0) (fstT (var 1))) * Syn.subst ![var 0, sndT (var 1)] B
/-- `[U < d] B(d, y)` over `0 = d`, `1 = ⟨U, y⟩`. -/
def hiB : PTm 2 := monus one (monus one (monus (var 0) (fstT (var 1)))) * Syn.subst ![var 0, sndT (var 1)] B

theorem inst2_loB (d z : PTm n) : inst2 (loB B) d z = monus one (monus d (fstT z)) * inst2 B d (sndT z) := by
  have hf : Syn.subst ![d, z] (Syn.subst ![var 0, sndT (var 1)] B) = inst2 B d (sndT z) := by
    simp only [inst2, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp
  simp only [inst2, loB, PTm.subst_mul, hf]
  simp

theorem inst2_hiB (d z : PTm n) :
    inst2 (hiB B) d z = monus one (monus one (monus d (fstT z))) * inst2 B d (sndT z) := by
  have hf : Syn.subst ![d, z] (Syn.subst ![var 0, sndT (var 1)] B) = inst2 B d (sndT z) := by
    simp only [inst2, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp
  simp only [inst2, hiB, PTm.subst_mul, hf]
  simp

theorem lo_at (d U y : PTm n) :
    Γ ⊢[PRAAx] inst2 (loB B) d (pairT U y) ≐ monus one (monus d U) * inst2 B d y := by
  rw [inst2_loB]
  exact congrMul (congrMonus (.eqRefl _) (congrMonus (.eqRefl _) (fst_pair _ _))) (congrInst2 B (.eqRefl _) (snd_pair _ _))

theorem hi_at (d U y : PTm n) :
    Γ ⊢[PRAAx] inst2 (hiB B) d (pairT U y) ≐ monus one (monus one (monus d U)) * inst2 B d y := by
  rw [inst2_hiB]
  exact congrMul (congrMonus (.eqRefl _) (congrMonus (.eqRefl _) (congrMonus (.eqRefl _) (fst_pair _ _))))
    (congrInst2 B (.eqRefl _) (snd_pair _ _))

theorem split_pt (d U y : PTm n) :
    Γ ⊢[PRAAx] inst2 B d y ≐ inst2 (loB B) d (pairT U y) + inst2 (hiB B) d (pairT U y) :=
  (split_term (monus d U) (inst2 B d y)).eqTrans (congrAdd (lo_at B d U y) (hi_at B d U y)).eqSymm

/-- `Σ_{d<M} B(d) = Σ_{d<M} [d ≤ U] B(d) + Σ_{d<M} [U < d] B(d)`. -/
theorem sum_split (U y M : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF B) M y ≐ ap2 (sumF (loB B)) M (pairT U y) + ap2 (sumF (hiB B)) M (pairT U y) := by
  refine (sum_congr_bounded B (addBody (loB B) (hiB B)) y (pairT U y) M (.allI (.impI ?_))).eqTrans
    (sum_add _ _ _ _)
  rw [inst2_addBody, shift_pairT]
  exact split_pt B _ _ _

end Outer

/-! ## The truncated weighted von Mangoldt function -/

section Vaughan

variable (w : PTm 2) (Vb : PTm 1)

/-- `[e ≤ V(N)] Λ_w(e)` over `0 = e`, `1 = N`. -/
def fle : PTm 2 := monus one (monus (var 0) (Syn.subst ![var 1] Vb)) * lamF w
/-- `[V(N) < e] Λ_w(e)` over `0 = e`, `1 = N`. -/
def fgt : PTm 2 := monus one (monus one (monus (var 0) (Syn.subst ![var 1] Vb))) * lamF w

theorem inst2_fle (e N : PTm n) :
    inst2 (fle w Vb) e N = monus one (monus e (Syn.subst ![N] Vb)) * Lam w e zero := by
  have hv : Syn.subst ![e, N] (Syn.subst ![var 1] Vb) = Syn.subst ![N] Vb := by
    simp only [Syn.subst_subst]; congr 1; funext k; fin_cases k; rfl
  have hl : Syn.subst ![e, N] (lamF w) = Lam w e zero := inst2_lamF w e N
  simp only [inst2, fle, PTm.subst_mul, PTm.subst_monus, hv, hl]
  simp

theorem inst2_fgt (e N : PTm n) :
    inst2 (fgt w Vb) e N = monus one (monus one (monus e (Syn.subst ![N] Vb))) * Lam w e zero := by
  have hv : Syn.subst ![e, N] (Syn.subst ![var 1] Vb) = Syn.subst ![N] Vb := by
    simp only [Syn.subst_subst]; congr 1; funext k; fin_cases k; rfl
  have hl : Syn.subst ![e, N] (lamF w) = Lam w e zero := inst2_lamF w e N
  simp only [inst2, fgt, PTm.subst_mul, PTm.subst_monus, hv, hl]
  simp

/-! ## `𝟏 * Λ_w = 𝟏 * Λ_{≤V} + 𝟏 * Λ_{>V}` in each row -/

theorem row_split_P (e z : PTm n) :
    Γ ⊢[PRAAx] inst2 (rowB (aP (lamF w))) e z ≐
      inst2 (rowB (aP (fle w Vb))) e z + inst2 (rowB (aP (fgt w Vb))) e z := by
  rw [inst2_rowB, inst2_rowB, inst2_rowB, inst3_aP, inst3_aP, inst3_aP, inst2_lamF, inst2_fle, inst2_fgt]
  refine (congrMul (.eqRefl _) (congrMul (.eqRefl _)
    (split_term (monus e (Syn.subst ![sndT z] Vb)) (Lam w e zero)))).eqTrans ?_
  ipra_ring

theorem row_split_N (e z : PTm n) :
    Γ ⊢[PRAAx] inst2 (rowB (aN (lamF w))) e z ≐
      inst2 (rowB (aN (fle w Vb))) e z + inst2 (rowB (aN (fgt w Vb))) e z := by
  rw [inst2_rowB, inst2_rowB, inst2_rowB, inst3_aN, inst3_aN, inst3_aN, inst2_lamF, inst2_fle, inst2_fgt]
  refine (congrMul (.eqRefl _) (congrMul (.eqRefl _)
    (split_term (monus e (Syn.subst ![sndT z] Vb)) (Lam w e zero)))).eqTrans ?_
  ipra_ring

theorem inner_split_P (d y : PTm n) :
    Γ ⊢[PRAAx] inst2 (oB (aP (lamF w))) d y ≐
      inst2 (oB (aP (fle w Vb))) d y + inst2 (oB (aP (fgt w Vb))) d y := by
  rw [inst2_oB, inst2_oB, inst2_oB]
  refine (sum_congr_bounded _ (addBody (rowB (aP (fle w Vb))) (rowB (aP (fgt w Vb)))) _ _ _
    (.allI (.impI ?_))).eqTrans (sum_add _ _ _ _)
  rw [inst2_addBody]
  exact row_split_P w Vb _ _

theorem inner_split_N (d y : PTm n) :
    Γ ⊢[PRAAx] inst2 (oB (aN (lamF w))) d y ≐
      inst2 (oB (aN (fle w Vb))) d y + inst2 (oB (aN (fgt w Vb))) d y := by
  rw [inst2_oB, inst2_oB, inst2_oB]
  refine (sum_congr_bounded _ (addBody (rowB (aN (fle w Vb))) (rowB (aN (fgt w Vb)))) _ _ _
    (.allI (.impI ?_))).eqTrans (sum_add _ _ _ _)
  rw [inst2_addBody]
  exact row_split_N w Vb _ _

/-! ## The tail `d > U` -/

/-- The parameter `⟨N + 1, N⟩` of the double divisor sums. -/
abbrev Yv (N : PTm n) : PTm n := pairT (succ N) N

theorem tail_pt_P {d U N : PTm n} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) :
    Γ ⊢[PRAAx] inst2 (hiB (QLP w)) d (pairT U N) ≐
      inst2 (hiB (oB (aP (fle w Vb)))) d (pairT U (Yv N)) + inst2 (hiB (oB (aP (fgt w Vb)))) d (pairT U (Yv N)) := by
  refine (hi_at _ _ _ _).eqTrans ?_
  refine (congrMul (.eqRefl _) ((Prf.andE₁ (row_lam_mob w (d := d) hN)).eqSymm.eqTrans
    (inner_split_P w Vb d _))).eqTrans ?_
  refine Prf.eqTrans ?_ (congrAdd (hi_at _ _ _ _) (hi_at _ _ _ _)).eqSymm
  ipra_ring

theorem tail_pt_N {d U N : PTm n} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) :
    Γ ⊢[PRAAx] inst2 (hiB (QLN w)) d (pairT U N) ≐
      inst2 (hiB (oB (aN (fle w Vb)))) d (pairT U (Yv N)) + inst2 (hiB (oB (aN (fgt w Vb)))) d (pairT U (Yv N)) := by
  refine (hi_at _ _ _ _).eqTrans ?_
  refine (congrMul (.eqRefl _) ((Prf.andE₂ (row_lam_mob w (d := d) hN)).eqSymm.eqTrans
    (inner_split_N w Vb d _))).eqTrans ?_
  refine Prf.eqTrans ?_ (congrAdd (hi_at _ _ _ _) (hi_at _ _ _ _)).eqSymm
  ipra_ring

/-- `μ⁺_{>U} * L_w = μ⁺_{>U} * 𝟏 * Λ_{≤V} + μ⁺_{>U} * 𝟏 * Λ_{>V}` at `N ≥ 1`. -/
theorem tail_sum_P {N : PTm n} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) (U : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (hiB (QLP w))) (succ N) (pairT U N) ≐
      ap2 (sumF (hiB (oB (aP (fle w Vb))))) (succ N) (pairT U (Yv N)) +
        ap2 (sumF (hiB (oB (aP (fgt w Vb))))) (succ N) (pairT U (Yv N)) := by
  have hs : Syn.shift (succ N) = succ (Syn.shift N) := by simp [Syn.shift]
  refine (sum_congr_bounded _ (addBody (hiB (oB (aP (fle w Vb)))) (hiB (oB (aP (fgt w Vb))))) (pairT U N)
    (pairT U (Yv N)) (succ N) (.allI (.impI ?_))).eqTrans (sum_add _ _ _ _)
  rw [inst2_addBody]
  simp only [shift_pairT]
  rw [hs]
  exact tail_pt_P w Vb (shift_pos hN).wk

/-- `μ⁻_{>U} * L_w = μ⁻_{>U} * 𝟏 * Λ_{≤V} + μ⁻_{>U} * 𝟏 * Λ_{>V}` at `N ≥ 1`. -/
theorem tail_sum_N {N : PTm n} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) (U : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (hiB (QLN w))) (succ N) (pairT U N) ≐
      ap2 (sumF (hiB (oB (aN (fle w Vb))))) (succ N) (pairT U (Yv N)) +
        ap2 (sumF (hiB (oB (aN (fgt w Vb))))) (succ N) (pairT U (Yv N)) := by
  have hs : Syn.shift (succ N) = succ (Syn.shift N) := by simp [Syn.shift]
  refine (sum_congr_bounded _ (addBody (hiB (oB (aN (fle w Vb)))) (hiB (oB (aN (fgt w Vb))))) (pairT U N)
    (pairT U (Yv N)) (succ N) (.allI (.impI ?_))).eqTrans (sum_add _ _ _ _)
  rw [inst2_addBody]
  simp only [shift_pairT]
  rw [hs]
  exact tail_pt_N w Vb (shift_pos hN).wk

/-! ## The identity -/

/-- The weighted Vaughan identity at `N ≥ 1`, with `μ = μ⁺ − μ⁻` moved to the two sides:
`Λ_w(N) + μ⁻_{≤U} * L_w + μ⁺_{≤U} * 𝟏 * Λ_{≤V} + μ⁻_{>U} * 𝟏 * Λ_{>V}
  = Λ_{≤V}(N) + μ⁺_{≤U} * L_w + μ⁻_{≤U} * 𝟏 * Λ_{≤V} + μ⁺_{>U} * 𝟏 * Λ_{>V}`. -/
theorem vaughan {N : PTm n} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) (U : PTm n) :
    Γ ⊢[PRAAx] Lam w N zero + ap2 (sumF (loB (QLN w))) (succ N) (pairT U N) +
        ap2 (sumF (loB (oB (aP (fle w Vb))))) (succ N) (pairT U (Yv N)) +
        ap2 (sumF (hiB (oB (aN (fgt w Vb))))) (succ N) (pairT U (Yv N)) ≐
      inst2 (fle w Vb) N N + ap2 (sumF (loB (QLP w))) (succ N) (pairT U N) +
        ap2 (sumF (loB (oB (aN (fle w Vb))))) (succ N) (pairT U (Yv N)) +
        ap2 (sumF (hiB (oB (aP (fgt w Vb))))) (succ N) (pairT U (Yv N)) := by
  ipra_lc -natEq (lambda_mobius (Γ := Γ) w hN) + natEq (sum_split (Γ := Γ) (QLP w) U N (succ N)) -
    natEq (sum_split (Γ := Γ) (QLN w) U N (succ N)) + natEq (tail_sum_P (Γ := Γ) w Vb hN U) -
    natEq (tail_sum_N (Γ := Γ) w Vb hN U) + natEq (mobius_inversion (Γ := Γ) (fle w Vb) hN) -
    natEq (sum_split (Γ := Γ) (oB (aP (fle w Vb))) U (Yv N) (succ N)) +
    natEq (sum_split (Γ := Γ) (oB (aN (fle w Vb))) U (Yv N) (succ N))

end Vaughan

end LeanProofs.IPRA.AnalyticNumberTheory.VaughanIdentity
