import IPRADerivations.AnalyticNumberTheory.BlockSums
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.Header

/-!
# The mass of a block of divisors (`pnt_ipra_constructive_2026-11-14`, `con:deficit`)

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`, `contraction.tex`, Lemma `con:deficit`: the
deficit on a block is compared with its length, `∫_s^{s+H} a dt = aH`. Discretely the length is the mass
`Σ_{D₁<d≤D₂} F⌊x/d⌋ ≈ x F (H_{D₂} − H_{D₁}) = x (S(D₂) − S(D₁))` (`F = L!`):

* `t_f_prefix`: the prefix sum `T_F(D) = Σ_{1≤d≤x} [d ≤ D] F⌊x/d⌋` is `Σ_{n≤D} F⌊x/n⌋` for `D ≤ x`;
* `mass_lower`, `mass_upper`: `x(S(D₂) − S(D₁)) − F D₂ ≤ Σ_{D₁<d≤D₂} F⌊x/d⌋ ≤ x(S(D₂) − S(D₁)) + F D₁`
  for `D₁ ≤ D₂ ≤ x`, `D₂ ≤ L` (`BlockFloor.f_sum` at both ends, `BlockSums.block_f`).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.BlockMass

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (S)
open LeanProofs.IPRA.AnalyticNumberTheory.SummatoryCompose (hRB)
open LeanProofs.IPRA.AnalyticNumberTheory.ConvSummatory (RB RB_at)
open LeanProofs.IPRA.AnalyticNumberTheory.ChebyshevBlock (iB gB gB_at)
open LeanProofs.IPRA.AnalyticNumberTheory.BlockFloor (fB fB_at f_sum)
open LeanProofs.IPRA.AnalyticNumberTheory.BlockMean (T)
open LeanProofs.IPRA.AnalyticNumberTheory.BlockSums (Y biB fzB ia_at ind0 ind1 bs_f block_f)
open LeanProofs.IPRA.Foundations.ProductSumDomination (sum_trunc)
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.Signum (sg)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

theorem hyp_shift_succ {N : PTm n} :
    (lt (var 0) (Syn.shift (succ N)) :: Γ.map Fm.shift) ⊢[PRAAx] lt (var 0) (succ (Syn.shift N)) := by
  have h0 : (lt (var 0) (Syn.shift (succ N)) :: Γ.map Fm.shift) ⊢[PRAAx] lt (var 0) (Syn.shift (succ N)) := Prf.hyp0
  have e : Syn.shift (succ N) = succ (Syn.shift N) := by simp [Syn.shift]
  rw [e] at h0 ⊢; exact h0

/-- `T_F(D) = Σ_{n≤D} F⌊x/n⌋` for `D ≤ x`. -/
theorem t_f_prefix {x D K F : PTm n} (hD : Γ ⊢[PRAAx] le D x) :
    Γ ⊢[PRAAx] T fB x D (pairT K F) ≐ ap2 (sumF (gB fB)) (succ D) (pairT x (pairT D (pairT K F))) := by
  have hS : Γ ⊢[PRAAx] le (succ D) (succ x) := (succ_monus_succ _ _).eqTrans hD
  refine (sum_trunc (RB iB fB) hS (.allI (.impI (.impI ?_)))).eqTrans ?_
  · simp only [shift_pairT]
    have hv : (le (Syn.shift (succ D)) (var 0) :: lt (var 0) (Syn.shift (succ x)) :: Γ.map Fm.shift) ⊢[PRAAx]
        lt (Syn.shift D) (var 0) := by
      have h0 : (le (Syn.shift (succ D)) (var 0) :: lt (var 0) (Syn.shift (succ x)) :: Γ.map Fm.shift) ⊢[PRAAx]
          le (Syn.shift (succ D)) (var 0) := Prf.hyp0
      have e : Syn.shift (succ D) = succ (Syn.shift D) := by simp [Syn.shift]
      rw [e] at h0 ⊢; exact h0
    refine (RB_at _ _ _ _ _).eqTrans ?_
    have z := (ia_at (Γ := (le (Syn.shift (succ D)) (var 0) :: lt (var 0) (Syn.shift (succ x)) :: Γ.map Fm.shift))
      (var 0) (Syn.shift D) (pairT (Syn.shift K) (Syn.shift F))).eqTrans (ind0 hv)
    ipra_lc (𝔞 (sg (var 0)) * 𝔞 (ap2 (sumF (LeanProofs.IPRA.AnalyticNumberTheory.ConvSummatory.bS fB)) (quo (Syn.shift x) (var 0)) (pairT (Syn.shift D) (pairT (Syn.shift K) (Syn.shift F))))) * natEq z
  · refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    simp only [shift_pairT]
    have hv : (lt (var 0) (Syn.shift (succ D)) :: Γ.map Fm.shift) ⊢[PRAAx] le (var 0) (Syn.shift D) :=
      (succ_monus_succ _ _).eqSymm.eqTrans hyp_shift_succ
    refine (RB_at _ _ _ _ _).eqTrans (.eqTrans ?_ (gB_at _ _ _ _).eqSymm)
    ipra_lc (𝔞 (sg (var 0)) * 𝔞 (ap2 (sumF (LeanProofs.IPRA.AnalyticNumberTheory.ConvSummatory.bS fB)) (quo (Syn.shift x) (var 0)) (pairT (Syn.shift D) (pairT (Syn.shift K) (Syn.shift F))))) * natEq ((ia_at (Γ := (lt (var 0) (Syn.shift (succ D)) :: Γ.map Fm.shift)) (var 0) (Syn.shift D) (pairT (Syn.shift K) (Syn.shift F))).eqTrans (ind1 hv)) +
      𝔞 (sg (var 0)) * natEq (bs_f (Γ := (lt (var 0) (Syn.shift (succ D)) :: Γ.map Fm.shift)) (quo (Syn.shift x) (var 0)) (Syn.shift D) (Syn.shift K) (Syn.shift F)) -
      𝔞 (sg (var 0)) * 𝔞 (quo (Syn.shift x) (var 0)) * natEq (fB_at (Γ := (lt (var 0) (Syn.shift (succ D)) :: Γ.map Fm.shift)) (var 0) (Syn.shift D) (Syn.shift K) (Syn.shift F))

/-- `x S(D) − F D ≤ Σ_{n≤D} F⌊x/n⌋ ≤ x S(D)`, from `BlockFloor.f_sum` (any level in the parameter). -/
theorem prefix_bounds {x D D' K L : PTm n} (hDL : Γ ⊢[PRAAx] le D L) :
    Γ ⊢[PRAAx] le (ap2 (sumF (gB fB)) (succ D) (pairT x (pairT D' (pairT K (fact L))))) (x * S D (fact L)) ⋏
      le (x * S D (fact L)) (ap2 (sumF (gB fB)) (succ D) (pairT x (pairT D' (pairT K (fact L)))) + fact L * D) :=
  f_sum hDL

section Mass

variable {x D₁ D₂ K L w : PTm n} (h12 : Γ ⊢[PRAAx] le D₁ D₂) (h2x : Γ ⊢[PRAAx] le D₂ x)
  (h2L : Γ ⊢[PRAAx] le D₂ L)

include h12 h2x h2L

/-- `x(S(D₂) − S(D₁)) ≤ Σ_{D₁<d≤D₂} F⌊x/d⌋ + F D₂`. -/
theorem mass_lower :
    Γ ⊢[PRAAx] le (x * S D₂ (fact L) + zero)
      (ap2 (sumF (hRB fzB biB)) (succ x) (pairT x (BlockSums.Y D₁ D₂ w (pairT K (fact L)))) + x * S D₁ (fact L) +
        fact L * D₂) := by
  have bf := natEq (block_f (Γ := Γ) (x := x) (w := w) (K := K) (F := fact L) h12)
  have t1 := natEq (t_f_prefix (Γ := Γ) (K := K) (F := fact L) (le_trans h12 h2x))
  have t2 := natEq (t_f_prefix (Γ := Γ) (K := K) (F := fact L) h2x)
  have p1 := Prf.andE₁ (prefix_bounds (Γ := Γ) (x := x) (D' := D₁) (K := K) (le_trans h12 h2L))
  have p2 := Prf.andE₂ (prefix_bounds (Γ := Γ) (x := x) (D' := D₂) (K := K) h2L)
  ipra_le sl p1 + sl p2 with bf - t2 + t1

/-- `Σ_{D₁<d≤D₂} F⌊x/d⌋ + x S(D₁) ≤ x S(D₂) + F D₁`. -/
theorem mass_upper :
    Γ ⊢[PRAAx] le (ap2 (sumF (hRB fzB biB)) (succ x) (pairT x (BlockSums.Y D₁ D₂ w (pairT K (fact L)))) + x * S D₁ (fact L))
      (x * S D₂ (fact L) + fact L * D₁) := by
  have bf := natEq (block_f (Γ := Γ) (x := x) (w := w) (K := K) (F := fact L) h12)
  have t1 := natEq (t_f_prefix (Γ := Γ) (K := K) (F := fact L) (le_trans h12 h2x))
  have t2 := natEq (t_f_prefix (Γ := Γ) (K := K) (F := fact L) h2x)
  have p1 := Prf.andE₂ (prefix_bounds (Γ := Γ) (x := x) (D' := D₁) (K := K) (le_trans h12 h2L))
  have p2 := Prf.andE₁ (prefix_bounds (Γ := Γ) (x := x) (D' := D₂) (K := K) h2L)
  ipra_le sl p1 + sl p2 with bf - t2 + t1

end Mass

end LeanProofs.IPRA.AnalyticNumberTheory.BlockMass
