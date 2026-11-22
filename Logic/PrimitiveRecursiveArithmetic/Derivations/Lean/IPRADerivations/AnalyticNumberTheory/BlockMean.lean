import IPRADerivations.AnalyticNumberTheory.BlockSigned

/-!
# The signed block mean over divisors (`pnt_ipra_constructive_2026-11-14`, `con:signed`)

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`, `contraction.tex`, hypothesis `con:signed`
(`|∫_u^v r(w) dw| ≤ 20`), in the form used by Lemma `con:deficit`: for a block of divisors `D₁ < d ≤ D₂` (the
logarithmic block `x/D₂ ≤ e^w ≤ x/D₁`),

  `|Σ_{D₁<d≤D₂} (ψ(⌊x/d⌋) − F⌊x/d⌋)| ≤ 24 F x`,

written with the prefix sums `T_b(D) = Σ_{1≤d≤x} [d ≤ D] B(⌊x/d⌋)` of `ChebyshevBlock` (`B = ψ` for `b = Λ`,
`B(m) = F m` for `b = F`): `block_upper`, `block_lower`. The proof: `T_b(D) + E_b(D) = G_b` (`block_id`, with `G_b`
independent of `D`: `g_indep`), and `BlockSigned.excess_upper` at `D₁`, `excess_lower` at `D₂`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.BlockMean

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.ConvSummatory (RB)
open LeanProofs.IPRA.AnalyticNumberTheory.ChebyshevBlock (iB eB gB gB_at block_id)
open LeanProofs.IPRA.AnalyticNumberTheory.BlockFloor (lB fB lB_at fB_at)
open LeanProofs.IPRA.AnalyticNumberTheory.BlockSigned (excess_upper excess_lower)
open LeanProofs.IPRA.Analysis.Products (fact)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `T_b(D) = Σ_{1≤d≤x} [d ≤ D] B(⌊x/d⌋)`. -/
abbrev T (b : PTm 2) (x D z : PTm n) : PTm n := ap2 (sumF (RB iB b)) (succ x) (pairT x (pairT D z))

/-- `G_Λ` does not depend on the level `D`. -/
theorem g_lam_indep (x D D' z : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (gB lB)) (succ x) (pairT x (pairT D z)) ≐ ap2 (sumF (gB lB)) (succ x) (pairT x (pairT D' z)) := by
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  simp only [shift_pairT]
  exact (gB_at _ _ _ _).eqTrans ((congrMul (congrMul (.eqRefl _) ((lB_at _ _ _).eqTrans (lB_at _ _ _).eqSymm))
    (.eqRefl _)).eqTrans (gB_at _ _ _ _).eqSymm)

/-- `G_F` does not depend on the level `D`. -/
theorem g_f_indep (x D D' K F : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (gB fB)) (succ x) (pairT x (pairT D (pairT K F))) ≐
      ap2 (sumF (gB fB)) (succ x) (pairT x (pairT D' (pairT K F))) := by
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  simp only [shift_pairT]
  exact (gB_at _ _ _ _).eqTrans ((congrMul (congrMul (.eqRefl _) ((fB_at _ _ _ _).eqTrans (fB_at _ _ _ _).eqSymm))
    (.eqRefl _)).eqTrans (gB_at _ _ _ _).eqSymm)

section Block

variable {x D₁ D₂ K L : PTm n}
  (h1 : Γ ⊢[PRAAx] le one D₁) (h12 : Γ ⊢[PRAAx] le D₁ D₂) (h2x : Γ ⊢[PRAAx] le D₂ x) (hK1 : Γ ⊢[PRAAx] le one K)
  (hPK : Γ ⊢[PRAAx] le (quo x D₁) K) (hPK' : Γ ⊢[PRAAx] le (quo x D₂) K)
  (hNN : Γ ⊢[PRAAx] le (K * pw (quo x D₁) (quo x D₁)) L) (hNN' : Γ ⊢[PRAAx] le (K * pw (quo x D₂) (quo x D₂)) L)
  (hKx : Γ ⊢[PRAAx] le (K * x) L) (hP : Γ ⊢[PRAAx] le (K * pw two (two * (two * x))) L)

include h1 h12 h2x hK1 hPK hPK' hNN hNN' hKx hP

/-- `Σ_{D₁<d≤D₂} ψ(⌊x/d⌋) ≤ Σ_{D₁<d≤D₂} F⌊x/d⌋ + 24 F x`. -/
theorem block_upper :
    Γ ⊢[PRAAx] le (T lB x D₂ (pairT K (fact L)) + T fB x D₁ (pairT K (fact L)))
      (T lB x D₁ (pairT K (fact L)) + T fB x D₂ (pairT K (fact L)) + num 24 * (fact L * x)) := by
  have h2 : Γ ⊢[PRAAx] le one D₂ := le_trans h1 h12
  have bl1 := natEq (block_id (Γ := Γ) lB x D₁ (pairT K (fact L)))
  have bl2 := natEq (block_id (Γ := Γ) lB x D₂ (pairT K (fact L)))
  have bf1 := natEq (block_id (Γ := Γ) fB x D₁ (pairT K (fact L)))
  have bf2 := natEq (block_id (Γ := Γ) fB x D₂ (pairT K (fact L)))
  have gl := natEq (g_lam_indep (Γ := Γ) x D₁ D₂ (pairT K (fact L)))
  have gf := natEq (g_f_indep (Γ := Γ) x D₁ D₂ K (fact L))
  have u1 := excess_upper h1 (le_trans h12 h2x) hK1 hPK hNN hKx hP
  have l2 := excess_lower h2 h2x hK1 hPK' hNN' hKx hP
  ipra_le sl u1 + sl l2 with bl1 - bl2 + bf2 - bf1 + gl - gf

/-- `Σ_{D₁<d≤D₂} F⌊x/d⌋ ≤ Σ_{D₁<d≤D₂} ψ(⌊x/d⌋) + 24 F x`. -/
theorem block_lower :
    Γ ⊢[PRAAx] le (T fB x D₂ (pairT K (fact L)) + T lB x D₁ (pairT K (fact L)))
      (T fB x D₁ (pairT K (fact L)) + T lB x D₂ (pairT K (fact L)) + num 24 * (fact L * x)) := by
  have h2 : Γ ⊢[PRAAx] le one D₂ := le_trans h1 h12
  have bl1 := natEq (block_id (Γ := Γ) lB x D₁ (pairT K (fact L)))
  have bl2 := natEq (block_id (Γ := Γ) lB x D₂ (pairT K (fact L)))
  have bf1 := natEq (block_id (Γ := Γ) fB x D₁ (pairT K (fact L)))
  have bf2 := natEq (block_id (Γ := Γ) fB x D₂ (pairT K (fact L)))
  have gl := natEq (g_lam_indep (Γ := Γ) x D₁ D₂ (pairT K (fact L)))
  have gf := natEq (g_f_indep (Γ := Γ) x D₁ D₂ K (fact L))
  have l1 := excess_lower h1 (le_trans h12 h2x) hK1 hPK hNN hKx hP
  have u2 := excess_upper h2 h2x hK1 hPK' hNN' hKx hP
  ipra_le sl l1 + sl u2 with bf1 - bf2 + bl2 - bl1 + gf - gl

end Block

end LeanProofs.IPRA.AnalyticNumberTheory.BlockMean
