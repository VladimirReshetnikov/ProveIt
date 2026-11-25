import IPRADerivations.DiophantineNumberTheory.KhinchinGapRound

/-!
# One (K2) round on a refining grid (`hurwitz_khinchin_ipra`)

Packet: `diophantine-number-theory/hurwitz_khinchin_ipra`, `khinchin.tex`, §"Amplification by the finitely many
residual gaps": "For each gap of positive length, apply the block construction to its interior `J` and add its
block union to `U_j` … All added intervals are inside the gap in which they were constructed. If
`R_j = |[0,1] ∖ U_j|`, (K11) gives `R_{j+1} ≤ (1 − 1/b₀) R_j`."

The new intervals are finer than the old cells, so each round refines the grid: a coarse cell `g < G` is a block of
`r` fine cells. Per coarse cell, with `w_g ∈ {0, 1}` the "uncovered" bit, `rs_g` the fine residual and `cv_g` the
newly covered fine cells of block `g` (`rs_g + cv_g = r`):

* a covered coarse cell stays covered: `rs_g ≤ r w_g`;
* (K11) on an uncovered coarse cell: `w_g r ≤ (c+1) cv_g`, i.e. at least the fraction `1/(c+1)` is newly covered.

* `block_pt`: these give `(c+1) rs_g ≤ c r w_g` (two cases, `w_g = 0` and `w_g = 1`);
* `round_grid`: summed over the coarse cells, `(c+1) R' ≤ c r R` with `R' = Σ_g rs_g` the fine residual and
  `R = Σ_g w_g` the coarse residual — in the common unit of the fine grid, `(c+1) R_{j+1} ≤ c R_j`, the per-round
  hypothesis of `KhinchinRounds.amplify`. The fine residual is a sum over blocks by
  `Foundations.BlockPartitionSum.block_sum`.
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.KhinchinGridRound

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinBlock (sum_le_lin1)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- A bit `w ≤ 1` is `0` or `1`. -/
theorem bit_cases {w : PTm n} (hw : Γ ⊢[PRAAx] le w one) : Γ ⊢[PRAAx] (w ≐ zero) ⋎ (w ≐ one) := by
  refine .orE (zero_or_succ w) (.orI₁ Prf.hyp0) (.orI₂ ?_)
  have e := natEq (Prf.hyp0 : ((w ≐ succ (pred w)) :: Γ) ⊢[PRAAx] w ≐ succ (pred w))
  have hw' : ((w ≐ succ (pred w)) :: Γ) ⊢[PRAAx] le w one := hw.wk
  have hp : ((w ≐ succ (pred w)) :: Γ) ⊢[PRAAx] le (pred w) zero := by ipra_le sl hw' with e
  exact Prf.hyp0.eqTrans (congrSucc ((monus_zero _).eqSymm.eqTrans hp))

/-- One coarse cell: `(c+1) rs ≤ c r w`. -/
theorem block_pt {w r rs cv c : PTm n} (hw : Γ ⊢[PRAAx] le w one) (hsum : Γ ⊢[PRAAx] rs + cv ≐ r)
    (ha : Γ ⊢[PRAAx] le rs (r * w)) (hb : Γ ⊢[PRAAx] le (w * r) (succ c * cv)) :
    Γ ⊢[PRAAx] le (succ c * rs) (c * (r * w)) := by
  refine .orE (bit_cases hw) ?_ ?_
  · have ha' : ((w ≐ zero) :: Γ) ⊢[PRAAx] le rs (r * w) := ha.wk
    have ew := natEq (Prf.hyp0 : ((w ≐ zero) :: Γ) ⊢[PRAAx] w ≐ zero)
    ipra_le (𝔞 c + 1) * sl ha' with -(𝔞 r * ew)
  · have hb' : ((w ≐ one) :: Γ) ⊢[PRAAx] le (w * r) (succ c * cv) := hb.wk
    have ew := natEq (Prf.hyp0 : ((w ≐ one) :: Γ) ⊢[PRAAx] w ≐ one)
    have es := natEq (hsum.wk (ψ := w ≐ one))
    ipra_le sl hb' with (𝔞 c + 1) * 𝔞 r * ew - (𝔞 c + 1) * es

/-- The round on a refining grid: `(c+1) Σ_g rs_g ≤ c r Σ_g w_g`. -/
theorem round_grid (w rs cv : PTm 2) (c r G x : PTm n)
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift G) ⟶
      (le (inst2 w (var 0) (Syn.shift x)) one ⋏
        (inst2 rs (var 0) (Syn.shift x) + inst2 cv (var 0) (Syn.shift x) ≐ Syn.shift r)) ⋏
      (le (inst2 rs (var 0) (Syn.shift x)) (Syn.shift r * inst2 w (var 0) (Syn.shift x)) ⋏
        le (inst2 w (var 0) (Syn.shift x) * Syn.shift r) (succ (Syn.shift c) * inst2 cv (var 0) (Syn.shift x))))) :
    Γ ⊢[PRAAx] le (succ c * ap2 (sumF rs) G x) ((c * r) * ap2 (sumF w) G x) := by
  refine sum_le_lin1 _ _ _ _ _ _ _ (.allI (.impI ?_))
  have p := Prf.impE (h.allOpen.wk (ψ := lt (var 0) (Syn.shift G))) Prf.hyp0
  rw [show Syn.shift (succ c) = succ (Syn.shift c) by simp [Syn.shift],
    show Syn.shift (c * r) = Syn.shift c * Syn.shift r by simp [Syn.shift]]
  have b := block_pt (Prf.andE₁ (Prf.andE₁ p)) (Prf.andE₂ (Prf.andE₁ p)) (Prf.andE₁ (Prf.andE₂ p))
    (Prf.andE₂ (Prf.andE₂ p))
  exact le_congr (.eqRefl _) (by ipra_ring) b

end LeanProofs.IPRA.DiophantineNumberTheory.KhinchinGridRound
