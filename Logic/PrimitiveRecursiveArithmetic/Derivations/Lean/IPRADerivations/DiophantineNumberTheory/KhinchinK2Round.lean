import IPRADerivations.DiophantineNumberTheory.KhinchinRoundWrapper

/-!
# The (K2) round theorem (`hurwitz_khinchin_ipra`)

Packet: `diophantine-number-theory/hurwitz_khinchin_ipra`, `khinchin.tex`, §"Amplification by the finitely many
residual gaps": "For each gap of positive length, apply the block construction to its interior `J` and add its
block union to `U_j` … If `R_j = |[0,1] ∖ U_j|`, (K11) gives `R_{j+1} ≤ (1 − 1/b₀) R_j`", `b₀ = 16384`.

* `k2_round`: on the coarse grid of `G = p + 1` cells with `r` fine cells each and `T = R! G' = rG`, `M ≥ 1`, if
  every cell's block satisfies the conclusion of `KhinchinBlock.block_cover` and the margins of `block_out`, and the
  coarse bits are `w_g ≤ 1`, then `16384 Σ_g rs_g ≤ 16383 r Σ_g w_g` — i.e. `R_{j+1} ≤ (1 − 1/16384) R_j` in the
  fine unit. Per cell it applies `KhinchinCellBridge.cell_bridge`, identifies the cell sum with the round's
  coverage body by `KhinchinRoundWrapper.vB_at` (`sum_congr_bounded`), and concludes with
  `KhinchinRoundCounts.round_from_counts`.
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.KhinchinK2Round

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Signum (sg)
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinBlockScales (Xt bB)
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinCellParams (αc γc b0c)
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinCellBridge (cell_bridge)
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinRoundCounts (round_from_counts rsB wB)
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinRoundWrapper (px vB vB_at)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- One round of (K2): `16384 Σ_g rs_g ≤ 16383 r Σ_g w_g`. -/
theorem k2_round (wb w : PTm 2) {B K0 M R G' p r : PTm n}
    (hT : Γ ⊢[PRAAx] fact R * G' ≐ r * succ p) (hM : Γ ⊢[PRAAx] le one M)
    (hw : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift (succ p)) ⟶
      le (inst2 w (var 0) (Syn.shift (px r B K0 M R G' p))) one))
    (hcov : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift (succ p)) ⟶
      le (monus (γc (var 0)) (αc (var 0)) * (fact (Syn.shift R) * Syn.shift G'))
        (num 8192 * succ (b0c (Syn.shift p)) *
          ap2 (sumF (sg (oB (bB wb)))) (fact (Syn.shift R) * Syn.shift G' * Syn.shift M)
            (pairT (Syn.shift B) (Xt (Syn.shift K0) (Syn.shift M) (Syn.shift R) (Syn.shift G') (αc (var 0))
              (γc (var 0)) (b0c (Syn.shift p)))))))
    (hH : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift (succ p)) ⟶
      Fm.all (lt (var 0) (Syn.shift (Syn.shift B)) ⟶
        le (fact (Syn.shift (Syn.shift R)) * Syn.shift (Syn.shift G') * Syn.shift (γc (var 0)) +
            inst2 wb (var 0) (Xt (Syn.shift (Syn.shift K0)) (Syn.shift (Syn.shift M)) (Syn.shift (Syn.shift R))
              (Syn.shift (Syn.shift G')) (Syn.shift (αc (var 0))) (Syn.shift (γc (var 0)))
              (Syn.shift (b0c (Syn.shift p)))) * succ (Syn.shift (b0c (Syn.shift p))))
          (Syn.shift (Syn.shift r * var 0 + Syn.shift r) * succ (Syn.shift (b0c (Syn.shift p))))))) :
    Γ ⊢[PRAAx] le (succ (num 16383) * ap2 (sumF (rsB w (vB wb))) (succ p) (pairT r (px r B K0 M R G' p)))
      ((num 16383 * r) * ap2 (sumF (wB w)) (succ p) (pairT r (px r B K0 M R G' p))) := by
  refine round_from_counts w (vB wb) (num 16383) r (succ p) (px r B K0 M R G' p) (.allI (.impI ?_))
  let Θ : List (Fm PTm (n + 1)) := lt (var 0) (Syn.shift (succ p)) :: Γ.map Fm.shift
  have hT0 : Γ.map Fm.shift ⊢[PRAAx] fact (Syn.shift R) * Syn.shift G' ≐ Syn.shift r * succ (Syn.shift p) := by
    simpa [Fm.shift, Syn.shift] using hT.shift
  have hM0 : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift M) := by simpa [Fm.shift, Syn.shift] using hM.shift
  have hT1 : Θ ⊢[PRAAx] fact (Syn.shift R) * Syn.shift G' ≐ Syn.shift r * succ (Syn.shift p) := hT0.wk
  have hM1 : Θ ⊢[PRAAx] le one (Syn.shift M) := hM0.wk
  have hg : Θ ⊢[PRAAx] lt (var 0) (succ (Syn.shift p)) := by
    have h0 : Θ ⊢[PRAAx] lt (var 0) (Syn.shift (succ p)) := Prf.hyp0
    rwa [show Syn.shift (succ p) = succ (Syn.shift p) by simp [Syn.shift]] at h0
  have hw1 := Prf.impE (hw.allOpen.wk (ψ := lt (var 0) (Syn.shift (succ p)))) Prf.hyp0
  have hc1 := Prf.impE (hcov.allOpen.wk (ψ := lt (var 0) (Syn.shift (succ p)))) Prf.hyp0
  have hH1 := Prf.impE (hH.allOpen.wk (ψ := lt (var 0) (Syn.shift (succ p)))) Prf.hyp0
  have eT := natEq hT1
  have hHN : Θ ⊢[PRAAx] le (Syn.shift r * var 0 + Syn.shift r) (fact (Syn.shift R) * Syn.shift G' * Syn.shift M) := by
    ipra_le 𝔞 (Syn.shift r) * sl hg + 𝔞 (Syn.shift r) * (𝔞 (Syn.shift p) + 1) * sl hM1 with
      (𝔞 (Syn.shift M)) * eT
  have cb := cell_bridge wb hT1 hc1 hH1 hHN
  rw [show Syn.shift (px r B K0 M R G' p) =
      px (Syn.shift r) (Syn.shift B) (Syn.shift K0) (Syn.shift M) (Syn.shift R) (Syn.shift G') (Syn.shift p) by
        simp [Syn.shift, px]] at hw1 ⊢
  have es : Θ ⊢[PRAAx] ap2 (sumF (sg (vB wb))) (Syn.shift r)
        (pairT (var 0) (px (Syn.shift r) (Syn.shift B) (Syn.shift K0) (Syn.shift M) (Syn.shift R) (Syn.shift G')
          (Syn.shift p))) ≐
      ap2 (sumF (offB (sg (oB (bB wb))))) (Syn.shift r)
        (pairT (Syn.shift r * var 0) (pairT (Syn.shift B) (Xt (Syn.shift K0) (Syn.shift M) (Syn.shift R)
          (Syn.shift G') (αc (var 0)) (γc (var 0)) (b0c (Syn.shift p))))) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [show Syn.shift (pairT (var 0 : PTm (n + 1)) (px (Syn.shift r) (Syn.shift B) (Syn.shift K0) (Syn.shift M)
          (Syn.shift R) (Syn.shift G') (Syn.shift p))) =
        pairT (var 1) (px (Syn.shift (Syn.shift r)) (Syn.shift (Syn.shift B)) (Syn.shift (Syn.shift K0))
          (Syn.shift (Syn.shift M)) (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift G')) (Syn.shift (Syn.shift p))) by
        simp [Syn.shift, px],
      show Syn.shift (pairT (Syn.shift r * var 0) (pairT (Syn.shift B) (Xt (Syn.shift K0) (Syn.shift M)
          (Syn.shift R) (Syn.shift G') (αc (var 0 : PTm (n + 1))) (γc (var 0)) (b0c (Syn.shift p))))) =
        pairT (Syn.shift (Syn.shift r) * var 1) (pairT (Syn.shift (Syn.shift B)) (Xt (Syn.shift (Syn.shift K0))
          (Syn.shift (Syn.shift M)) (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift G')) (αc (var 1)) (γc (var 1))
          (b0c (Syn.shift (Syn.shift p))))) by
        simp [Syn.shift, Xt]]
    exact vB_at wb (var 0) (var 1) _ _ _ _ _ _ _
  have ee := natEq es
  rw [show Syn.shift (num 16383 : PTm n) = num 16383 by simp [Syn.shift]]
  refine .andI hw1 ?_
  ipra_le sl cb + 𝔞 (Syn.shift r) * sl hw1 with 16384 * ee


end LeanProofs.IPRA.DiophantineNumberTheory.KhinchinK2Round
