import IPRADerivations.DiophantineNumberTheory.KhinchinRoundWrapper

/-!
# The (K2) round theorem (`hurwitz_khinchin_ipra`)

Packet: `diophantine-number-theory/hurwitz_khinchin_ipra`, `khinchin.tex`, §"Amplification by the finitely many
residual gaps": "For each gap of positive length, apply the block construction to its interior `J` and add its
block union to `U_j` … If `R_j = |[0,1] ∖ U_j|`, (K11) gives `R_{j+1} ≤ (1 − 1/b₀) R_j`", `b₀ = 16384`, and "Freeze
the old gap list at the beginning of the round: process each old gap once, aggregate the new intervals, and only
then compute the next gap list."

Across rounds the coarse bits are the frozen residual of the previous round, carried as a code `z`; so the round
parameter is `⟨z, x⟩` with `x = px r B K₀ M R G' p`, the bits are `w(g, ⟨z, x⟩)`, and the new coverage `vZ` ignores
`z`:

* `vZ_at`: `sg(vZ(k, ⟨g, ⟨z, x⟩⟩)) = sg(⋃_g)(rg + k)` (`KhinchinRoundWrapper.vB_at` after dropping `z`);
* `k2_round_z`: on the coarse grid of `G = p + 1` cells with `r` fine cells each and `T = R! G' = rG`, `M ≥ 1`, if
  every cell's block satisfies the conclusion of `KhinchinBlock.block_cover` and the margins of `block_out`, and the
  coarse bits are `w_g ≤ 1`, then `16384 Σ_g rs_g ≤ 16383 r Σ_g w_g`, i.e. `R_{j+1} ≤ (1 − 1/16384) R_j` in the
  fine unit. Per cell it applies `KhinchinCellBridge.cell_bridge`, identifies the cell sum with the round's coverage
  body by `vZ_at` (`sum_congr_bounded`), and concludes with `KhinchinRoundCounts.round_from_counts`.
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.KhinchinK2RoundZ

open_ipra exports
open LeanProofs.IPRA.Signum (sg)
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinBlockScales (Xt bB)
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinCellParams (αc γc b0c)
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinCellBridge (cell_bridge)
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinRoundCounts (round_from_counts rsB wB)
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinRoundWrapper (px vB vB_at)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The new fine coverage with the carried parameter: `vZ(k, ⟨g, ⟨z, x⟩⟩) = v(k, ⟨g, x⟩)`. -/
def vZ (wb : PTm 2) : PTm 2 := Syn.subst ![var 0, pairT (fstT (var 1)) (sndT (sndT (var 1)))] (vB wb)

theorem inst2_vZ (wb : PTm 2) (k y : PTm n) :
    inst2 (vZ wb) k y = inst2 (vB wb) k (pairT (fstT y) (sndT (sndT y))) := by
  simp only [inst2, vZ]
  rw [Syn.subst_subst]
  exact congrArg (fun σ => Syn.subst σ (vB wb)) (funext fun i => by fin_cases i <;> simp)

theorem vZ_at (wb : PTm 2) (k g z r B K0 M R G' p : PTm n) :
    Γ ⊢[PRAAx] inst2 (sg (vZ wb)) k (pairT g (pairT z (px r B K0 M R G' p))) ≐
      inst2 (offB (sg (oB (bB wb)))) k (pairT (r * g) (pairT B (Xt K0 M R G' (αc g) (γc g) (b0c p)))) := by
  rw [show inst2 (sg (vZ wb)) k (pairT g (pairT z (px r B K0 M R G' p))) =
      sg (inst2 (vZ wb) k (pairT g (pairT z (px r B K0 M R G' p)))) by simp [inst2, Signum.sg], inst2_vZ]
  have e : Γ ⊢[PRAAx] pairT (fstT (pairT g (pairT z (px r B K0 M R G' p))))
        (sndT (sndT (pairT g (pairT z (px r B K0 M R G' p))))) ≐ pairT g (px r B K0 M R G' p) :=
    congrPairT (fst_pair _ _) ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _))
  have h1 := LeanProofs.IPRA.Foundations.CoverLocal.congrSg' (congrInst2 (vB wb) (.eqRefl k) e)
  have h2 := vB_at (Γ := Γ) wb k g r B K0 M R G' p
  rw [show inst2 (sg (vB wb)) k (pairT g (px r B K0 M R G' p)) = sg (inst2 (vB wb) k (pairT g (px r B K0 M R G' p)))
    by simp [inst2, Signum.sg]] at h2
  exact h1.eqTrans h2

/-- One round of (K2) with bits `w(g, ⟨z, x⟩)`: `16384 Σ_g rs_g ≤ 16383 r Σ_g w_g`. -/
theorem k2_round_z (wb w : PTm 2) {z B K0 M R G' p r : PTm n}
    (hT : Γ ⊢[PRAAx] fact R * G' ≐ r * succ p) (hM : Γ ⊢[PRAAx] le one M)
    (hw : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift (succ p)) ⟶
      le (inst2 w (var 0) (Syn.shift (pairT z (px r B K0 M R G' p)))) one))
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
    Γ ⊢[PRAAx] le (succ (num 16383) * ap2 (sumF (rsB w (vZ wb))) (succ p) (pairT r (pairT z (px r B K0 M R G' p))))
      ((num 16383 * r) * ap2 (sumF (wB w)) (succ p) (pairT r (pairT z (px r B K0 M R G' p)))) := by
  refine round_from_counts w (vZ wb) (num 16383) r (succ p) (pairT z (px r B K0 M R G' p)) (.allI (.impI ?_))
  let Θ : List (Fm PTm (n + 1)) := lt (var 0) (Syn.shift (succ p)) :: Γ.map Fm.shift
  have hT0 : Γ.map Fm.shift ⊢[PRAAx] fact (Syn.shift R) * Syn.shift G' ≐ Syn.shift r * succ (Syn.shift p) := by
    simpa [Syn.shift] using Order.shift_eq hT
  have hM0 : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift M) := Order.shift_one_le hM
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
  rw [show Syn.shift (pairT z (px r B K0 M R G' p)) =
      pairT (Syn.shift z) (px (Syn.shift r) (Syn.shift B) (Syn.shift K0) (Syn.shift M) (Syn.shift R) (Syn.shift G')
        (Syn.shift p)) by simp [Syn.shift, px]] at hw1 ⊢
  have es : Θ ⊢[PRAAx] ap2 (sumF (sg (vZ wb))) (Syn.shift r)
        (pairT (var 0) (pairT (Syn.shift z) (px (Syn.shift r) (Syn.shift B) (Syn.shift K0) (Syn.shift M) (Syn.shift R)
          (Syn.shift G') (Syn.shift p)))) ≐
      ap2 (sumF (offB (sg (oB (bB wb))))) (Syn.shift r)
        (pairT (Syn.shift r * var 0) (pairT (Syn.shift B) (Xt (Syn.shift K0) (Syn.shift M) (Syn.shift R)
          (Syn.shift G') (αc (var 0)) (γc (var 0)) (b0c (Syn.shift p))))) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [show Syn.shift (pairT (var 0 : PTm (n + 1)) (pairT (Syn.shift z) (px (Syn.shift r) (Syn.shift B) (Syn.shift K0)
          (Syn.shift M) (Syn.shift R) (Syn.shift G') (Syn.shift p)))) =
        pairT (var 1) (pairT (Syn.shift (Syn.shift z)) (px (Syn.shift (Syn.shift r)) (Syn.shift (Syn.shift B))
          (Syn.shift (Syn.shift K0)) (Syn.shift (Syn.shift M)) (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift G'))
          (Syn.shift (Syn.shift p)))) by
        simp [Syn.shift, px],
      show Syn.shift (pairT (Syn.shift r * var 0) (pairT (Syn.shift B) (Xt (Syn.shift K0) (Syn.shift M)
          (Syn.shift R) (Syn.shift G') (αc (var 0 : PTm (n + 1))) (γc (var 0)) (b0c (Syn.shift p))))) =
        pairT (Syn.shift (Syn.shift r) * var 1) (pairT (Syn.shift (Syn.shift B)) (Xt (Syn.shift (Syn.shift K0))
          (Syn.shift (Syn.shift M)) (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift G')) (αc (var 1)) (γc (var 1))
          (b0c (Syn.shift (Syn.shift p))))) by
        simp [Syn.shift, Xt]]
    exact vZ_at wb (var 0) (var 1) _ _ _ _ _ _ _ _
  have ee := natEq es
  rw [show Syn.shift (num 16383 : PTm n) = num 16383 by simp [Syn.shift]]
  refine .andI hw1 ?_
  ipra_le sl cb + 𝔞 (Syn.shift r) * sl hw1 with 16384 * ee

end LeanProofs.IPRA.DiophantineNumberTheory.KhinchinK2RoundZ
