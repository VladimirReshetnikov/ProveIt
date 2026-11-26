import IPRADerivations.AnalyticNumberTheory.BlockDispatch
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.Header

/-!
# The finite block deficit (`pnt_ipra_constructive_2026-11-14`, Lemma `con:deficit`)

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`, `contraction.tex`, Lemma `con:deficit` (Finite
block deficit): "Suppose `ε ≤ a ≤ 4` and `|r(t)| ≤ a` throughout a block `[s, s + H]` … Then
`∫_s^{s+H} (a − |r(t)|) dt ≥ 1/(64q²)`. The proof needs only finitely many comparisons of rational numbers."

The block is `D₁ < d ≤ D₂` with midpoint `D_h`; both halves have harmonic length `≥ F H₀`; the stage bound
`D|ψ(m) − Fm| ≤ AFm` holds on the block; `1 ≤ A ≤ 4D` and `16 D A H₀ ≥ 3A² + 384D²`. Then (`block_deficit`)

  `3 A² F x ≤ 48 D Σ_{D₁<d≤D₂} g + 100 A D F (D₂ + ⌊x/D₁⌋)`,  `g = AQ ∸ D|P − Q|`,

by three cases read from bounded searches: no high sample on the upper half (`case_A`), no low sample on the lower
half (`case_B`), or both, when `CrossingSearch.crossing` gives the crossing pair (`case_C_core`, with the interior
hypothesis `interior`).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.BlockDeficitMain

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (S)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicMertens (le_scale)
open LeanProofs.IPRA.AnalyticNumberTheory.BlockTests (four hiB loB)
open LeanProofs.IPRA.AnalyticNumberTheory.BlockDeficit (gzB OnBlock stg Pm Qm Bs')
open LeanProofs.IPRA.AnalyticNumberTheory.BlockCases (case_A case_B block_mono)
open LeanProofs.IPRA.AnalyticNumberTheory.BlockCross (case_C_core)
open LeanProofs.IPRA.AnalyticNumberTheory.BlockDispatch (off_at mid_fail hi_pass lo_pass onblock_A onblock_B Pl Psh)
open LeanProofs.IPRA.Foundations.BoundedReflection (exB wit ex_cases ex_elim)
open LeanProofs.IPRA.Foundations.CrossingSearch (uT vT crossing between_not_high between_not_low u_ge ne_transport)
open LeanProofs.IPRA.AnalyticNumberTheory.AbsDiff (absd)
open LeanProofs.IPRA.Analysis.Products (fact)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- The crossing searches run from the base `D₁ + 1`. -/
abbrev PP (x D₁ D₂ A Ds K L : PTm n) : PTm n := pairT (succ D₁) (Pl x D₁ D₂ A Ds K L)

section Interior

variable {x D₁ D₂ A Ds K L i0 j0 : PTm n}

theorem shift_du : Syn.shift (succ D₁ + uT (offB loB) (offB hiB) i0 j0 (PP x D₁ D₂ A Ds K L)) =
    succ (Syn.shift D₁) + uT (offB loB) (offB hiB) (Syn.shift i0) (Syn.shift j0) (Syn.shift (PP x D₁ D₂ A Ds K L)) := by
  simp [Syn.shift]

theorem shift_dv : Syn.shift (pred (succ D₁ + vT (offB hiB) i0 j0 (PP x D₁ D₂ A Ds K L))) =
    pred (succ (Syn.shift D₁) + vT (offB hiB) (Syn.shift i0) (Syn.shift j0) (Syn.shift (PP x D₁ D₂ A Ds K L))) := by
  simp [Syn.shift]

theorem shift_pp : Syn.shift (PP x D₁ D₂ A Ds K L) = pairT (succ (Syn.shift D₁)) (Psh x D₁ D₂ A Ds K L) := by
  simp [Syn.shift, PP, Pl, Psh, BlockSums.Y]

/-- The binder context of the interior block. -/
abbrev ICtx (x D₁ D₂ A Ds K L i0 j0 : PTm n) (Γ : List (Fm PTm n)) : List (Fm PTm (n + 1)) :=
  le (var 0) (Syn.shift (pred (succ D₁ + vT (offB hiB) i0 j0 (PP x D₁ D₂ A Ds K L)))) ::
    lt (Syn.shift (succ D₁ + uT (offB loB) (offB hiB) i0 j0 (PP x D₁ D₂ A Ds K L))) (var 0) ::
    lt (var 0) (Syn.shift (succ x)) :: Γ.map Fm.shift

/-- Between the crossing samples neither test passes: `2D|P − Q| ≤ AQ` on the interior block. -/
theorem interior (hi0 : Γ ⊢[PRAAx] neg (inst2 (offB loB) i0 (PP x D₁ D₂ A Ds K L) ≐ zero)) :
    Γ ⊢[PRAAx] OnBlock x (succ D₁ + uT (offB loB) (offB hiB) i0 j0 (PP x D₁ D₂ A Ds K L))
      (pred (succ D₁ + vT (offB hiB) i0 j0 (PP x D₁ D₂ A Ds K L)))
      (le (two * (Syn.shift Ds * absd (Pm x K L) (Qm x L))) (Syn.shift A * Qm x L)) := by
  have hi0' : (Γ.map Fm.shift) ⊢[PRAAx]
      neg (inst2 (offB loB) (Syn.shift i0) (Syn.shift (PP x D₁ D₂ A Ds K L)) ≐ zero) := by
    simpa [Fm.shift, Syn.shift, subst_inst2] using hi0.shift
  refine .allI (.impI (.impI (.impI ?_)))
  -- the three binder hypotheses, with the shifted bounds rewritten
  have hA : (le (var 0) (Syn.shift (pred (succ D₁ + vT (offB hiB) i0 j0 (PP x D₁ D₂ A Ds K L)))) ::
      lt (Syn.shift (succ D₁ + uT (offB loB) (offB hiB) i0 j0 (PP x D₁ D₂ A Ds K L))) (var 0) ::
      lt (var 0) (Syn.shift (succ x)) :: Γ.map Fm.shift) ⊢[PRAAx]
      lt (succ (Syn.shift D₁) + uT (offB loB) (offB hiB) (Syn.shift i0) (Syn.shift j0)
        (Syn.shift (PP x D₁ D₂ A Ds K L))) (var 0) := by
    have h0 : (le (var 0) (Syn.shift (pred (succ D₁ + vT (offB hiB) i0 j0 (PP x D₁ D₂ A Ds K L)))) ::
        lt (Syn.shift (succ D₁ + uT (offB loB) (offB hiB) i0 j0 (PP x D₁ D₂ A Ds K L))) (var 0) ::
        lt (var 0) (Syn.shift (succ x)) :: Γ.map Fm.shift) ⊢[PRAAx]
        lt (Syn.shift (succ D₁ + uT (offB loB) (offB hiB) i0 j0 (PP x D₁ D₂ A Ds K L))) (var 0) := .hyp (by simp)
    rw [shift_du, shift_dv] at h0 ⊢; exact h0
  have hB : (le (var 0) (Syn.shift (pred (succ D₁ + vT (offB hiB) i0 j0 (PP x D₁ D₂ A Ds K L)))) ::
      lt (Syn.shift (succ D₁ + uT (offB loB) (offB hiB) i0 j0 (PP x D₁ D₂ A Ds K L))) (var 0) ::
      lt (var 0) (Syn.shift (succ x)) :: Γ.map Fm.shift) ⊢[PRAAx]
      le (var 0) (pred (succ (Syn.shift D₁) + vT (offB hiB) (Syn.shift i0) (Syn.shift j0)
        (Syn.shift (PP x D₁ D₂ A Ds K L)))) := by
    have h0 : (le (var 0) (Syn.shift (pred (succ D₁ + vT (offB hiB) i0 j0 (PP x D₁ D₂ A Ds K L)))) ::
        lt (Syn.shift (succ D₁ + uT (offB loB) (offB hiB) i0 j0 (PP x D₁ D₂ A Ds K L))) (var 0) ::
        lt (var 0) (Syn.shift (succ x)) :: Γ.map Fm.shift) ⊢[PRAAx]
        le (var 0) (Syn.shift (pred (succ D₁ + vT (offB hiB) i0 j0 (PP x D₁ D₂ A Ds K L)))) := Prf.hyp0
    rw [shift_du, shift_dv] at h0 ⊢; exact h0
  -- the index `i = d − (D₁ + 1)` lies strictly between `u` and `v`
  have ug : ICtx x D₁ D₂ A Ds K L i0 j0 Γ ⊢[PRAAx]
      le (Syn.shift i0) (uT (offB loB) (offB hiB) (Syn.shift i0) (Syn.shift j0) (Syn.shift (PP x D₁ D₂ A Ds K L))) :=
    (u_ge (offB loB) (offB hiB) (j0 := Syn.shift j0) hi0').wk.wk.wk
  have ei := eq_add_of_le (le_trans (le_add_right (succ (Syn.shift D₁)) _) (le_of_lt hA))
  have e1 := natEq ei
  have e2 := natEq (eq_add_of_le hA)
  have ps : (le (var 0) (Syn.shift (pred (succ D₁ + vT (offB hiB) i0 j0 (PP x D₁ D₂ A Ds K L)))) ::
      lt (Syn.shift (succ D₁ + uT (offB loB) (offB hiB) i0 j0 (PP x D₁ D₂ A Ds K L))) (var 0) ::
      lt (var 0) (Syn.shift (succ x)) :: Γ.map Fm.shift) ⊢[PRAAx]
      pred (succ (Syn.shift D₁) + vT (offB hiB) (Syn.shift i0) (Syn.shift j0) (Syn.shift (PP x D₁ D₂ A Ds K L))) ≐
        Syn.shift D₁ + vT (offB hiB) (Syn.shift i0) (Syn.shift j0) (Syn.shift (PP x D₁ D₂ A Ds K L)) :=
    (congrPred (by ipra_ring)).eqTrans (pred_succ _)
  have e3 := natEq (eq_add_of_le (le_congr (.eqRefl _) ps hB))
  have hu : ICtx x D₁ D₂ A Ds K L i0 j0 Γ ⊢[PRAAx] lt (uT (offB loB) (offB hiB) (Syn.shift i0) (Syn.shift j0) (Syn.shift (PP x D₁ D₂ A Ds K L)))
      (monus (var 0) (succ (Syn.shift D₁))) := by ipra_le sl hA with e1
  have hv : ICtx x D₁ D₂ A Ds K L i0 j0 Γ ⊢[PRAAx] lt (monus (var 0) (succ (Syn.shift D₁)))
      (vT (offB hiB) (Syn.shift i0) (Syn.shift j0) (Syn.shift (PP x D₁ D₂ A Ds K L))) := by
    ipra_le 𝔞 (monus (Syn.shift D₁ + vT (offB hiB) (Syn.shift i0) (Syn.shift j0) (Syn.shift (PP x D₁ D₂ A Ds K L)))
      (var 0)) with e1 + e3
  have hz1 := between_not_high (offB loB) (offB hiB) hi0'.wk.wk.wk hu hv
  have hz2 := between_not_low (offB hiB) (lt_of_le_of_lt ug hu) hv
  rw [shift_pp] at hz1 hz2
  have z1 := ((congrInst2 hiB ei (.eqRefl _)).eqTrans (off_at _ _ _ _).eqSymm).eqTrans hz2
  have z2 := ((congrInst2 loB ei (.eqRefl _)).eqTrans (off_at _ _ _ _).eqSymm).eqTrans hz1
  exact mid_fail z1 z2

end Interior

section Main

variable {x D₁ Dh D₂ A Ds K L H0 : PTm n}

/-- The common conclusion. -/
abbrev Concl (x D₁ D₂ A Ds K L : PTm n) : Fm PTm n :=
  le (num 3 * (A * (A * (fact L * x))))
    (num 48 * (Ds * Bs' gzB x D₁ D₂ A Ds K L) + num 100 * (A * (Ds * (fact L * (D₂ + quo x D₁)))))

theorem blk_A (h1 : Γ ⊢[PRAAx] le one D₁) (h1h : Γ ⊢[PRAAx] le D₁ Dh) (hh2 : Γ ⊢[PRAAx] le Dh D₂)
    (h2x : Γ ⊢[PRAAx] le D₂ x) (h2L : Γ ⊢[PRAAx] le D₂ L) (hK1 : Γ ⊢[PRAAx] le one K)
    (hPKh : Γ ⊢[PRAAx] le (quo x Dh) K) (hPK2 : Γ ⊢[PRAAx] le (quo x D₂) K)
    (hNNh : Γ ⊢[PRAAx] le (K * pw (quo x Dh) (quo x Dh)) L) (hNN2 : Γ ⊢[PRAAx] le (K * pw (quo x D₂) (quo x D₂)) L)
    (hKx : Γ ⊢[PRAAx] le (K * x) L) (hP : Γ ⊢[PRAAx] le (K * pw two (two * (two * x))) L)
    (hSa : Γ ⊢[PRAAx] le (S Dh (fact L) + fact L * H0) (S D₂ (fact L)))
    (hH0 : Γ ⊢[PRAAx] le (num 3 * (A * A) + num 384 * (Ds * Ds)) (num 16 * (Ds * (A * H0))))
    (hst : Γ ⊢[PRAAx] OnBlock x D₁ D₂ (stg x A Ds K L))
    (hz : Γ ⊢[PRAAx] exB (offB hiB) (monus D₂ Dh) (pairT (succ Dh) (Pl x D₁ D₂ A Ds K L)) ≐ zero) :
    Γ ⊢[PRAAx] Concl x D₁ D₂ A Ds K L := by
  have cA := case_A (le_trans h1 h1h) hh2 h2x h2L hK1 hPKh hPK2 hNNh hNN2 hKx hP hSa hH0 (onblock_A h1h hst hz)
  have bm := block_mono (A := A) (Ds := Ds) (K := K) (L := L) (x := x) h1h (le_refl D₂) hh2
  ipra_le sl cA + 48 * 𝔞 Ds * sl bm + 84 * 𝔞 A * 𝔞 Ds * 𝔞 (fact L) * 𝔞 D₂ +
    100 * 𝔞 A * 𝔞 Ds * 𝔞 (fact L) * 𝔞 (quo x D₁)

theorem blk_B (h1 : Γ ⊢[PRAAx] le one D₁) (h1h : Γ ⊢[PRAAx] le D₁ Dh) (hh2 : Γ ⊢[PRAAx] le Dh D₂)
    (h2x : Γ ⊢[PRAAx] le D₂ x) (h2L : Γ ⊢[PRAAx] le D₂ L) (hK1 : Γ ⊢[PRAAx] le one K)
    (hPK1 : Γ ⊢[PRAAx] le (quo x D₁) K) (hPKh : Γ ⊢[PRAAx] le (quo x Dh) K)
    (hNN1 : Γ ⊢[PRAAx] le (K * pw (quo x D₁) (quo x D₁)) L) (hNNh : Γ ⊢[PRAAx] le (K * pw (quo x Dh) (quo x Dh)) L)
    (hKx : Γ ⊢[PRAAx] le (K * x) L) (hP : Γ ⊢[PRAAx] le (K * pw two (two * (two * x))) L)
    (hSb : Γ ⊢[PRAAx] le (S D₁ (fact L) + fact L * H0) (S Dh (fact L)))
    (hH0 : Γ ⊢[PRAAx] le (num 3 * (A * A) + num 384 * (Ds * Ds)) (num 16 * (Ds * (A * H0))))
    (hst : Γ ⊢[PRAAx] OnBlock x D₁ D₂ (stg x A Ds K L))
    (hz : Γ ⊢[PRAAx] exB (offB loB) (monus Dh D₁) (pairT (succ D₁) (Pl x D₁ D₂ A Ds K L)) ≐ zero) :
    Γ ⊢[PRAAx] Concl x D₁ D₂ A Ds K L := by
  have cB := case_B h1 h1h (le_trans hh2 h2x) (le_trans hh2 h2L) hK1 hPK1 hPKh hNN1 hNNh hKx hP hSb hH0
    (onblock_B hh2 hst hz)
  have bm := block_mono (A := A) (Ds := Ds) (K := K) (L := L) (x := x) (le_refl D₁) hh2 h1h
  ipra_le sl cB + 48 * 𝔞 Ds * sl bm + 16 * 𝔞 A * 𝔞 Ds * 𝔞 (fact L) * sl hh2 +
    84 * 𝔞 A * 𝔞 Ds * 𝔞 (fact L) * 𝔞 D₂ + 100 * 𝔞 A * 𝔞 Ds * 𝔞 (fact L) * 𝔞 (quo x D₁)

theorem blk_C (h1 : Γ ⊢[PRAAx] le one D₁) (h1h : Γ ⊢[PRAAx] le D₁ Dh) (hh2 : Γ ⊢[PRAAx] le Dh D₂)
    (h2x : Γ ⊢[PRAAx] le D₂ x) (h2L : Γ ⊢[PRAAx] le D₂ L) (hK1 : Γ ⊢[PRAAx] le one K)
    (hP : Γ ⊢[PRAAx] le (K * pw two (two * (two * x))) L)
    (hA1 : Γ ⊢[PRAAx] le one A) (hA4 : Γ ⊢[PRAAx] le A (two * (two * Ds)))
    (hzh : Γ ⊢[PRAAx] exB (offB hiB) (monus D₂ Dh) (pairT (succ Dh) (Pl x D₁ D₂ A Ds K L)) ≐ one)
    (hzl : Γ ⊢[PRAAx] exB (offB loB) (monus Dh D₁) (PP x D₁ D₂ A Ds K L) ≐ one) :
    Γ ⊢[PRAAx] Concl x D₁ D₂ A Ds K L := by
  have ew := ex_elim (offB hiB) hzh
  have el := ex_elim (offB loB) hzl
  have ar : Γ ⊢[PRAAx] succ Dh + wit (offB hiB) (monus D₂ Dh) (pairT (succ Dh) (Pl x D₁ D₂ A Ds K L)) ≐
      succ D₁ + (monus Dh D₁ + wit (offB hiB) (monus D₂ Dh) (pairT (succ Dh) (Pl x D₁ D₂ A Ds K L))) := by
    ipra_lc natEq (eq_add_of_le h1h)
  have hj0 : Γ ⊢[PRAAx] neg (inst2 (offB hiB)
      (monus Dh D₁ + wit (offB hiB) (monus D₂ Dh) (pairT (succ Dh) (Pl x D₁ D₂ A Ds K L)))
      (PP x D₁ D₂ A Ds K L) ≐ zero) :=
    ne_transport ((off_at _ _ _ _).eqTrans ((congrInst2 hiB ar (.eqRefl _)).eqTrans (off_at _ _ _ _).eqSymm))
      (Prf.andE₂ ew)
  have hlt : Γ ⊢[PRAAx] lt (wit (offB loB) (monus Dh D₁) (PP x D₁ D₂ A Ds K L))
      (monus Dh D₁ + wit (offB hiB) (monus D₂ Dh) (pairT (succ Dh) (Pl x D₁ D₂ A Ds K L))) :=
    lt_of_lt_of_le (Prf.andE₁ el) (le_add_right _ _)
  have cr := crossing (offB loB) (offB hiB) (Prf.andE₂ el) hj0 hlt
  have hlo := lo_pass (ne_transport (off_at _ _ _ _) (Prf.andE₁ (Prf.andE₁ cr)))
  have hhi := hi_pass (ne_transport (off_at _ _ _ _) (Prf.andE₂ (Prf.andE₁ cr)))
  have huv := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ cr))
  have hvj := Prf.andE₂ (Prf.andE₂ (Prf.andE₂ cr))
  have hwl := Prf.andE₁ ew
  have hint := interior (j0 := monus Dh D₁ + wit (offB hiB) (monus D₂ Dh) (pairT (succ Dh) (Pl x D₁ D₂ A Ds K L)))
    (Prf.andE₂ el)
  have eDh := natEq (eq_add_of_le h1h)
  have eD2 := natEq (eq_add_of_le hh2)
  refine case_C_core h1 (by ipra_le 𝔞 (uT (offB loB) (offB hiB) (wit (offB loB) (monus Dh D₁) (PP x D₁ D₂ A Ds K L)) (monus Dh D₁ + wit (offB hiB) (monus D₂ Dh) (pairT (succ Dh) (Pl x D₁ D₂ A Ds K L))) (PP x D₁ D₂ A Ds K L)) + 1)
    (by ipra_le sl huv) (by ipra_le sl hvj + sl hwl with eD2 + eDh) h2x h2L hK1 hP hA1 hA4 hlo hhi hint

/-- Lemma `con:deficit`, finitely: `3 A² F x ≤ 48 D Σ_{D₁<d≤D₂} g + 100 A D F (D₂ + ⌊x/D₁⌋)`. -/
theorem block_deficit (h1 : Γ ⊢[PRAAx] le one D₁) (h1h : Γ ⊢[PRAAx] le D₁ Dh) (hh2 : Γ ⊢[PRAAx] le Dh D₂)
    (h2x : Γ ⊢[PRAAx] le D₂ x) (h2L : Γ ⊢[PRAAx] le D₂ L) (hK1 : Γ ⊢[PRAAx] le one K)
    (hPK1 : Γ ⊢[PRAAx] le (quo x D₁) K) (hPKh : Γ ⊢[PRAAx] le (quo x Dh) K) (hPK2 : Γ ⊢[PRAAx] le (quo x D₂) K)
    (hNN1 : Γ ⊢[PRAAx] le (K * pw (quo x D₁) (quo x D₁)) L) (hNNh : Γ ⊢[PRAAx] le (K * pw (quo x Dh) (quo x Dh)) L)
    (hNN2 : Γ ⊢[PRAAx] le (K * pw (quo x D₂) (quo x D₂)) L)
    (hKx : Γ ⊢[PRAAx] le (K * x) L) (hP : Γ ⊢[PRAAx] le (K * pw two (two * (two * x))) L)
    (hA1 : Γ ⊢[PRAAx] le one A) (hA4 : Γ ⊢[PRAAx] le A (two * (two * Ds)))
    (hSa : Γ ⊢[PRAAx] le (S Dh (fact L) + fact L * H0) (S D₂ (fact L)))
    (hSb : Γ ⊢[PRAAx] le (S D₁ (fact L) + fact L * H0) (S Dh (fact L)))
    (hH0 : Γ ⊢[PRAAx] le (num 3 * (A * A) + num 384 * (Ds * Ds)) (num 16 * (Ds * (A * H0))))
    (hst : Γ ⊢[PRAAx] OnBlock x D₁ D₂ (stg x A Ds K L)) :
    Γ ⊢[PRAAx] Concl x D₁ D₂ A Ds K L := by
  refine .orE (ex_cases (offB hiB) (monus D₂ Dh) (pairT (succ Dh) (Pl x D₁ D₂ A Ds K L))) ?_ ?_
  · exact blk_A h1.wk h1h.wk hh2.wk h2x.wk h2L.wk hK1.wk hPKh.wk hPK2.wk hNNh.wk hNN2.wk hKx.wk hP.wk hSa.wk hH0.wk
      hst.wk Prf.hyp0
  · refine .orE (ex_cases (offB loB) (monus Dh D₁) (PP x D₁ D₂ A Ds K L)) ?_ ?_
    · exact blk_B h1.wk.wk h1h.wk.wk hh2.wk.wk h2x.wk.wk h2L.wk.wk hK1.wk.wk hPK1.wk.wk hPKh.wk.wk hNN1.wk.wk
        hNNh.wk.wk hKx.wk.wk hP.wk.wk hSb.wk.wk hH0.wk.wk hst.wk.wk Prf.hyp0
    · exact blk_C h1.wk.wk h1h.wk.wk hh2.wk.wk h2x.wk.wk h2L.wk.wk hK1.wk.wk hP.wk.wk hA1.wk.wk hA4.wk.wk
        Prf.hyp1 Prf.hyp0

end Main

end LeanProofs.IPRA.AnalyticNumberTheory.BlockDeficitMain
