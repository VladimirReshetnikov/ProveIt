import IPRADerivations.AnalyticNumberTheory.SelbergMobiusP
import IPRADerivations.AnalyticNumberTheory.ConvSummatory

/-!
# Selberg's identity summed up to `x` (`pnt_ipra_constructive_2026-11-14`, towards `sb:symmetry-bound`)

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`, `selberg.tex`, proof of Lemma `sb:symmetry`:
`A(x) = Σ_{n≤x} (Λ(n) log n + (Λ*Λ)(n)) = Σ_{n≤x} (μ * L²)(n)`, and "reversing finite sums" turns the right side
into `Σ_{d≤x} μ(d) P_2(x/d)`. For every prime weight `w` and parameter `y` (the harmonic logarithm's mesh), with
`B(m) = Σ_{1≤k≤m} L_w(k, y)²` and the signed Möbius function `μ = μ⁺ − μ⁻`:

  `Σ_{1≤d≤x} μ⁺(d) B(⌊x/d⌋) = A_w(x) + Σ_{1≤d≤x} μ⁻(d) B(⌊x/d⌋)`,
  `A_w(x) = Σ_{n≤x} (L_w(n, y) Λ_w(n, y) + (Λ_w * Λ_w)(n, y))`                 (`symmetry_sum`).

* `row_conv`: each row of `SelbergMobiusP.selberg_mobius_p` is the convolution `(μ^± * L_w²)(n)`, where the Möbius
  search bound is made independent of `n` by `MobiusBounds.mu_bound` (`μ^±_{n+1}(d) = μ^±_{d+1}(d)` for `d ≤ n`);
* `pt_n`: `(μ⁺ * L_w²)(n) = G_w(n) + (μ⁻ * L_w²)(n)` for every `n` (both sides vanish at `n = 0`);
* `symmetry_sum`: summed over `n ≤ x` and reversed by `ConvSummatory.conv_summatory`.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.SymmetrySum

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius
open LeanProofs.IPRA.AnalyticNumberTheory.WeightedMangoldt
open LeanProofs.IPRA.AnalyticNumberTheory.DirichletLeibniz (cvB conv cv_at)
open LeanProofs.IPRA.AnalyticNumberTheory.SelbergMobiusP (Gx QSP QSN inst2_QSP inst2_QSN selberg_mobius_p)
open LeanProofs.IPRA.AnalyticNumberTheory.ConvSummatory (RB conv_summatory)
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `μ⁺(d) = μ⁺_{d+1}(d)`. -/
abbrev aPB : PTm 2 := muP (succ (var 0)) (var 0)
/-- `μ⁻(d) = μ⁻_{d+1}(d)`. -/
abbrev aNB : PTm 2 := muN (succ (var 0)) (var 0)

theorem inst2_aP (d y : PTm n) : inst2 aPB d y = muP (succ d) d := by simp [inst2]
theorem inst2_aN (d y : PTm n) : inst2 aNB d y = muN (succ d) d := by simp [inst2]

section Sym

variable (w : PTm 2)

/-- `L_w(k, y)²`. -/
abbrev bL : PTm 2 := Lw w (var 0) (var 1) * Lw w (var 0) (var 1)
/-- `G_w(n, y) = L_w Λ_w + Λ_w * Λ_w`. -/
abbrev GxB : PTm 2 := Gx w (var 0) (var 1)

theorem inst2_bL (k y : PTm n) : inst2 (bL w) k y = Lw w k y * Lw w k y := by simp [inst2]
theorem inst2_GxB (k y : PTm n) : inst2 (GxB w) k y = Gx w k y := by simp [inst2]

theorem congrGx1 {e e' y : PTm n} (h : Γ ⊢[PRAAx] e ≐ e') : Γ ⊢[PRAAx] Gx w e y ≐ Gx w e' y :=
  congrAdd (congrMul (congrAp2 _ (congrSucc h) (congrPairT h (.eqRefl _)))
    (congrAp2 _ (congrSucc h) (congrPairT h (.eqRefl _)))) (congrAp2 _ (congrSucc h) (congrPairT h (.eqRefl _)))

/-- The row algebra over opaque terms: `(S E') M' (L'L') = (S E)(M (L L))` from `L' = L`, `M' = M`, `E' = E`. -/
theorem row_alg {S E E' M' Md L L' : PTm n} (eL : Γ ⊢[PRAAx] L' ≐ L) (eM : Γ ⊢[PRAAx] M' ≐ Md)
    (eE : Γ ⊢[PRAAx] E' ≐ E) : Γ ⊢[PRAAx] ((S * E') * M') * (L' * L') ≐ (S * E) * (Md * (L * L)) := by
  ipra_lc 𝔞 S * 𝔞 E' * 𝔞 M' * (𝔞 L' + 𝔞 L) * natEq eL + 𝔞 S * 𝔞 E' * 𝔞 L * 𝔞 L * natEq eM +
    𝔞 S * 𝔞 Md * 𝔞 L * 𝔞 L * natEq eE

/-- Both sides vanish when `S = 0`. -/
theorem row_zero {S E E' M' Md L L' : PTm n} (hS : Γ ⊢[PRAAx] S ≐ zero) :
    Γ ⊢[PRAAx] ((S * E') * M') * (L' * L') ≐ (S * E) * (Md * (L * L)) :=
  (zero_mul_l (zero_mul_l (zero_mul_l hS _) _) _).eqTrans (zero_mul_l (zero_mul_l hS _) _).eqSymm

/-- One summand of a row: `[d ∣ n] μ^±_{n+1}(d) L_w(n/d)² = [d ∣ n] μ^±(d) L_w(n/d)²` for `d ≤ n`. -/
theorem row_pt {d N y : PTm n} (hdN : Γ ⊢[PRAAx] le (succ d) (succ N)) :
    Γ ⊢[PRAAx] (inst2 (QSP w) d (pairT N y) ≐ inst2 (cvB aPB (bL w)) d (pairT N y)) ⋏
      (inst2 (QSN w) d (pairT N y) ≐ inst2 (cvB aNB (bL w)) d (pairT N y)) := by
  rw [inst2_QSP, inst2_QSN]
  simp only [DirichletLeibniz.inst2_cvB, inst2_aP, inst2_aN, inst2_bL]
  have f₁ := fst_pair (Γ := Γ) N y
  have s₁ := snd_pair (Γ := Γ) N y
  have q : Γ ⊢[PRAAx] quo (fstT (pairT N y)) d ≐ quo N d := congrAp2 quoF f₁ (.eqRefl _)
  have cL : Γ ⊢[PRAAx] Lw w (quo (fstT (pairT N y)) d) (sndT (pairT N y)) ≐ Lw w (quo N d) y :=
    congrAp2 (sumF (ellB w)) (congrSucc q) (congrPairT q s₁)
  have cM := congrMu (Γ := Γ) (d := d) (congrSucc f₁)
  have cE : Γ ⊢[PRAAx] eqb (rem (fstT (pairT N y)) d) zero ≐ eqb (rem N d) zero :=
    congrEqb' (congrAp2 remF f₁ (.eqRefl _)) (.eqRefl _)
  -- the right sides, decoded from the convolution body
  have cLy : Γ ⊢[PRAAx] Lw w (quo (fstT (pairT N y)) d) (sndT (pairT N y)) * Lw w (quo (fstT (pairT N y)) d) (sndT (pairT N y)) ≐
      Lw w (quo N d) y * Lw w (quo N d) y := congrMul cL cL
  refine .orE (zero_or_succ d) ?_ ?_
  · have hS : ((d ≐ zero) :: Γ) ⊢[PRAAx] sg d ≐ zero := (congrSg Prf.hyp0).eqTrans sg_zero
    exact .andI ((row_zero hS).eqTrans (congrMul (congrMul (.eqRefl _) cE.wk.eqSymm)
        (congrMul (.eqRefl _) cLy.wk.eqSymm)))
      ((row_zero hS).eqTrans (congrMul (congrMul (.eqRefl _) cE.wk.eqSymm) (congrMul (.eqRefl _) cLy.wk.eqSymm)))
  · have mb := mu_bound (Γ := (d ≐ succ (pred d)) :: Γ) Prf.hyp0 hdN.wk
    exact .andI ((row_alg cL.wk ((Prf.andE₁ cM).wk.eqTrans (Prf.andE₁ mb)) cE.wk).eqTrans
        (congrMul (congrMul (.eqRefl _) cE.wk.eqSymm) (congrMul (.eqRefl _) cLy.wk.eqSymm)))
      ((row_alg cL.wk ((Prf.andE₂ cM).wk.eqTrans (Prf.andE₂ mb)) cE.wk).eqTrans
        (congrMul (congrMul (.eqRefl _) cE.wk.eqSymm) (congrMul (.eqRefl _) cLy.wk.eqSymm)))

/-- A row of `selberg_mobius_p` is the convolution `(μ^± * L_w²)(N)`. -/
theorem row_conv (N y : PTm n) :
    Γ ⊢[PRAAx] (ap2 (sumF (QSP w)) (succ (fstT (pairT N y))) (pairT N y) ≐ conv aPB (bL w) N y) ⋏
      (ap2 (sumF (QSN w)) (succ (fstT (pairT N y))) (pairT N y) ≐ conv aNB (bL w) N y) := by
  have rg := congrSucc (fst_pair (Γ := Γ) N y)
  have hs : Syn.shift (succ N) = succ (Syn.shift N) := by simp [Syn.shift]
  refine .andI ((congrAp2 _ rg (.eqRefl _)).eqTrans (sum_congr_bounded _ _ _ _ _ (.allI ?_)))
    ((congrAp2 _ rg (.eqRefl _)).eqTrans (sum_congr_bounded _ _ _ _ _ (.allI ?_)))
  · rw [hs]; refine .impI ?_; rw [shift_pairT]
    exact Prf.andE₁ (row_pt w (Prf.hyp0 : (lt (var 0) (succ (Syn.shift N)) :: Γ.map Fm.shift) ⊢[PRAAx] _))
  · rw [hs]; refine .impI ?_; rw [shift_pairT]
    exact Prf.andE₂ (row_pt w (Prf.hyp0 : (lt (var 0) (succ (Syn.shift N)) :: Γ.map Fm.shift) ⊢[PRAAx] _))

/-- `(μ⁺ * L_w²)(n) = G_w(n) + (μ⁻ * L_w²)(n)` for every `n`. -/
theorem pt_n (N y : PTm n) :
    Γ ⊢[PRAAx] inst2 (cvF aPB (bL w)) N y ≐ inst2 (GxB w) N y + inst2 (cvF aNB (bL w)) N y := by
  rw [inst2_cvF, inst2_cvF, inst2_GxB]
  refine .orE (zero_or_succ N) ?_ ?_
  · let C : List (Fm PTm n) := (N ≐ zero) :: Γ
    have h0 : C ⊢[PRAAx] N ≐ zero := Prf.hyp0
    have cz : ∀ (a : PTm 2), C ⊢[PRAAx] conv a (bL w) N y ≐ zero := fun a => by
      refine (congrAp2 _ (congrSucc h0) (congrPairT h0 (.eqRefl _))).eqTrans ?_
      refine (sum_succ' _ _ _).eqTrans ((congrAdd (sum_zero _ _) (cv_at _ _ _ _ _)).eqTrans ?_)
      exact (congrAdd (.eqRefl _) (zero_mul_l (zero_mul_l sg_zero _) _)).eqTrans (add_zero _)
    have g0 : C ⊢[PRAAx] Gx w N y ≐ zero := by
      refine (congrGx1 w h0).eqTrans ?_
      have l0 := lam_zero (Γ := C) w y
      have c0 : C ⊢[PRAAx] conv (lamF w) (lamF w) zero y ≐ zero :=
        (sum_succ' _ _ _).eqTrans ((congrAdd (sum_zero _ _) (cv_at _ _ _ _ _)).eqTrans
          ((congrAdd (.eqRefl _) (zero_mul_l (zero_mul_l sg_zero _) _)).eqTrans (add_zero _)))
      exact (congrAdd ((congrMul (.eqRefl _) l0).eqTrans (mul_zero _)) c0).eqTrans (add_zero _)
    ipra_lc natEq (cz aPB) - natEq (cz aNB) - natEq g0
  · let C : List (Fm PTm n) := (N ≐ succ (pred N)) :: Γ
    have hN : C ⊢[PRAAx] fstT (pairT N y) ≐ succ (pred (fstT (pairT N y))) :=
      ConvolutionAssoc.pos_of_eq ((fst_pair _ _).eqTrans Prf.hyp0)
    have sm := selberg_mobius_p (Γ := C) w hN
    have rc := row_conv (Γ := C) w N y
    have gx := congrGx1 (Γ := C) w (y := sndT (pairT N y)) (fst_pair N y)
    have gy := LeanProofs.IPRA.AnalyticNumberTheory.SelbergMobiusP.congrGx (Γ := C) w (e := N) (snd_pair N y)
    ipra_lc -natEq (Prf.andE₁ rc) + natEq sm + natEq (Prf.andE₂ rc) + natEq gx + natEq gy

/-- Selberg's identity summed up to `x` and reversed:
`Σ_{1≤d≤x} μ⁺(d) B(⌊x/d⌋) = A_w(x) + Σ_{1≤d≤x} μ⁻(d) B(⌊x/d⌋)`, `B(m) = Σ_{1≤k≤m} L_w(k, y)²`. -/
theorem symmetry_sum (x y : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (RB aPB (bL w))) (succ x) (pairT x y) ≐
      ap2 (sumF (GxB w)) (succ x) y + ap2 (sumF (RB aNB (bL w))) (succ x) (pairT x y) := by
  have cP := conv_summatory (Γ := Γ) aPB (bL w) x y
  have cN := conv_summatory (Γ := Γ) aNB (bL w) x y
  have s := sum_add2 (Γ := Γ) (GxB w) (cvF aNB (bL w)) (cvF aPB (bL w)) (K := succ x) (x := y) (x' := y) (z := y)
    (.allI (.impI (pt_n w _ _)))
  ipra_lc -natEq cP + natEq s + natEq cN

end Sym

end LeanProofs.IPRA.AnalyticNumberTheory.SymmetrySum

export_ipra AnalyticNumberTheory.SymmetrySum (GxB aNB aPB inst2_aN inst2_aP)
