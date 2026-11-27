import IPRADerivations.AnalyticNumberTheory.BlockDeficit
import IPRADerivations.Foundations.CrossingSearch

/-!
# The sample tests of the block deficit (`pnt_ipra_constructive_2026-11-14`, `con:deficit`)

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`, `contraction.tex`, proof of Lemma `con:deficit`:
"All tests below concern the rational numbers `b_i` and `a/4`." Here every divisor `d` is a sample, with the exact
value `r(⌊x/d⌋)`, and the two tests are primitive recursive Booleans in the block layout (`a = A/D`, `P = ψ(m)`,
`Q = Fm`, `m = ⌊x/d⌋`):

* `hiB` ("`b ≥ a/4`"): `AQ ≤ 4D(P ∸ Q)`; `loB` ("`b ≤ −a/4`"): `AQ ≤ 4D(Q ∸ P)`;
* `hi_at`, `lo_at`: their values; `test_zero`, `test_one`: a test `[a ≤ b] = monus 1 (a ∸ b)` is `0` exactly when
  `b < a` and nonzero exactly when `a ≤ b`;
* `half_of_not_hi`, `half_of_not_lo`: a failed test gives the case hypothesis `2D(P ∸ Q) ≤ AQ` (resp. `Q ∸ P`);
* `mid_of_neither`: both tests failed give `2D|P − Q| ≤ AQ`;
* `cross_gap` ("`r(t_u) − r(t_v) ≥ a/2 − 2σ` … Another application of (con:decline) gives `t_v − t_u ≥ …`"): a low
  sample at `y` and a high sample at `x ≤ y` with `ψ(x) ≤ ψ(y)`, `ψ(x) ≤ 4Fx` give `Ay ≤ 8D(y − x)`, i.e.
  `1 − x/y ≥ a/8`, by the integer form of the decline `yψ(x) − xψ(y) ≤ 4Fx(y − x)`.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.BlockTests

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicChebyshev (wt)
open LeanProofs.IPRA.AnalyticNumberTheory.BlockSums (pzB fzB pz_at fz_at)
open LeanProofs.IPRA.AnalyticNumberTheory.BlockDeficit (AwB DwB aw_at dw_at)
open LeanProofs.IPRA.Foundations.BoundedReflection (ne_of_compl zero_of_compl_ne)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The numeral `4`. -/
abbrev four {m : ℕ} : PTm m := two * two

/-- A body read at `m = ⌊X/d⌋` with the layout `(X, y)`: `0 = d`, `1 = (X, y)`. -/
abbrev atm (h : PTm 2) : PTm 2 := Syn.subst ![quo (fstT (var 1)) (var 0), sndT (var 1)] h

/-- `[AQ ≤ 4D(P ∸ Q)]`. -/
abbrev hiB : PTm 2 :=
  monus one (monus (atm AwB * atm fzB) (four * (atm DwB * monus (atm pzB) (atm fzB))))
/-- `[AQ ≤ 4D(Q ∸ P)]`. -/
abbrev loB : PTm 2 :=
  monus one (monus (atm AwB * atm fzB) (four * (atm DwB * monus (atm fzB) (atm pzB))))

theorem inst2_atm (h : PTm 2) (d X y : PTm n) : inst2 (atm h) d (pairT X y) = inst2 h (quo (fstT (pairT X y)) d) (sndT (pairT X y)) := by
  simp only [inst2, atm, Syn.subst_subst]; congr 1; funext i; fin_cases i <;> simp

theorem atm_at (h : PTm 2) (d X y : PTm n) :
    Γ ⊢[PRAAx] inst2 (atm h) d (pairT X y) ≐ inst2 h (quo X d) y := by
  rw [inst2_atm]; exact congrInst2 h (congrAp2 quoF (fst_pair _ _) (.eqRefl _)) (snd_pair _ _)

/-- The value of `hiB`. -/
theorem hi_at (d X D₁ D₂ A Ds K F : PTm n) :
    Γ ⊢[PRAAx] inst2 hiB d (pairT X (BlockSums.Y D₁ D₂ (pairT A Ds) (pairT K F))) ≐
      monus one (monus (A * (F * quo X d)) (four * (Ds * monus (Psi wt (quo X d) (pairT K F)) (F * quo X d)))) := by
  have a := (atm_at (Γ := Γ) AwB d X (BlockSums.Y D₁ D₂ (pairT A Ds) (pairT K F))).eqTrans (aw_at _ _ _ _ _ _)
  have dd := (atm_at (Γ := Γ) DwB d X (BlockSums.Y D₁ D₂ (pairT A Ds) (pairT K F))).eqTrans (dw_at _ _ _ _ _ _)
  have f := (atm_at (Γ := Γ) fzB d X (BlockSums.Y D₁ D₂ (pairT A Ds) (pairT K F))).eqTrans (fz_at _ _ _ _ _ _)
  have p := (atm_at (Γ := Γ) pzB d X (BlockSums.Y D₁ D₂ (pairT A Ds) (pairT K F))).eqTrans (pz_at _ _ _ _ _ _)
  rw [show inst2 hiB d (pairT X (BlockSums.Y D₁ D₂ (pairT A Ds) (pairT K F))) =
    monus one (monus (inst2 (atm AwB) d (pairT X (BlockSums.Y D₁ D₂ (pairT A Ds) (pairT K F))) *
        inst2 (atm fzB) d (pairT X (BlockSums.Y D₁ D₂ (pairT A Ds) (pairT K F))))
      (four * (inst2 (atm DwB) d (pairT X (BlockSums.Y D₁ D₂ (pairT A Ds) (pairT K F))) *
        monus (inst2 (atm pzB) d (pairT X (BlockSums.Y D₁ D₂ (pairT A Ds) (pairT K F))))
          (inst2 (atm fzB) d (pairT X (BlockSums.Y D₁ D₂ (pairT A Ds) (pairT K F))))))) by
    simp only [inst2, hiB, PTm.subst_monus, PTm.subst_mul]; simp]
  exact congrMonus (.eqRefl _) (congrMonus (congrMul a f) (congrMul (.eqRefl _) (congrMul dd (congrMonus p f))))

/-- The value of `loB`. -/
theorem lo_at (d X D₁ D₂ A Ds K F : PTm n) :
    Γ ⊢[PRAAx] inst2 loB d (pairT X (BlockSums.Y D₁ D₂ (pairT A Ds) (pairT K F))) ≐
      monus one (monus (A * (F * quo X d)) (four * (Ds * monus (F * quo X d) (Psi wt (quo X d) (pairT K F))))) := by
  have a := (atm_at (Γ := Γ) AwB d X (BlockSums.Y D₁ D₂ (pairT A Ds) (pairT K F))).eqTrans (aw_at _ _ _ _ _ _)
  have dd := (atm_at (Γ := Γ) DwB d X (BlockSums.Y D₁ D₂ (pairT A Ds) (pairT K F))).eqTrans (dw_at _ _ _ _ _ _)
  have f := (atm_at (Γ := Γ) fzB d X (BlockSums.Y D₁ D₂ (pairT A Ds) (pairT K F))).eqTrans (fz_at _ _ _ _ _ _)
  have p := (atm_at (Γ := Γ) pzB d X (BlockSums.Y D₁ D₂ (pairT A Ds) (pairT K F))).eqTrans (pz_at _ _ _ _ _ _)
  rw [show inst2 loB d (pairT X (BlockSums.Y D₁ D₂ (pairT A Ds) (pairT K F))) =
    monus one (monus (inst2 (atm AwB) d (pairT X (BlockSums.Y D₁ D₂ (pairT A Ds) (pairT K F))) *
        inst2 (atm fzB) d (pairT X (BlockSums.Y D₁ D₂ (pairT A Ds) (pairT K F))))
      (four * (inst2 (atm DwB) d (pairT X (BlockSums.Y D₁ D₂ (pairT A Ds) (pairT K F))) *
        monus (inst2 (atm fzB) d (pairT X (BlockSums.Y D₁ D₂ (pairT A Ds) (pairT K F))))
          (inst2 (atm pzB) d (pairT X (BlockSums.Y D₁ D₂ (pairT A Ds) (pairT K F))))))) by
    simp only [inst2, loB, PTm.subst_monus, PTm.subst_mul]; simp]
  exact congrMonus (.eqRefl _) (congrMonus (congrMul a f) (congrMul (.eqRefl _) (congrMul dd (congrMonus f p))))

/-- `[a ≤ b] = 0` gives `b < a`. -/
theorem test_zero {a b : PTm n} (h : Γ ⊢[PRAAx] monus one (monus a b) ≐ zero) : Γ ⊢[PRAAx] lt b a := by
  have ne := ne_of_compl h
  refine .orE (lt_or_le b a) Prf.hyp0 ?_
  exact .botE _ (Prf.impE ne.wk Prf.hyp0)

/-- `[a ≤ b] ≠ 0` gives `a ≤ b`. -/
theorem test_one {a b : PTm n} (h : Γ ⊢[PRAAx] neg (monus one (monus a b) ≐ zero)) : Γ ⊢[PRAAx] le a b :=
  zero_of_compl_ne h

/-- A failed high test: `2D(P ∸ Q) ≤ AQ`. -/
theorem half_of_lt {X A : PTm n} (h : Γ ⊢[PRAAx] lt (four * X) A) : Γ ⊢[PRAAx] le (two * X) A := by
  ipra_le sl h + 2 * 𝔞 X + 1

/-- Both tests failed: `2D|P − Q| ≤ AQ`. -/
theorem mid_of_neither {P Q Ds AQ : PTm n} (h1 : Γ ⊢[PRAAx] lt (four * (Ds * monus P Q)) AQ)
    (h2 : Γ ⊢[PRAAx] lt (four * (Ds * monus Q P)) AQ) : Γ ⊢[PRAAx] le (two * (Ds * absd P Q)) AQ := by
  refine .orE (le_total P Q) ?_ ?_
  · have z := natEq (Prf.hyp0 : ((le P Q) :: Γ) ⊢[PRAAx] monus P Q ≐ zero)
    have h2' := h2.wk (ψ := le P Q)
    ipra_le sl h2' + 2 * 𝔞 Ds * 𝔞 (monus Q P) + 1 with 2 * 𝔞 Ds * z
  · have z := natEq (Prf.hyp0 : ((le Q P) :: Γ) ⊢[PRAAx] monus Q P ≐ zero)
    have h1' := h1.wk (ψ := le Q P)
    ipra_le sl h1' + 2 * 𝔞 Ds * 𝔞 (monus P Q) + 1 with 2 * 𝔞 Ds * z

/-- `1 ≤ Fx` from `1 ≤ F`, `1 ≤ x`. -/
theorem one_le_mul {F x : PTm n} (hF : Γ ⊢[PRAAx] le one F) (hx : Γ ⊢[PRAAx] le one x) :
    Γ ⊢[PRAAx] le one (F * x) := by
  have a := natEq (eq_add_of_le hF); have b := natEq (eq_add_of_le hx)
  ipra_le 𝔞 (monus F one) * 𝔞 (monus x one) + 𝔞 (monus F one) + 𝔞 (monus x one) with
    𝔞 x * a + (1 + 𝔞 (monus F one)) * b

/-- A passed high test forces `C ≤ P`: `P = C + (P ∸ C)` (`A, C ≥ 1`). -/
theorem split_hi {P C A Ds : PTm n} (hA : Γ ⊢[PRAAx] le one A) (hC : Γ ⊢[PRAAx] le one C)
    (h : Γ ⊢[PRAAx] le (A * C) (four * (Ds * monus P C))) : Γ ⊢[PRAAx] P ≐ C + monus P C := by
  refine .orE (le_total P C) ?_ (eq_add_of_le Prf.hyp0)
  have z := natEq (Prf.hyp0 : ((le P C) :: Γ) ⊢[PRAAx] monus P C ≐ zero)
  have a := natEq (eq_add_of_le (hA.wk (ψ := le P C)))
  have c := natEq (eq_add_of_le (hC.wk (ψ := le P C)))
  have l : ((le P C) :: Γ) ⊢[PRAAx] lt (four * (Ds * monus P C)) (A * C) := by
    ipra_le 𝔞 (monus A one) * 𝔞 (monus C one) + 𝔞 (monus A one) + 𝔞 (monus C one) with
      𝔞 C * a + (1 + 𝔞 (monus A one)) * c - 4 * 𝔞 Ds * z
  exact le_lt_absurd _ (h.wk (ψ := le P C)) l

/-- A passed low test forces `Q ≤ C`: `C = Q + (C ∸ Q)` (`A, C ≥ 1`). -/
theorem split_lo {Q C A Ds : PTm n} (hA : Γ ⊢[PRAAx] le one A) (hC : Γ ⊢[PRAAx] le one C)
    (h : Γ ⊢[PRAAx] le (A * C) (four * (Ds * monus C Q))) : Γ ⊢[PRAAx] C ≐ Q + monus C Q := by
  refine .orE (le_total C Q) ?_ (eq_add_of_le Prf.hyp0)
  have z := natEq (Prf.hyp0 : ((le C Q) :: Γ) ⊢[PRAAx] monus C Q ≐ zero)
  have a := natEq (eq_add_of_le (hA.wk (ψ := le C Q)))
  have c := natEq (eq_add_of_le (hC.wk (ψ := le C Q)))
  have l : ((le C Q) :: Γ) ⊢[PRAAx] lt (four * (Ds * monus C Q)) (A * C) := by
    ipra_le 𝔞 (monus A one) * 𝔞 (monus C one) + 𝔞 (monus A one) + 𝔞 (monus C one) with
      𝔞 C * a + (1 + 𝔞 (monus A one)) * c - 4 * 𝔞 Ds * z
  exact le_lt_absurd _ (h.wk (ψ := le C Q)) l

/-- The integer decline: `y ψ(x) ≤ x ψ(y) + 4F x (y − x)` for `x ≤ y`, `ψ(x) ≤ ψ(y)`, `ψ(x) ≤ 4Fx`. -/
theorem decline_int {x y P Q F : PTm n} (hxy : Γ ⊢[PRAAx] le x y) (hPQ : Γ ⊢[PRAAx] le P Q)
    (hP : Γ ⊢[PRAAx] le P (four * (F * x))) :
    Γ ⊢[PRAAx] le (y * P) (x * Q + four * (F * x) * monus y x) := by
  have e := natEq (eq_add_of_le hxy)
  have a := HarmonicMertens.le_scale x hPQ
  have b := HarmonicMertens.le_scale (monus y x) hP
  ipra_le sl a + sl b with 𝔞 P * e

/-- A high sample at `x ≤ y` and a low sample at `y`: `A y ≤ 8 D (y − x)`, i.e. `1 − x/y ≥ a/8`. -/
theorem cross_gap {x y P Q F A Ds : PTm n} (hxy : Γ ⊢[PRAAx] le x y) (hPQ : Γ ⊢[PRAAx] le P Q)
    (hP : Γ ⊢[PRAAx] le P (four * (F * x))) (hF : Γ ⊢[PRAAx] le one F) (hx : Γ ⊢[PRAAx] le one x)
    (hA : Γ ⊢[PRAAx] le one A)
    (hhi : Γ ⊢[PRAAx] le (A * (F * x)) (four * (Ds * monus P (F * x))))
    (hlo : Γ ⊢[PRAAx] le (A * (F * y)) (four * (Ds * monus (F * y) Q))) :
    Γ ⊢[PRAAx] le (A * y) (num 8 * (Ds * monus y x)) := by
  have dc := decline_int hxy hPQ hP
  have hFx := one_le_mul hF hx
  have hFy := one_le_mul hF (le_trans hx hxy)
  have eP := natEq (split_hi hA hFx hhi)
  have eQ := natEq (split_lo hA hFy hlo)
  refine LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep.cancel_pos (c := two * (F * x))
    (by ipra_le sl hFx + 𝔞 F * 𝔞 x) ?_
  ipra_le 𝔞 y * sl hhi + 𝔞 x * sl hlo + 4 * 𝔞 Ds * sl dc with 4 * 𝔞 Ds * 𝔞 y * eP + 4 * 𝔞 Ds * 𝔞 x * eQ

end LeanProofs.IPRA.AnalyticNumberTheory.BlockTests
