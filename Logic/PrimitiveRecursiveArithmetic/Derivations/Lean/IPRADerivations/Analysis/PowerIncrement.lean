import IPRADerivations.Algebra.PowerDifference

/-!
# The second-order increment of a power

Packets: `analysis/stirling_ipra` (`stirling_ipra.tex`, `eq:powerr`) and `analysis/taylor_cauchy_ipra`
(`report.tex`, `eq:power2` and the polynomial-weight estimate `eq:weight2`):
for `m ≥ 1`, `x^m − y^m − m y^{m−1} (x − y) = (x − y)² ∑_{ℓ ≤ m−2} (ℓ + 1) x^{m−2−ℓ} y^ℓ`, and for
`0 ≤ a ≤ b ≤ 1`, `0 ≤ b^m − a^m − m a^{m−1} (b − a) ≤ (m(m − 1)/2) (b − a)²`.

With `m = i + 1` and `kd x y i = ∑_{ℓ<i} (ℓ + 1) x^{i−1−ℓ} y^ℓ`, defined by the recursion
`kd (i + 1) = x · kd i + (i + 1) y^i`:

* `power_second` (`eq:power2`): `x^{i+1} + (i+1) y^i y + 2xy · kd = y^{i+1} + (i+1) y^i x + (x² + y²) · kd`,
  the identity with `(x − y)²` expanded, for arbitrary `x`, `y` (no ordering is needed);
* `gd_kd`: `∑_{r ≤ i} x^{i−r} y^r + y · kd = (i + 1) y^i + x · kd`, the first-order sum `gd` of
  `Algebra/PowerDifference` in terms of `kd`;
* `kd_le`: for `x, y ≤ R`, `2R · kd x y i ≤ i (i + 1) R^i`, i.e. `kd ≤ (m(m − 1)/2) R^{m−2}`;
* `power_inc`: `(a + h)^{i+1} = a^{i+1} + (i + 1) a^i h + h² · kd (a + h) a i`;
* `power_inc_lower`, `power_inc_upper` (`eq:powerr`, on the scale `R`): for `a + h ≤ R`,
  `a^{i+1} + (i+1) a^i h ≤ (a + h)^{i+1}` and
  `2R (a + h)^{i+1} ≤ 2R (a^{i+1} + (i+1) a^i h) + i (i + 1) R^i h²`.

The first-order statements (`eq:powerdiff`, `|b^k − a^k| ≤ k |b − a|`) are `Algebra/PowerDifference`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.PowerIncrement

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.Algebra.PowerDifference (gd gd_zero gd_succ)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The second-order coefficient sum -/

/-- Step of `kd`: variables `0 = i`, `1 = kd i`, `2 = ⟨x, y⟩`. -/
abbrev kdStep : PTm 3 := fstT (var 2) * var 1 + succ (var 0) * pw (sndT (var 2)) (var 0)
abbrev kdF : PR 2 := rec2 zero kdStep

/-- `kd x y i = ∑_{ℓ<i} (ℓ + 1) x^(i−1−ℓ) y^ℓ`. -/
abbrev kd (x y i : PTm n) : PTm n := ap2 kdF i (pairT x y)

theorem kd_zero (x y : PTm n) : Γ ⊢[PRAAx] kd x y zero ≐ zero := by
  have h := rec2_zero (Γ := Γ) zero kdStep (pairT x y)
  simpa using h

theorem kd_succ (x y i : PTm n) : Γ ⊢[PRAAx] kd x y (succ i) ≐ x * kd x y i + succ i * pw y i := by
  have h := rec2_succ (Γ := Γ) zero kdStep i (pairT x y)
  have e : Syn.subst ![i, ap2 kdF i (pairT x y), pairT x y] kdStep =
      fstT (pairT x y) * kd x y i + succ i * pw (sndT (pairT x y)) i := by
    simp [ConciseIPRA.PTm.subst_succ]
  rw [e] at h
  exact h.eqTrans (congrAdd (congrMul (fst_pair _ _) (.eqRefl _))
    (congrMul (.eqRefl _) (congrAp2 powF (.eqRefl _) (snd_pair _ _))))

/-! ## The identity -/

/-- The ring form of the induction step of `power_second`. -/
theorem inc_ring {R : Type*} [CommRing R] (x y X1 X2 Y0 Y1 Y2 K0 K1 i : R)
    (sX : X2 = X1 * x) (sY2 : Y2 = Y1 * y) (sY1 : Y1 = Y0 * y) (sK : K1 = x * K0 + (i + 1) * Y0)
    (ih : X1 + (i + 1) * Y0 * y + 2 * (x * y) * K0 = Y1 + (i + 1) * Y0 * x + (x * x + y * y) * K0) :
    X2 + (i + 1 + 1) * Y1 * y + 2 * (x * y) * K1 = Y2 + (i + 1 + 1) * Y1 * x + (x * x + y * y) * K1 := by
  subst sX sY2 sY1 sK
  linear_combination x * ih

abbrev Second (x y i : PTm n) : Fm PTm n :=
  pw x (succ i) + succ i * pw y i * y + two * (x * y) * kd x y i ≐
    pw y (succ i) + succ i * pw y i * x + (x * x + y * y) * kd x y i

theorem second_base (x y : PTm n) : Γ ⊢[PRAAx] Second x y zero := by
  have e1 := natEq (pw_succ (Γ := Γ) x zero); have e0 := natEq (pw_zero (Γ := Γ) x)
  have f1 := natEq (pw_succ (Γ := Γ) y zero); have f0 := natEq (pw_zero (Γ := Γ) y)
  have k := natEq (kd_zero (Γ := Γ) x y)
  apply deriveNat; ipra_simps
  linear_combination e1 + 𝔞 x * e0 - f1 - 𝔞 x * f0 +
    (2 * (𝔞 x * 𝔞 y) - 𝔞 x * 𝔞 x - 𝔞 y * 𝔞 y) * k

theorem second_step {x y i : PTm n} (ih : Γ ⊢[PRAAx] Second x y i) : Γ ⊢[PRAAx] Second x y (succ i) := by
  have e := natEq ih
  have sX := natEq (pw_succ (Γ := Γ) x (succ i))
  have sY2 := natEq (pw_succ (Γ := Γ) y (succ i)); have sY1 := natEq (pw_succ (Γ := Γ) y i)
  have sK := natEq (kd_succ (Γ := Γ) x y i)
  apply deriveNat; ipra_simps
  have r := inc_ring (𝔞 x) (𝔞 y) (𝔞 (pw x (succ i))) (𝔞 (pw x (succ (succ i)))) (𝔞 (pw y i))
    (𝔞 (pw y (succ i))) (𝔞 (pw y (succ (succ i)))) (𝔞 (kd x y i)) (𝔞 (kd x y (succ i))) (𝔞 i)
    (by linear_combination sX) (by linear_combination sY2) (by linear_combination sY1)
    (by linear_combination sK) (by linear_combination e)
  linear_combination r

/-- Variables: `0 = i` (induction), `1 = x`, `2 = y`. -/
private abbrev secF : Fm PTm 3 := Second (var 1) (var 2) (var 0)

private theorem sec₀ : ([] : List (Fm PTm 3)) ⊢[PRAAx] secF := by
  refine ind _ trivial ?_ ?_
  · simp only [Fm.subst_eq, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul, Syn.subst_var,
      Syn.inst_zero, Syn.inst_one, inst_two, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact second_base _ _
  · simp only [Fm.subst_eq, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul, Syn.subst_var,
      Syn.repl_zero, repl_one, repl_two, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact second_step Prf.hyp0

/-- `eq:power2` with `(x − y)²` expanded:
`x^{i+1} + (i+1) y^i y + 2xy · kd = y^{i+1} + (i+1) y^i x + (x² + y²) · kd`. -/
theorem power_second (x y i : PTm n) : Γ ⊢[PRAAx] Second x y i := by
  have h := inst (Γ := Γ) sec₀ (![i, x, y] : Fin 3 → PTm n)
  simpa using h

/-! ## The first-order sum in terms of the second-order sum -/

/-- The ring form of the induction step of `gd_kd`. -/
theorem gk_ring {R : Type*} [CommRing R] (x y G1 G2 K0 K1 Y0 Y1 i : R)
    (sG : G2 = x * G1 + Y1) (sK : K1 = x * K0 + (i + 1) * Y0) (sY : Y1 = Y0 * y)
    (ih : G1 + y * K0 = (i + 1) * Y0 + x * K0) : G2 + y * K1 = (i + 1 + 1) * Y1 + x * K1 := by
  subst sG sK sY
  linear_combination x * ih

abbrev GdKd (x y i : PTm n) : Fm PTm n :=
  gd x y (succ i) + y * kd x y i ≐ succ i * pw y i + x * kd x y i

theorem gd_kd_base (x y : PTm n) : Γ ⊢[PRAAx] GdKd x y zero := by
  have g1 := natEq (gd_succ (Γ := Γ) x y zero); have g0 := natEq (gd_zero (Γ := Γ) x y)
  have k := natEq (kd_zero (Γ := Γ) x y)
  apply deriveNat; ipra_simps
  linear_combination g1 + 𝔞 x * g0 + (𝔞 y - 𝔞 x) * k

theorem gd_kd_step {x y i : PTm n} (ih : Γ ⊢[PRAAx] GdKd x y i) : Γ ⊢[PRAAx] GdKd x y (succ i) := by
  have e := natEq ih
  have sG := natEq (gd_succ (Γ := Γ) x y (succ i))
  have sK := natEq (kd_succ (Γ := Γ) x y i)
  have sY := natEq (pw_succ (Γ := Γ) y i)
  apply deriveNat; ipra_simps
  have r := gk_ring (𝔞 x) (𝔞 y) (𝔞 (gd x y (succ i))) (𝔞 (gd x y (succ (succ i)))) (𝔞 (kd x y i))
    (𝔞 (kd x y (succ i))) (𝔞 (pw y i)) (𝔞 (pw y (succ i))) (𝔞 i)
    (by linear_combination sG) (by linear_combination sK) (by linear_combination sY)
    (by linear_combination e)
  linear_combination r

/-- Variables: `0 = i` (induction), `1 = x`, `2 = y`. -/
private abbrev gkF : Fm PTm 3 := GdKd (var 1) (var 2) (var 0)

private theorem gk₀ : ([] : List (Fm PTm 3)) ⊢[PRAAx] gkF := by
  refine ind _ trivial ?_ ?_
  · simp only [Fm.subst_eq, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul, Syn.subst_var,
      Syn.inst_zero, Syn.inst_one, inst_two, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact gd_kd_base _ _
  · simp only [Fm.subst_eq, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul, Syn.subst_var,
      Syn.repl_zero, repl_one, repl_two, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact gd_kd_step Prf.hyp0

/-- `∑_{r ≤ i} x^{i−r} y^r = (i + 1) y^i + (x − y) · kd x y i`, written without subtraction. -/
theorem gd_kd (x y i : PTm n) : Γ ⊢[PRAAx] GdKd x y i := by
  have h := inst (Γ := Γ) gk₀ (![i, x, y] : Fin 3 → PTm n)
  simpa using h

/-! ## The size of the coefficient sum -/

theorem kd_le_base (x y R : PTm n) :
    Γ ⊢[PRAAx] le (two * R * kd x y zero) (zero * succ zero * pw R zero) := by
  refine le_of_eq_add (d := zero) ?_
  have k := natEq (kd_zero (Γ := Γ) x y)
  apply deriveNat; ipra_simps
  linear_combination -2 * 𝔞 R * k

theorem kd_le_step {x y R i : PTm n} (hx : Γ ⊢[PRAAx] le x R) (hy : Γ ⊢[PRAAx] le y R)
    (ih : Γ ⊢[PRAAx] le (two * R * kd x y i) (i * succ i * pw R i)) :
    Γ ⊢[PRAAx] le (two * R * kd x y (succ i)) (succ i * succ (succ i) * pw R (succ i)) := by
  have m := add_le_add₂ (le_mul_mono hx ih) (le_mul_mono (le_refl (two * succ i * R)) (pw_le_pw i hy))
  have s := natEq (pw_succ (Γ := Γ) R i)
  have k := natEq (kd_succ (Γ := Γ) x y i)
  refine le_congr ?_ ?_ m
  · apply deriveNat; ipra_simps
    linear_combination -2 * 𝔞 R * k
  · apply deriveNat; ipra_simps
    linear_combination -(𝔞 i + 1) * (𝔞 i + 1 + 1) * s

/-- Variables: `0 = i` (induction), `1 = x`, `2 = y`, `3 = R`. -/
private abbrev klF : Fm PTm 4 :=
  le (var 1) (var 3) ⟶ (le (var 2) (var 3) ⟶
    le (two * var 3 * kd (var 1) (var 2) (var 0)) (var 0 * succ (var 0) * pw (var 3) (var 0)))

private theorem kl₀ : ([] : List (Fm PTm 4)) ⊢[PRAAx] klF := by
  refine ind _ ⟨le_QF _ _, ⟨le_QF _ _, le_QF _ _⟩⟩ ?_ ?_
  · simp only [Fm.subst_imp, subst_le, Fm.subst_eq, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul,
      Syn.subst_var, Syn.inst_zero, Syn.inst_one, inst_two, inst_three, ConciseIPRA.PTm.subst_zero,
      ConciseIPRA.PTm.subst_succ]
    exact .impI (.impI (kd_le_base _ _ _))
  · simp only [Fm.subst_imp, subst_le, Fm.subst_eq, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul,
      Syn.subst_var, Syn.repl_zero, repl_one, repl_two, repl_three, ConciseIPRA.PTm.subst_zero,
      ConciseIPRA.PTm.subst_succ]
    refine .impI (.impI ?_)
    exact kd_le_step Prf.hyp1 Prf.hyp0 (.impE (.impE Prf.hyp1.wk Prf.hyp1) Prf.hyp0)

/-- For `x, y ≤ R`: `2R ∑_{ℓ<i} (ℓ + 1) x^(i−1−ℓ) y^ℓ ≤ i (i + 1) R^i`. -/
theorem kd_le {x y R : PTm n} (i : PTm n) (hx : Γ ⊢[PRAAx] le x R) (hy : Γ ⊢[PRAAx] le y R) :
    Γ ⊢[PRAAx] le (two * R * kd x y i) (i * succ i * pw R i) := by
  have h := inst (Γ := Γ) kl₀ (![i, x, y, R] : Fin 4 → PTm n)
  simp at h
  exact .impE (.impE h hx) hy

/-! ## The increment form (`eq:powerr`) -/

/-- `(a + h)^{i+1} = a^{i+1} + (i + 1) a^i h + h² · kd (a + h) a i`. -/
theorem power_inc (a h i : PTm n) :
    Γ ⊢[PRAAx] pw (a + h) (succ i) ≐ pw a (succ i) + succ i * pw a i * h + h * h * kd (a + h) a i := by
  have e := natEq (power_second (Γ := Γ) (a + h) a i)
  apply deriveNat; ipra_simps
  linear_combination e

/-- `a^{i+1} + (i + 1) a^i h ≤ (a + h)^{i+1}`. -/
theorem power_inc_lower (a h i : PTm n) :
    Γ ⊢[PRAAx] le (pw a (succ i) + succ i * pw a i * h) (pw (a + h) (succ i)) :=
  le_of_eq_add (d := h * h * kd (a + h) a i) (power_inc a h i)

/-- For `a + h ≤ R`: `2R (a + h)^{i+1} ≤ 2R (a^{i+1} + (i + 1) a^i h) + i (i + 1) R^i h²`. -/
theorem power_inc_upper {a h R : PTm n} (i : PTm n) (hR : Γ ⊢[PRAAx] le (a + h) R) :
    Γ ⊢[PRAAx] le (two * R * pw (a + h) (succ i))
      (two * R * (pw a (succ i) + succ i * pw a i * h) + i * succ i * pw R i * (h * h)) := by
  have ha : Γ ⊢[PRAAx] le a R := le_trans (le_add_right a h) hR
  have k := natEq (eq_add_of_le (kd_le (Γ := Γ) i hR ha))
  have e := natEq (power_inc (Γ := Γ) a h i)
  refine le_of_eq_add (d := h * h * monus (i * succ i * pw R i) (two * R * kd (a + h) a i)) ?_
  apply deriveNat; ipra_simps
  linear_combination 𝔞 h * 𝔞 h * k - 2 * 𝔞 R * e

end LeanProofs.IPRA.Analysis.PowerIncrement
