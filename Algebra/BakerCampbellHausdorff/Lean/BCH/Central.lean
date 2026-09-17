/-
# The central-commutator case of the Baker–Campbell–Hausdorff formula

This file formalizes Theorem 9.2 of the accompanying article
(`docs/combined`, Section 9.1) for real or complex unital Banach algebras:
if `C = [X, Y]` commutes with both `X` and `Y`, then for every scalar `t`

* `e^{tX} Y e^{-tX} = Y + tC`                       (9.2)
* `e^{tX} e^{tY} = exp(t(X + Y) + ½ t² C)`         (9.3)

and in particular

* `e^X e^Y = e^{X + Y + C/2}`,
* `e^{X + Y} = e^X e^Y e^{-C/2}`,
* `e^{X/2} e^Y e^{X/2} = e^{X + Y}`,
* `e^X e^Y e^{-X} e^{-Y} = e^C`.                    (9.4)

## Method

The article proves (9.2) from Campbell's series and (9.3) by a uniqueness
argument for a linear differential equation. The formal proof below uses an
equivalent but shorter device that needs only "a function on `ℝ` with zero
derivative is constant" (`is_const_of_deriv_eq_zero`): for (9.2) the
function `σ ↦ e^{σX} (Y + (s - σ)C) e^{-σX}` has zero derivative, and for
(9.3) the function `s ↦ e^{-sY} e^{-sX} e^{s(X+Y)} e^{s² D}`, where `D + D = C`,
has zero derivative. The scalar parameter of the statements is `t ∈ 𝕂`; the
internal parameter of the two auxiliary functions is real, and the statements
for general `t` follow from the case `t = 1` applied to `tX, tY`, whose
commutator `t²C` is again central.
-/
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Algebra.Lie.OfAssociative
import BCH.Commuting

open NormedSpace

namespace BCH

/-! ### Elementary bracket identities in the ring convention `⁅a, b⁆ = a b - b a` -/

section Bracket

variable {R : Type*} [Ring R]

lemma lie_neg_left' (a b : R) : ⁅-a, b⁆ = -⁅a, b⁆ := by
  simp only [Ring.lie_def, neg_mul, mul_neg, neg_sub, sub_neg_eq_add]; abel

lemma lie_smul_left' {S : Type*} [Monoid S] [DistribMulAction S R] [SMulCommClass S R R]
    [IsScalarTower S R R] (t : S) (a b : R) : ⁅t • a, b⁆ = t • ⁅a, b⁆ := by
  simp only [Ring.lie_def, smul_mul_assoc, mul_smul_comm, smul_sub]

lemma lie_smul_right' {S : Type*} [Monoid S] [DistribMulAction S R] [SMulCommClass S R R]
    [IsScalarTower S R R] (t : S) (a b : R) : ⁅a, t • b⁆ = t • ⁅a, b⁆ := by
  simp only [Ring.lie_def, smul_mul_assoc, mul_smul_comm, smul_sub]

lemma lie_add_left' (a b c : R) : ⁅a + b, c⁆ = ⁅a, c⁆ + ⁅b, c⁆ := by
  simp only [Ring.lie_def, add_mul, mul_add]; abel

lemma lie_self' (a : R) : ⁅a, a⁆ = 0 := by
  simp [Ring.lie_def]

lemma lie_swap' (a b : R) : ⁅b, a⁆ = -⁅a, b⁆ := by
  simp only [Ring.lie_def, neg_sub]

end Bracket

section ExpInverse

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸]

/-- `e^X e^{-X} = 1`. -/
lemma exp_mul_exp_neg (X : 𝔸) : exp X * exp (-X) = 1 := by
  rw [← exp_add_of_commute (Commute.neg_right (Commute.refl X)), add_neg_cancel, exp_zero]

/-- `e^{-X} e^X = 1`. -/
lemma exp_neg_mul_exp (X : 𝔸) : exp (-X) * exp X = 1 := by
  rw [← exp_add_of_commute (Commute.neg_left (Commute.refl X)), neg_add_cancel, exp_zero]

/-- `e^X` as a unit, with inverse `e^{-X}`. -/
noncomputable def expUnit (X : 𝔸) : 𝔸ˣ :=
  ⟨exp X, exp (-X), exp_mul_exp_neg X, exp_neg_mul_exp X⟩

/-- Conjugation by `e^X` commutes with the exponential: `exp(e^X Y e^{-X}) = e^X e^Y e^{-X}`. -/
lemma exp_exp_conj (X Y : 𝔸) : exp (exp X * Y * exp (-X)) = exp X * exp Y * exp (-X) :=
  exp_units_conj (expUnit X) Y

end ExpInverse

section RealParameter

/-! ### Auxiliary lemmas with a real parameter

These lemmas assume an `ℝ`- and a `ℚ`-normed-algebra structure on `𝔸`; in the
main theorems they are obtained by restriction of scalars from `𝕂`. -/

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormedAlgebra ℚ 𝔸]
  [CompleteSpace 𝔸]

/-- Campbell's identity when `[X, Y]` commutes with `X`, real parameter:
`e^{sX} Y e^{-sX} = Y + s [X, Y]`. -/
lemma exp_smul_mul_mul_exp_smul_neg (X Y : 𝔸) (hX : Commute X ⁅X, Y⁆) (s : ℝ) :
    exp (s • X) * Y * exp (s • (-X)) = Y + s • ⁅X, Y⁆ := by
  set C := ⁅X, Y⁆ with hC
  let v : ℝ → 𝔸 := fun σ => exp (σ • X) * (Y + (s - σ) • C) * exp (σ • (-X))
  have hderiv : ∀ σ : ℝ, HasDerivAt v 0 σ := by
    intro σ
    set E := exp (σ • X) with hE
    set E' := exp (σ • (-X)) with hE'
    set P := Y + (s - σ) • C with hP
    have h1 : HasDerivAt (fun σ : ℝ => exp (σ • X)) (X * E) σ :=
      hasDerivAt_exp_smul_const' X σ
    have h2 : HasDerivAt (fun σ : ℝ => Y + (s - σ) • C) ((-1 : ℝ) • C) σ := by
      have := (((hasDerivAt_id σ).const_sub s).smul_const C).const_add Y
      simpa using this
    have h3 : HasDerivAt (fun σ : ℝ => exp (σ • (-X))) (E' * (-X)) σ :=
      hasDerivAt_exp_smul_const (-X) σ
    have h := (h1.mul h2).mul h3
    -- commutation facts, in right-associated form for rewriting
    have hXE : ∀ z, X * (E * z) = E * (X * z) := fun z => by
      rw [← mul_assoc, (((Commute.refl X).smul_right σ).exp_right).eq, mul_assoc]
    have hE'X : E' * X = X * E' :=
      ((((Commute.refl X).neg_right).smul_right σ).exp_right).eq.symm
    have hXC : X * C = C * X := hX
    have key : X * P - P * X - C = 0 := by
      have hXY : X * Y - Y * X = C := by rw [hC, Ring.lie_def]
      rw [hP, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, hXC, ← hXY]
      abel
    have hD : (X * E * P + E * ((-1 : ℝ) • C)) * E' + E * P * (E' * (-X)) = 0 := by
      calc (X * E * P + E * ((-1 : ℝ) • C)) * E' + E * P * (E' * (-X))
          = E * (X * P - P * X - C) * E' := by
            simp only [neg_one_smul, mul_neg, neg_mul, add_mul, mul_sub, sub_mul, mul_assoc,
              hXE, hE'X]
            abel
        _ = 0 := by rw [key, mul_zero, zero_mul]
    refine h.congr_deriv ?_
    simpa only [Pi.mul_apply] using hD
  have hconst : v s = v 0 :=
    is_const_of_deriv_eq_zero (fun σ => (hderiv σ).differentiableAt)
      (fun σ => (hderiv σ).deriv) s 0
  simpa [v] using hconst

/-- Multiplicative form: `e^{sX} Y = (Y + s[X,Y]) e^{sX}`. -/
lemma exp_smul_mul_eq (X Y : 𝔸) (hX : Commute X ⁅X, Y⁆) (s : ℝ) :
    exp (s • X) * Y = (Y + s • ⁅X, Y⁆) * exp (s • X) := by
  have h := exp_smul_mul_mul_exp_smul_neg X Y hX s
  have hinv : exp (s • (-X)) * exp (s • X) = 1 := by
    rw [smul_neg]; exact exp_neg_mul_exp _
  calc exp (s • X) * Y = exp (s • X) * Y * (exp (s • (-X)) * exp (s • X)) := by
        rw [hinv, mul_one]
    _ = (exp (s • X) * Y * exp (s • (-X))) * exp (s • X) := by
        simp only [mul_assoc]
    _ = (Y + s • ⁅X, Y⁆) * exp (s • X) := by rw [h]

/-- The central-commutator identity with a real parameter, in the form
`e^{-sY} e^{-sX} e^{s(X+Y)} e^{s² D} = 1`, where `D + D = [X, Y]`. -/
lemma central_aux (X Y D : 𝔸) (hX : Commute X ⁅X, Y⁆) (hY : Commute Y ⁅X, Y⁆)
    (hD : D + D = ⁅X, Y⁆) (s : ℝ) :
    exp (s • (-Y)) * exp (s • (-X)) * exp (s • (X + Y)) * exp ((s ^ 2) • D) = 1 := by
  set C := ⁅X, Y⁆ with hC
  have hCD : Commute C D := by
    have : Commute (D + D) D := (Commute.refl D).add_left (Commute.refl D)
    rwa [hD] at this
  let u : ℝ → 𝔸 := fun s =>
    exp (s • (-Y)) * exp (s • (-X)) * exp (s • (X + Y))
      * ((fun r : ℝ => exp (r • D)) ∘ fun s : ℝ => s ^ 2) s
  have hderiv : ∀ s : ℝ, HasDerivAt u 0 s := by
    intro s
    set A := exp (s • (-Y)) with hAdef
    set B := exp (s • (-X)) with hBdef
    set E := exp (s • (X + Y)) with hEdef
    set F := exp ((s ^ 2) • D) with hFdef
    have hA : HasDerivAt (fun s : ℝ => exp (s • (-Y))) ((-Y) * A) s :=
      hasDerivAt_exp_smul_const' (-Y) s
    have hB : HasDerivAt (fun s : ℝ => exp (s • (-X))) ((-X) * B) s :=
      hasDerivAt_exp_smul_const' (-X) s
    have hE : HasDerivAt (fun s : ℝ => exp (s • (X + Y))) ((X + Y) * E) s :=
      hasDerivAt_exp_smul_const' (X + Y) s
    have hF : HasDerivAt ((fun r : ℝ => exp (r • D)) ∘ fun s : ℝ => s ^ 2) (s • (F * C)) s := by
      have := (hasDerivAt_exp_smul_const D (s ^ 2)).scomp s (hasDerivAt_pow 2 s)
      refine this.congr_deriv ?_
      rw [← hFdef]
      have h2s : ((2 : ℕ) : ℝ) * s ^ (2 - 1) = s + s := by norm_num; ring
      rw [h2s, add_smul, ← smul_add, ← mul_add, hD]
    have h := ((hA.mul hB).mul hE).mul hF
    -- commutation facts, in right-associated form
    have hXB : ∀ z, X * (B * z) = B * (X * z) := fun z => by
      rw [← mul_assoc, ((((Commute.refl X).neg_right).smul_right s).exp_right).eq, mul_assoc]
    have hYA : ∀ z, A * (Y * z) = Y * (A * z) := fun z => by
      rw [← mul_assoc, ← ((((Commute.refl Y).neg_right).smul_right s).exp_right).eq, mul_assoc]
    have hCA : ∀ z, A * (C * z) = C * (A * z) := fun z => by
      rw [← mul_assoc, ← (((hY.symm.neg_right).smul_right s).exp_right).eq, mul_assoc]
    have hCB : ∀ z, B * (C * z) = C * (B * z) := fun z => by
      rw [← mul_assoc, ← (((hX.symm.neg_right).smul_right s).exp_right).eq, mul_assoc]
    have hCE : ∀ z, E * (C * z) = C * (E * z) := fun z => by
      rw [← mul_assoc, ← (((hX.symm.add_right hY.symm).smul_right s).exp_right).eq, mul_assoc]
    have hCF : F * C = C * F :=
      ((hCD.smul_right (s ^ 2)).exp_right).eq.symm
    -- the conjugation lemma for `-X`: `B Y = (Y - sC) B`
    have hBY : ∀ z, B * (Y * z) = Y * (B * z) - s • (C * (B * z)) := by
      intro z
      have hX' : Commute (-X) ⁅-X, Y⁆ := by
        rw [lie_neg_left']; exact hX.neg_left.neg_right
      have h0 := exp_smul_mul_eq (-X) Y hX' s
      rw [lie_neg_left' X Y, show s • -⁅X, Y⁆ = -(s • ⁅X, Y⁆) from smul_neg s ⁅X, Y⁆,
        ← sub_eq_add_neg, ← hBdef, ← hC] at h0
      rw [← mul_assoc, h0, mul_assoc, sub_mul, smul_mul_assoc]
    have hD0 : (((-Y) * A * B + A * ((-X) * B)) * E + A * B * ((X + Y) * E)) * F
          + A * B * E * (s • (F * C)) = 0 := by
      calc (((-Y) * A * B + A * ((-X) * B)) * E + A * B * ((X + Y) * E)) * F
            + A * B * E * (s • (F * C))
          = -(Y * (A * (B * (E * F)))) + (Y * (A * (B * (E * F))) - s • (C * (A * (B * (E * F)))))
            + s • (C * (A * (B * (E * F)))) := by
            simp only [neg_mul, mul_neg, add_mul, mul_add, mul_assoc, mul_smul_comm,
              smul_mul_assoc, hXB, hBY, hYA, hCA, hCB, hCE, hCF, mul_sub, sub_mul]
            try simp only [add_mul, sub_mul, smul_mul_assoc, mul_assoc]
            abel
        _ = 0 := by abel
    refine h.congr_deriv ?_
    simp only [Pi.mul_apply, Function.comp_apply]
    try rw [← hAdef]
    try rw [← hBdef]
    try rw [← hEdef]
    try rw [← hFdef]
    exact hD0
  have hconst : u s = u 0 :=
    is_const_of_deriv_eq_zero (fun s => (hderiv s).differentiableAt)
      (fun s => (hderiv s).deriv) s 0
  have hu0 : u 0 = 1 := by simp [u]
  simpa [u, hu0] using hconst

end RealParameter

section Main

variable {𝕂 𝔸 : Type*} [RCLike 𝕂] [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸]

/-- **Theorem 9.2, identity (9.2).** If `C = [X, Y]` commutes with `X`, then
`e^{tX} Y e^{-tX} = Y + tC` for every scalar `t`. (Commutation with `Y` is not needed
for this identity.) -/
theorem central_conj {X Y : 𝔸} (hX : Commute X ⁅X, Y⁆) (t : 𝕂) :
    exp (t • X) * Y * exp (-(t • X)) = Y + t • ⁅X, Y⁆ := by
  let +nondep : NormedAlgebra ℝ 𝔸 := .restrictScalars ℝ 𝕂 𝔸
  let +nondep : NormedAlgebra ℚ 𝔸 := .restrictScalars ℚ 𝕂 𝔸
  have hX' : Commute (t • X) ⁅t • X, Y⁆ := by
    rw [lie_smul_left']; exact (hX.smul_left t).smul_right t
  have h := exp_smul_mul_mul_exp_smul_neg (t • X) Y hX' 1
  rw [one_smul, one_smul, one_smul, lie_smul_left'] at h
  exact h

/-- **Theorem 9.2, first identity of (9.4).** If `C = [X, Y]` commutes with `X` and `Y`,
then `e^X e^Y = e^{X + Y + C/2}`. -/
theorem exp_mul_exp_of_central {X Y : 𝔸} (hX : Commute X ⁅X, Y⁆) (hY : Commute Y ⁅X, Y⁆) :
    exp X * exp Y = exp (X + Y + (1 / 2 : 𝕂) • ⁅X, Y⁆) := by
  let +nondep : NormedAlgebra ℝ 𝔸 := .restrictScalars ℝ 𝕂 𝔸
  let +nondep : NormedAlgebra ℚ 𝔸 := .restrictScalars ℚ 𝕂 𝔸
  set D := (1 / 2 : 𝕂) • ⁅X, Y⁆ with hDdef
  have hD : D + D = ⁅X, Y⁆ := by
    rw [hDdef, ← add_smul]; norm_num
  have h := central_aux X Y D hX hY hD 1
  simp only [one_smul, one_pow] at h
  -- `e^{-Y} e^{-X} e^{X+Y} e^{D} = 1`, hence `e^{X+Y} e^{D} = e^X e^Y`
  have h2 : exp (X + Y) * exp D = exp X * exp Y := by
    have e : exp X * exp Y
        = exp X * (exp Y * exp (-Y)) * exp (-X) * exp (X + Y) * exp D := by
      rw [show exp X * (exp Y * exp (-Y)) * exp (-X) * exp (X + Y) * exp D
          = exp X * exp Y * (exp (-Y) * exp (-X) * exp (X + Y) * exp D)
          by simp only [mul_assoc], h, mul_one]
    rw [exp_mul_exp_neg, mul_one, exp_mul_exp_neg, one_mul] at e
    exact e.symm
  have hcomm : Commute (X + Y) D := (hX.add_left hY).smul_right _
  rw [← h2, ← exp_add_of_commute hcomm]

/-- **Theorem 9.2, identity (9.3).** If `C = [X, Y]` commutes with `X` and `Y`, then
`e^{tX} e^{tY} = exp(t(X + Y) + ½ t² C)` for every scalar `t`. -/
theorem central_exp_mul_exp {X Y : 𝔸} (hX : Commute X ⁅X, Y⁆) (hY : Commute Y ⁅X, Y⁆)
    (t : 𝕂) :
    exp (t • X) * exp (t • Y) = exp (t • (X + Y) + (t ^ 2 / 2) • ⁅X, Y⁆) := by
  have hC' : ⁅t • X, t • Y⁆ = (t ^ 2) • ⁅X, Y⁆ := by
    rw [lie_smul_left', lie_smul_right', smul_smul, sq]
  have hX' : Commute (t • X) ⁅t • X, t • Y⁆ := by
    rw [hC']; exact (hX.smul_left t).smul_right _
  have hY' : Commute (t • Y) ⁅t • X, t • Y⁆ := by
    rw [hC']; exact (hY.smul_left t).smul_right _
  have hhalf : (1 / 2 : 𝕂) * t ^ 2 = t ^ 2 / 2 := by ring
  rw [exp_mul_exp_of_central (𝕂 := 𝕂) hX' hY', hC', smul_smul, smul_add, hhalf]

/-- **Theorem 9.2, second identity of (9.4).** `e^{X + Y} = e^X e^Y e^{-C/2}`. -/
theorem exp_add_eq_of_central {X Y : 𝔸} (hX : Commute X ⁅X, Y⁆) (hY : Commute Y ⁅X, Y⁆) :
    exp (X + Y) = exp X * exp Y * exp (-((1 / 2 : 𝕂) • ⁅X, Y⁆)) := by
  let +nondep : NormedAlgebra ℚ 𝔸 := .restrictScalars ℚ 𝕂 𝔸
  have hc : Commute (X + Y + (1 / 2 : 𝕂) • ⁅X, Y⁆) (-((1 / 2 : 𝕂) • ⁅X, Y⁆)) :=
    (((hX.add_left hY).smul_right _).add_left
      (((Commute.refl ⁅X, Y⁆).smul_left _).smul_right _)).neg_right
  rw [exp_mul_exp_of_central (𝕂 := 𝕂) hX hY, ← exp_add_of_commute hc, add_neg_cancel_right]

/-- **Theorem 9.2, third identity of (9.4).** `e^{X/2} e^Y e^{X/2} = e^{X + Y}`. -/
theorem exp_half_mul_exp_mul_exp_half {X Y : 𝔸} (hX : Commute X ⁅X, Y⁆)
    (hY : Commute Y ⁅X, Y⁆) :
    exp ((1 / 2 : 𝕂) • X) * exp Y * exp ((1 / 2 : 𝕂) • X) = exp (X + Y) := by
  set C := ⁅X, Y⁆ with hC
  -- first product: `e^{X/2} e^Y = e^{X/2 + Y + C/4}`
  have h1 : exp ((1 / 2 : 𝕂) • X) * exp Y
      = exp ((1 / 2 : 𝕂) • X + Y + (1 / 2 : 𝕂) • ((1 / 2 : 𝕂) • C)) := by
    have hX1 : Commute ((1 / 2 : 𝕂) • X) ⁅(1 / 2 : 𝕂) • X, Y⁆ := by
      rw [lie_smul_left']; exact (hX.smul_left _).smul_right _
    have hY1 : Commute Y ⁅(1 / 2 : 𝕂) • X, Y⁆ := by
      rw [lie_smul_left']; exact hY.smul_right _
    rw [exp_mul_exp_of_central (𝕂 := 𝕂) hX1 hY1, lie_smul_left']
  -- second product with `e^{X/2}`: the commutator `[X/2 + Y + C/4, X/2] = -C/2`
  set W := (1 / 2 : 𝕂) • X + Y + (1 / 2 : 𝕂) • ((1 / 2 : 𝕂) • C) with hW
  have hCX : ⁅C, X⁆ = 0 := by
    rw [Ring.lie_def, sub_eq_zero]; exact hX.symm
  have hYX : ⁅Y, X⁆ = -C := by rw [lie_swap']
  have hWX : ⁅W, (1 / 2 : 𝕂) • X⁆ = -((1 / 2 : 𝕂) • C) := by
    rw [hW, lie_smul_right', lie_add_left', lie_add_left', lie_smul_left', lie_self', smul_zero,
      zero_add, lie_smul_left', lie_smul_left', hCX, smul_zero, smul_zero, add_zero, hYX,
      smul_neg]
  have hW1 : Commute W ⁅W, (1 / 2 : 𝕂) • X⁆ := by
    rw [hWX, hW]
    exact ((((hX.smul_left _).add_left hY).add_left
      (((Commute.refl C).smul_left _).smul_left _)).smul_right _).neg_right
  have hW2 : Commute ((1 / 2 : 𝕂) • X) ⁅W, (1 / 2 : 𝕂) • X⁆ := by
    rw [hWX]
    exact ((hX.smul_left _).smul_right _).neg_right
  rw [h1, exp_mul_exp_of_central (𝕂 := 𝕂) hW1 hW2, hWX, hW]
  congr 1
  have e1 : (1 / 2 : 𝕂) • X + (1 / 2 : 𝕂) • X = X := by
    rw [← add_smul]; norm_num
  rw [smul_neg]
  calc (1 / 2 : 𝕂) • X + Y + (1 / 2 : 𝕂) • ((1 / 2 : 𝕂) • C) + (1 / 2 : 𝕂) • X
        + -((1 / 2 : 𝕂) • ((1 / 2 : 𝕂) • C))
      = ((1 / 2 : 𝕂) • X + (1 / 2 : 𝕂) • X) + Y := by abel
    _ = X + Y := by rw [e1]

end Main

section GroupCommutator

variable (𝕂 : Type*) {𝔸 : Type*} [RCLike 𝕂] [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸]
  [CompleteSpace 𝔸]

include 𝕂

/-- **Theorem 9.2, fourth identity of (9.4).** The group commutator:
`e^X e^Y e^{-X} e^{-Y} = e^{[X, Y]}`. The scalar field is an explicit argument because it
does not occur in the statement. -/
theorem exp_group_commutator {X Y : 𝔸} (hX : Commute X ⁅X, Y⁆) (hY : Commute Y ⁅X, Y⁆) :
    exp X * exp Y * exp (-X) * exp (-Y) = exp ⁅X, Y⁆ := by
  let +nondep : NormedAlgebra ℚ 𝔸 := .restrictScalars ℚ 𝕂 𝔸
  -- `e^X e^Y e^{-X} = exp(e^X Y e^{-X}) = e^{Y + C}` by (9.2) with `t = 1`
  have h := central_conj (𝕂 := 𝕂) hX (1 : 𝕂)
  simp only [one_smul] at h
  have h' : exp X * exp Y * exp (-X) = exp (Y + ⁅X, Y⁆) := by
    rw [← exp_exp_conj, h]
  have hc : Commute (Y + ⁅X, Y⁆) (-Y) := ((Commute.refl Y).add_left hY.symm).neg_right
  rw [h', ← exp_add_of_commute hc, show Y + ⁅X, Y⁆ + -Y = ⁅X, Y⁆ by abel]

end GroupCommutator

end BCH
