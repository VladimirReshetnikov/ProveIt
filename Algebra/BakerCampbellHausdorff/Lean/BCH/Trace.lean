/-
# The trace of the BCH logarithm (Proposition 7.5)

Proposition 7.5 of the accompanying article (`docs/combined`) states that
`tr Z(X, Y) = tr X + tr Y`, formally degree by degree and for matrices whenever
the homogeneous series converges. The mechanism is that every `Zₙ` with `n ≥ 2`
is a Lie polynomial (Theorem 3.6), hence by the Dynkin–Specht–Wever identity
(Lemma 3.4) a linear combination of right-nested brackets of length `≥ 2`,
each of which is a commutator, and commutators have trace zero.

The formalization is stated for an arbitrary *tracial* linear functional `τ`
(`τ (a * b) = τ (b * a)`) on an arbitrary algebra:

* `tracial_bchHom`: `τ (Zₙ(X, Y)) = 0` for `n ≥ 2` (this covers the formal
  series, taking the free algebra itself);
* `tracial_tsum_bchHom`: for a continuous tracial functional on a Banach
  algebra, `τ (∑ₙ Zₙ(X, Y)) = τ X + τ Y` whenever the series is summable;
* `trace_tsum_bchHom`: the matrix case, `tr (∑ₙ Zₙ(X, Y)) = tr X + tr Y`,
  with the `ℓ∞`-operator norm on matrices (any norm gives the same notion of
  convergence, all norms on a finite-dimensional space being equivalent).
-/
import BCH.Formal.Dynkin
import BCH.LowDegree
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Topology.UniformSpace.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace

open Finset

attribute [local instance 100] LieRing.ofAssociativeRing

namespace BCH

section Formal

variable {𝕂 : Type*} [RCLike 𝕂] {𝔸 : Type*} [Ring 𝔸] [Algebra 𝕂 𝔸]

/-- The evaluation homomorphism `𝕂⟨X, Y⟩ → 𝔸` sending the generators to `X` and `Y`. -/
noncomputable def evalHom (X Y : 𝔸) : FreeTwo 𝕂 →ₐ[𝕂] 𝔸 :=
  MonoidAlgebra.lift 𝕂 𝔸 (FreeMonoid (Fin 2)) (FreeMonoid.lift ![X, Y])

lemma evalHom_genX (X Y : 𝔸) : evalHom X Y (genX 𝕂) = X := by
  rw [genX, evalHom, MonoidAlgebra.lift_single, one_smul, FreeMonoid.lift_eval_of]
  rfl

lemma evalHom_genY (X Y : 𝔸) : evalHom X Y (genY 𝕂) = Y := by
  rw [genY, evalHom, MonoidAlgebra.lift_single, one_smul, FreeMonoid.lift_eval_of]
  rfl

/-- `Zₙ(X, Y)` is the evaluation of the formal `Zₙ`. -/
lemma bchHom_eq_evalHom (X Y : 𝔸) (n : ℕ) :
    bchHom 𝕂 X Y n = evalHom X Y (bchHom 𝕂 (genX 𝕂) (genY 𝕂) n) := by
  rw [map_bchHom, evalHom_genX, evalHom_genY]

/-- The evaluated right-nested bracket of a list is the evaluation of the formal one. -/
lemma evalHom_rbList (X Y : 𝔸) : ∀ l : List (Fin 2),
    evalHom X Y (rbList 𝕂 l) = rbEval ![X, Y] l
  | [] => by simp [rbList, rbEval]
  | [i] => by
    simp only [rbList, rbEval, gen, evalHom, MonoidAlgebra.lift_single, one_smul,
      FreeMonoid.lift_eval_of]
  | i :: j :: rest => by
    have ih := evalHom_rbList X Y (j :: rest)
    simp only [rbList, rbEval]
    rw [Ring.lie_def, map_sub, map_mul, map_mul, ih, Ring.lie_def]
    have hg : evalHom X Y (gen 𝕂 i) = ![X, Y] i := by
      simp only [gen, evalHom, MonoidAlgebra.lift_single, one_smul, FreeMonoid.lift_eval_of]
    rw [hg]

/-- The evaluated right-nested bracket of a word. -/
lemma evalHom_rb (X Y : 𝔸) (w : FreeMonoid (Fin 2)) :
    evalHom X Y (rb 𝕂 w) = rbEval ![X, Y] (FreeMonoid.toList w) :=
  evalHom_rbList X Y _

/-- A tracial linear functional kills the evaluation of every right-nested bracket of a word
of length `≥ 2`. -/
lemma tracial_rb {τ : 𝔸 →ₗ[𝕂] 𝕂} (hτ : ∀ a b : 𝔸, τ (a * b) = τ (b * a))
    (φ : FreeTwo 𝕂 →ₐ[𝕂] 𝔸) {w : FreeMonoid (Fin 2)} (hw : 2 ≤ FreeMonoid.length w) :
    τ (φ (rb 𝕂 w)) = 0 := by
  obtain ⟨i, w', rfl⟩ : ∃ i w', w = FreeMonoid.of i * w' := by
    induction w using FreeMonoid.inductionOn' with
    | one => rw [FreeMonoid.length_one] at hw; omega
    | mul_of i w _ => exact ⟨i, w, rfl⟩
  have hw' : w' ≠ 1 := by
    rintro rfl
    rw [mul_one, FreeMonoid.length_of] at hw
    omega
  rw [rb_of_mul 𝕂 i hw', Ring.lie_def, map_sub, map_mul, map_mul, map_sub, hτ, sub_self]

/-- A tracial linear functional kills the evaluation of every homogeneous Lie polynomial of
degree `≥ 2` (Dynkin–Specht–Wever). -/
theorem tracial_eval_of_mem_lieGen {τ : 𝔸 →ₗ[𝕂] 𝕂} (hτ : ∀ a b : 𝔸, τ (a * b) = τ (b * a))
    (φ : FreeTwo 𝕂 →ₐ[𝕂] 𝔸) {n : ℕ} (hn : 2 ≤ n) {P : FreeTwo 𝕂} (hP : P ∈ lieGen 𝕂)
    (hhom : IsHomogeneous n P) : τ (φ P) = 0 := by
  have h := R_of_mem_lieGen hP hhom
  have hn0 : (n : 𝕂) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hR : τ (φ (R P)) = 0 := by
    rw [R_apply, Finsupp.sum, map_sum, map_sum]
    refine Finset.sum_eq_zero fun w hw => ?_
    rw [map_smul, map_smul, tracial_rb hτ φ (by rw [hhom w hw]; exact hn), smul_zero]
  rw [h, map_smul, map_smul, smul_eq_mul] at hR
  exact (mul_eq_zero.mp hR).resolve_left hn0

/-- **Proposition 7.5, degreewise**: a tracial linear functional vanishes on `Zₙ(X, Y)` for
`n ≥ 2`. In the free algebra this is the statement for the formal BCH series. -/
theorem tracial_bchHom {τ : 𝔸 →ₗ[𝕂] 𝕂} (hτ : ∀ a b : 𝔸, τ (a * b) = τ (b * a)) (X Y : 𝔸)
    {n : ℕ} (hn : 2 ≤ n) : τ (bchHom 𝕂 X Y n) = 0 := by
  rw [bchHom_eq_evalHom]
  exact tracial_eval_of_mem_lieGen hτ _ hn (bchHom_mem_lieGen n)
    (bchHom_isHomogeneous genX_isHomogeneous genY_isHomogeneous n)

/-- The degree-one component: `τ (Z₁) = τ X + τ Y`. -/
theorem tracial_bchHom_one (τ : 𝔸 →ₗ[𝕂] 𝕂) (X Y : 𝔸) : τ (bchHom 𝕂 X Y 1) = τ X + τ Y := by
  rw [bchHom_one, map_add]

end Formal

section Analytic

variable {𝕂 : Type*} [RCLike 𝕂] {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸]

omit [CompleteSpace 𝔸] in
/-- **Proposition 7.5** for a continuous tracial functional `τ` on a normed algebra:
`τ (∑ₙ Zₙ(X, Y)) = τ X + τ Y` whenever the homogeneous series converges. -/
theorem tracial_tsum_bchHom (τ : 𝔸 →L[𝕂] 𝕂) (hτ : ∀ a b : 𝔸, τ (a * b) = τ (b * a))
    {X Y : 𝔸} (hs : Summable fun n => bchHom 𝕂 X Y n) :
    τ (∑' n, bchHom 𝕂 X Y n) = τ X + τ Y := by
  rw [ContinuousLinearMap.map_tsum τ hs, tsum_eq_sum (s := Finset.range 2)]
  · simp [Finset.sum_range_succ, bchHom_zero, bchHom_one]
  · intro n hn
    rw [Finset.mem_range, not_lt] at hn
    exact tracial_bchHom (τ := (τ : 𝔸 →ₗ[𝕂] 𝕂)) hτ X Y hn

/-- **Proposition 7.5** in the convergence domain `‖X‖ + ‖Y‖ < log 2`. -/
theorem tracial_tsum_bchHom_of_lt (τ : 𝔸 →L[𝕂] 𝕂) (hτ : ∀ a b : 𝔸, τ (a * b) = τ (b * a))
    {X Y : 𝔸} (hs : ‖X‖ + ‖Y‖ < Real.log 2) :
    τ (∑' n, bchHom 𝕂 X Y n) = τ X + τ Y :=
  tracial_tsum_bchHom τ hτ (summable_norm_bchHom hs).of_norm

end Analytic

section Matrix

open scoped Matrix.Norms.Operator

variable {𝕂 : Type*} [RCLike 𝕂] {m : Type*} [Fintype m] [DecidableEq m]

set_option backward.isDefEq.respectTransparency false in
/-- **Proposition 7.5** for matrices: `tr (∑ₙ Zₙ(X, Y)) = tr X + tr Y` whenever the
homogeneous series converges (here in the `ℓ∞`-operator norm). -/
theorem trace_tsum_bchHom {X Y : Matrix m m 𝕂} (hs : Summable fun n => bchHom 𝕂 X Y n) :
    Matrix.trace (∑' n, bchHom 𝕂 X Y n) = Matrix.trace X + Matrix.trace Y :=
  tracial_tsum_bchHom (LinearMap.toContinuousLinearMap (Matrix.traceLinearMap m 𝕂 𝕂))
    (fun a b => Matrix.trace_mul_comm a b) hs

set_option backward.isDefEq.respectTransparency false in
/-- **Proposition 7.5** for matrices with `‖X‖ + ‖Y‖ < log 2`. -/
theorem trace_tsum_bchHom_of_lt {X Y : Matrix m m 𝕂} (hs : ‖X‖ + ‖Y‖ < Real.log 2) :
    Matrix.trace (∑' n, bchHom 𝕂 X Y n) = Matrix.trace X + Matrix.trace Y :=
  trace_tsum_bchHom (summable_norm_bchHom hs).of_norm

end Matrix

end BCH
