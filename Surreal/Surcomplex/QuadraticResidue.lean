import Surreal.Algebra.QuadraticResidueEvaluation
import Surreal.Algebra.QuadraticLocalResidue
import Surreal.Algebra.QuadraticDualNumber
import Surreal.Algebra.QuadraticLineCircle
import Surreal.Surcomplex.QuadraticCollisionPoints

/-!
# The residue pairing on the actual surcomplex collision algebra

Instantiate the polynomial quotient and its residue duality at the actual
surcomplex field. This proves `trigonometry:thm:residuepairing`,
`trigonometry:eq:pairmatrix` and `trigonometry:eq:residuesum`, including
the identification with local Laurent coefficients at simple and double
roots. The preceding algebra is `trigonometry:eq:quadalgebra`.
-/

universe u v

namespace Surreal.Surcomplex.QuadraticCollision

open Polynomial Foundations
open scoped PowerSeries LaurentSeries

noncomputable section

/-- The actual class algebra, implemented by unique degree-below-two representatives. -/
abbrev Algebra (d : Surcomplex.{u}) := FinitePolynomial.quadraticQuotient d

/-- The quadratic quotient represents the original line-circle equations in every
commutative surcomplex algebra, retaining nilpotents at tangency. -/
def lineCircleEquiv (A B D : SignSequence.{u}) (h : 0 < A ^ 2 + B ^ 2)
    (S : Type v) [CommRing S] [_root_.Algebra Surcomplex.{u} S] :
    (Algebra (ofReal ((A ^ 2 + B ^ 2 - D ^ 2) / (A ^ 2 + B ^ 2))) →ₐ[Surcomplex.{u}] S) ≃
      FinitePolynomial.lineCirclePoints (ofReal A : Surcomplex.{u}) (ofReal B) (ofReal D) S := by
  let ρ := SignSequence.sqrt (A ^ 2 + B ^ 2)
  have hρ : (ofReal ρ : Surcomplex.{u}) ≠ 0 :=
    (map_ne_zero ofReal).mpr (SignSequence.sqrt_pos h).ne'
  have hn : (ofReal ρ : Surcomplex.{u}) ^ 2 = ofReal A ^ 2 + ofReal B ^ 2 := by
    rw [← map_pow, SignSequence.sqrt_sq h.le, map_add, map_pow, map_pow]
  have hd : ((ofReal ρ : Surcomplex.{u}) ^ 2 - ofReal D ^ 2) / ofReal ρ ^ 2 =
      ofReal ((A ^ 2 + B ^ 2 - D ^ 2) / (A ^ 2 + B ^ 2)) := by
    simp only [← map_pow, ρ, SignSequence.sqrt_sq h.le, ← map_sub, ← map_div₀]
  exact hd ▸ FinitePolynomial.quadraticLineCircleEquiv
    (ofReal A) (ofReal B) (ofReal D) (ofReal ρ) hρ hn S

/-- The coordinate `W` in the actual quadratic quotient. -/
abbrev root (d : Surcomplex.{u}) : Algebra d := FinitePolynomial.quadraticRoot d

/-- The source's functional extracts the coefficient of `W` in the unique remainder. -/
def residue (d : Surcomplex.{u}) : Algebra d →ₗ[Surcomplex.{u}] Surcomplex.{u} :=
  FinitePolynomial.quadraticResidue d

/-- The actual algebra has dimension two at every parameter, including zero. -/
theorem finrank_algebra (d : Surcomplex.{u}) : Module.finrank Surcomplex.{u} (Algebra d) = 2 :=
  FinitePolynomial.quadraticQuotient_finrank d

/-- The residue pairing identifies the actual quadratic algebra with its full linear dual. -/
def pairingEquiv (d : Surcomplex.{u}) :
    Algebra d ≃ₗ[Surcomplex.{u}] Module.Dual Surcomplex.{u} (Algebra d) :=
  FinitePolynomial.quadraticResiduePairingEquiv d

@[simp] theorem pairingEquiv_apply (d : Surcomplex.{u}) (f g : Algebra d) :
    pairingEquiv d f g = residue d (f * g) := rfl

/-- The Gram matrix is independent of the parameter, without a discriminant denominator. -/
theorem pairing_matrix (d : Surcomplex.{u}) :
    (fun i j : Fin 2 => residue d
      (FinitePolynomial.quadraticBasis d i * FinitePolynomial.quadraticBasis d j)) =
        !![0, 1; 1, 0] :=
  FinitePolynomial.quadraticResidueGram_eq d

/-- Its determinant remains the nonzero unit minus one at the collision. -/
theorem pairing_determinant (d : Surcomplex.{u}) :
    (FinitePolynomial.quadraticResidueGram d).det = -1 :=
  FinitePolynomial.det_quadraticResidueGram d

/-- The collision is the actual dual-number algebra over the surcomplex field. -/
def dualEquiv : Algebra (0 : Surcomplex.{u}) ≃ₐ[Surcomplex.{u}] DualNumber Surcomplex.{u} :=
  FinitePolynomial.quadraticDualEquiv

/-- Evaluation at the unique collision point leaves a nonzero nilpotent direction in the algebra. -/
theorem collision_nilpotent :
    root (0 : Surcomplex.{u}) ≠ 0 ∧ root (0 : Surcomplex.{u}) ^ 2 = 0 :=
  FinitePolynomial.quadratic_collision_nilpotent

/-- The two-point formula applies to every actual surcomplex polynomial. -/
theorem residue_polynomial (d s : Surcomplex.{u}) (hd : d ≠ 0) (hs : s ^ 2 = d)
    (g : Surcomplex.{u}[X]) :
    residue d (AdjoinRoot.mk (FinitePolynomial.quadraticPolynomial d) g) =
      g.eval s / (2 * s) + g.eval (-s) / (-2 * s) :=
  FinitePolynomial.quadraticResidue_mk_eq_residue_sum d s hd hs (by norm_num) g

/-- The separated residue formula is literally the sum of two verified local Laurent residues. -/
theorem residue_eq_local_residue_sum (d s : Surcomplex.{u}) (hd : d ≠ 0) (hs : s ^ 2 = d)
    (g : Surcomplex.{u}[X]) :
    ∃ hs0 : s ≠ 0,
      residue d (AdjoinRoot.mk (FinitePolynomial.quadraticPolynomial d) g) =
        (QuadraticLocalResidue.simpleQuotient s hs0 g).coeff (-1) +
        (QuadraticLocalResidue.simpleQuotient (-s) (neg_ne_zero.mpr hs0) g).coeff (-1) := by
  have hs0 : s ≠ 0 := by
    intro he
    exact hd (by simpa only [he, zero_pow (by decide : 2 ≠ 0)] using hs.symm)
  refine ⟨hs0, ?_⟩
  rw [QuadraticLocalResidue.coeff_simpleQuotient s hs0 g,
    QuadraticLocalResidue.coeff_negativeQuotient s hs0 g]
  exact residue_polynomial d s hd hs g

/-- At the double root, the same functional is the actual formal Laurent residue `g'(0)`. -/
theorem residue_at_collision (g : Surcomplex.{u}[X]) :
    residue 0 (AdjoinRoot.mk (FinitePolynomial.quadraticPolynomial 0) g) =
      g.derivative.eval 0 ∧
    residue 0 (AdjoinRoot.mk (FinitePolynomial.quadraticPolynomial 0) g) =
      (QuadraticLocalResidue.collisionQuotient g).coeff (-1) := by
  have he := FinitePolynomial.quadraticResidue_mk_zero g
  refine ⟨he, ?_⟩
  rw [QuadraticLocalResidue.coeff_collisionQuotient_eq_derivative]
  exact he

/-- The trace of actual multiplication is residue against `2W`. -/
theorem trace_eq_residue (d : Surcomplex.{u}) (g : Algebra d) :
    _root_.Algebra.trace Surcomplex.{u} (Algebra d) g = residue d (2 * root d * g) :=
  FinitePolynomial.quadratic_trace_eq_residue d g

/-- Constant numerators have the two individually infinite residues displayed in the source. -/
theorem constant_local_residue (d : SignSequence.{u}) (hp : 0 < d) :
    ∃ hs : ofReal (SignSequence.sqrt d) ≠ (0 : Surcomplex.{u}),
      (QuadraticLocalResidue.simpleQuotient _ hs (1 : Surcomplex.{u}[X])).coeff (-1) =
        ofReal (constantResidue d) ∧
      (QuadraticLocalResidue.simpleQuotient _ (neg_ne_zero.mpr hs)
        (1 : Surcomplex.{u}[X])).coeff (-1) = -ofReal (constantResidue d) := by
  have hs : ofReal (SignSequence.sqrt d) ≠ (0 : Surcomplex.{u}) :=
    (map_ne_zero ofReal).mpr (SignSequence.sqrt_pos hp).ne'
  refine ⟨hs, ?_, ?_⟩
  · rw [QuadraticLocalResidue.coeff_simpleQuotient, eval_one, constantResidue,
      map_inv₀, map_mul, map_ofNat, one_div]
  · rw [QuadraticLocalResidue.coeff_simpleQuotient, eval_one, constantResidue,
      map_inv₀, map_mul, map_ofNat, mul_neg, div_neg, one_div]

/-- The actual local residues are individually infinite and cancel, at every positive
infinitesimal parameter. -/
theorem infinite_local_residues_cancel (d : SignSequence.{u}) (hp : 0 < d)
    (hi : SignSequence.IsInfinitesimal d) :
    ∃ hs : ofReal (SignSequence.sqrt d) ≠ (0 : Surcomplex.{u}),
      let r := (QuadraticLocalResidue.simpleQuotient _ hs (1 : Surcomplex.{u}[X])).coeff (-1)
      let t := (QuadraticLocalResidue.simpleQuotient _ (neg_ne_zero.mpr hs)
        (1 : Surcomplex.{u}[X])).coeff (-1)
      ¬ IsFinite r ∧ ¬ IsFinite t ∧ r + t = 0 := by
  obtain ⟨hs, hr, ht⟩ := constant_local_residue d hp
  refine ⟨hs, ?_⟩
  dsimp only
  rw [hr, ht]
  exact ⟨(constant_residues_not_finite d hp hi).1,
    (constant_residues_not_finite d hp hi).2, add_neg_cancel _⟩

/-- With numerator `W`, both local residues are one half and their sum is one. -/
theorem linear_local_residues (s : Surcomplex.{u}) (hs : s ≠ 0) :
    (QuadraticLocalResidue.simpleQuotient s hs (X : Surcomplex.{u}[X])).coeff (-1) = 1 / 2 ∧
    (QuadraticLocalResidue.simpleQuotient (-s) (neg_ne_zero.mpr hs)
      (X : Surcomplex.{u}[X])).coeff (-1) = 1 / 2 := by
  rw [QuadraticLocalResidue.coeff_simpleQuotient s hs X,
    QuadraticLocalResidue.coeff_negativeQuotient s hs X,
    eval_X, eval_X]
  exact linear_residues s hs

end
end Surreal.Surcomplex.QuadraticCollision
