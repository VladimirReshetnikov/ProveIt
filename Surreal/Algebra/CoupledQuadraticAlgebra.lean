import Surreal.Algebra.QuadraticLineCircle
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# The rank-four algebra of two independent quadratic collisions

The algebra in `trigonometry:sec:coupled` is constructed as the tensor
product of the two native monic quadratic quotients. Its universal property
represents both equations in every commutative target algebra, retaining
nilpotents. Its basis and dimension are independent of the parameters.
The local factors are identified in `CoupledQuadraticSplit.lean` and
`CoupledQuadraticLocal.lean`; angular multiplicities are computed from the
formal coordinate quotients in `CoupledAngularMultiplicity.lean`.
-/

namespace Surreal.FinitePolynomial

open scoped TensorProduct

noncomputable section

variable {R : Type*} [CommRing R]

/-- The algebra presented by two independent relations `X²=a`, `Y²=b`. -/
abbrev coupledQuotient (a b : R) := quadraticQuotient a ⊗[R] quadraticQuotient b

/-- The first coordinate in the two-relation algebra. -/
def coupledX (a b : R) : coupledQuotient a b := quadraticRoot a ⊗ₜ[R] 1

/-- The second coordinate in the two-relation algebra. -/
def coupledY (a b : R) : coupledQuotient a b := 1 ⊗ₜ[R] quadraticRoot b

/-- Maps from this algebra are precisely simultaneous solutions of the two
relations, in every commutative target algebra, even one with nilpotents. -/
def coupledHomEquivRoots (a b : R) (S : Type*) [CommRing S] [Algebra R S] :
    (coupledQuotient a b →ₐ[R] S) ≃
      {x : S // x ^ 2 = algebraMap R S a} × {y : S // y ^ 2 = algebraMap R S b} :=
  (Algebra.TensorProduct.liftEquiv (R := R) (S := R)
    (A := quadraticQuotient a) (B := quadraticQuotient b) (C := S)).symm.trans
      ((Equiv.subtypeUnivEquiv (fun _ => fun _ _ => Commute.all _ _)).trans
        (Equiv.prodCongr (quadraticHomEquivRoots a S) (quadraticHomEquivRoots b S)))

@[simp] theorem coupledHomEquivRoots_fst (a b : R) (S : Type*) [CommRing S]
    [Algebra R S] (f : coupledQuotient a b →ₐ[R] S) :
    (coupledHomEquivRoots a b S f).1.1 = f (coupledX a b) := rfl

@[simp] theorem coupledHomEquivRoots_snd (a b : R) (S : Type*) [CommRing S]
    [Algebra R S] (f : coupledQuotient a b →ₐ[R] S) :
    (coupledHomEquivRoots a b S f).2.1 = f (coupledY a b) := rfl

@[simp] theorem coupledX_sq (a b : R) :
    coupledX a b ^ 2 = algebraMap R (coupledQuotient a b) a :=
  (coupledHomEquivRoots a b (coupledQuotient a b) (AlgHom.id R _)).1.2

@[simp] theorem coupledY_sq (a b : R) :
    coupledY a b ^ 2 = algebraMap R (coupledQuotient a b) b :=
  (coupledHomEquivRoots a b (coupledQuotient a b) (AlgHom.id R _)).2.2

variable [Nontrivial R]

/-- The tensor power basis, with four indices even at a collision. -/
def coupledBasis (a b : R) : Module.Basis (Fin 2 × Fin 2) R (coupledQuotient a b) :=
  (quadraticBasis a).tensorProduct (quadraticBasis b)

/-- The four basis elements are exactly `1`, `X`, `Y` and `XY`. -/
theorem coupledBasis_apply (a b : R) (i j : Fin 2) :
    coupledBasis a b (i, j) = coupledX a b ^ (i : ℕ) * coupledY a b ^ (j : ℕ) := by
  simp only [coupledBasis, Module.Basis.tensorProduct_apply, quadraticBasis_apply,
    coupledX, coupledY, Algebra.TensorProduct.tmul_pow,
    Algebra.TensorProduct.tmul_mul_tmul, one_pow, mul_one, one_mul]

/-- Dimension four holds over every nontrivial commutative base ring,
including when either or both parameters vanish. -/
theorem coupledQuotient_finrank (a b : R) : Module.finrank R (coupledQuotient a b) = 4 := by
  simpa using Module.finrank_eq_card_basis (coupledBasis a b)

/-- Every element has a unique four-coordinate remainder in the displayed basis. -/
theorem existsUnique_coupled_representation (a b : R) (z : coupledQuotient a b) :
    ∃! c : Fin 2 × Fin 2 → R,
      z = ∑ i, c i • (coupledX a b ^ (i.1 : ℕ) * coupledY a b ^ (i.2 : ℕ)) := by
  simp_rw [← coupledBasis_apply]
  refine ⟨(coupledBasis a b).equivFun z, (coupledBasis a b).sum_equivFun z |>.symm, ?_⟩
  intro c hc
  apply (coupledBasis a b).equivFun.symm.injective
  rw [Module.Basis.equivFun_symm_apply, ← hc,
    LinearEquiv.symm_apply_apply]

end
end Surreal.FinitePolynomial
