import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.Algebra.Group.Subgroup.Lattice
import OAI.Combinatorics.Progressions.Estimates.WeightedDerivationDrop
import OAI.Combinatorics.Progressions.Polynomial.PolynomialDerivativeSeparation
import OAI.Combinatorics.Progressions.Polynomial.PolynomialPrimitive
import OAI.Combinatorics.Progressions.Polynomial.WeightedPolynomialPotential

namespace OAI

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators

variable {σ : Type*}

noncomputable def polynomialExponentialPath (x : σ → ℚ) (P : MvPolynomial σ ℚ) :
    Polynomial (MvPolynomial σ ℚ) :=
  polynomialPrimitive (polynomialTranslationPath x P)

@[simp] theorem polynomialExponentialPath_derivative (x : σ → ℚ)
    (P : MvPolynomial σ ℚ) :
    (polynomialExponentialPath x P).derivative = polynomialTranslationPath x P :=
  polynomialPrimitive_derivative _

@[simp] theorem polynomialExponentialPath_eval_zero (x : σ → ℚ)
    (P : MvPolynomial σ ℚ) : (polynomialExponentialPath x P).eval 0 = 0 :=
  polynomialPrimitive_eval_zero _

theorem polynomialExponentialPath_unique (x : σ → ℚ) (P : MvPolynomial σ ℚ)
    {F : Polynomial (MvPolynomial σ ℚ)}
    (hderiv : F.derivative = polynomialTranslationPath x P) (hzero : F.eval 0 = 0) :
    polynomialExponentialPath x P = F :=
  polynomialPrimitive_unique hderiv hzero

theorem polynomialExponentialPath_potential [Fintype σ] (x : σ → ℚ)
    (V : MvPolynomial σ ℚ) :
    polynomialExponentialPath x (scalarDirectionalDerivative x V) =
      Polynomial.C V - polynomialTranslationPath x V := by
  apply polynomialExponentialPath_unique
  · rw [Polynomial.derivative_sub, Polynomial.derivative_C,
      polynomialTranslationPath_derivative, zero_sub, neg_neg]
  · simp

theorem polynomialExponentialPath_eval_potential [Fintype σ] (x : σ → ℚ)
    (V : MvPolynomial σ ℚ) (t : ℚ) :
    (polynomialExponentialPath x (scalarDirectionalDerivative x V)).eval (C t) =
      V - polynomialTranslate (fun i => -(t * x i)) V := by
  rw [polynomialExponentialPath_potential, Polynomial.eval_sub, Polynomial.eval_C,
    polynomialTranslationPath_eval]

noncomputable def polynomialExponentialCoordinate (x : σ → ℚ)
    (P : MvPolynomial σ ℚ) : MvPolynomial σ ℚ :=
  (polynomialExponentialPath x P).eval 1

theorem polynomialExponentialCoordinate_formula (x : σ → ℚ) (P : MvPolynomial σ ℚ) :
    polynomialExponentialCoordinate x P =
      ∑ n ∈ (polynomialTranslationPath x P).support,
        (((n + 1 : ℕ) : ℚ)⁻¹ • (polynomialTranslationPath x P).coeff n) := by
  classical
  simp only [polynomialExponentialCoordinate, polynomialExponentialPath,
    polynomialPrimitive, Polynomial.sum_def, Polynomial.eval_finsetSum,
    Polynomial.eval_monomial, one_pow, mul_one]

theorem polynomialExponentialCoordinate_potential [Fintype σ] (x : σ → ℚ)
    (V : MvPolynomial σ ℚ) :
    polynomialExponentialCoordinate x (scalarDirectionalDerivative x V) =
      V - polynomialTranslate (-x) V := by
  have h := polynomialExponentialPath_eval_potential x V 1
  have hx : (fun i => -(1 * x i)) = -x := by funext i; simp
  rw [map_one, hx] at h
  exact h

theorem weightedPolynomialPotential_exponentialCoordinate [Fintype σ]
    (w : σ → ℕ) {d : ℕ} (hd : 0 < d) (P : σ → MvPolynomial σ ℚ)
    (hweight : ∀ i, w i ≤ d)
    (hhom : ∀ i, (P i).IsWeightedHomogeneous w (d - w i))
    (hclosed : ∀ i j, pderiv i (P j) = pderiv j (P i)) (x : σ → ℚ) :
    polynomialExponentialCoordinate x (∑ i, x i • P i) =
      weightedPolynomialPotential w d P -
        polynomialTranslate (-x) (weightedPolynomialPotential w d P) := by
  have h := polynomialExponentialCoordinate_potential x (weightedPolynomialPotential w d P)
  simpa only [scalarDirectionalDerivative_apply,
    weightedPolynomialPotential_pderiv w hd P hweight hhom hclosed] using h

end Erdos3

end

section

namespace Erdos3

open MvPolynomial

variable {σ : Type*}

@[simp] theorem polynomialTranslationPath_zero (P : MvPolynomial σ ℚ) :
    polynomialTranslationPath (0 : σ → ℚ) P = Polynomial.C P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

@[simp] theorem polynomialExponentialPath_C (x : σ → ℚ) (c : ℚ) :
    polynomialExponentialPath x (C c) = Polynomial.C (C c) * Polynomial.X := by
  apply polynomialExponentialPath_unique <;> simp

@[simp] theorem polynomialExponentialPath_zero (P : MvPolynomial σ ℚ) :
    polynomialExponentialPath (0 : σ → ℚ) P = Polynomial.C P * Polynomial.X := by
  apply polynomialExponentialPath_unique <;> simp

@[simp] theorem polynomialExponentialCoordinate_C (x : σ → ℚ) (c : ℚ) :
    polynomialExponentialCoordinate x (C c) = C c := by
  simp [polynomialExponentialCoordinate]

@[simp] theorem polynomialExponentialCoordinate_zero (P : MvPolynomial σ ℚ) :
    polynomialExponentialCoordinate (0 : σ → ℚ) P = P := by
  simp [polynomialExponentialCoordinate]

end Erdos3

end

section

namespace Erdos3

open MvPolynomial

variable {σ : Type*}

theorem polynomialTranslationPath_translate_reflection (x : σ → ℚ)
    (P : MvPolynomial σ ℚ) :
    (polynomialTranslationPath x P).map (polynomialTranslate x).toRingHom =
      (polynomialTranslationPath (-x) P).comp (1 - Polynomial.X) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, Polynomial.map_add, Polynomial.add_comp, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, Polynomial.map_mul, Polynomial.mul_comp]
    rw [hp]
    congr 1
    simp only [polynomialTranslationPath_X, Polynomial.map_sub, Polynomial.map_C,
      Polynomial.map_mul, Polynomial.map_X, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      polynomialTranslate_X, polynomialTranslate_C, Polynomial.sub_comp,
      Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp, Pi.neg_apply,
      map_neg, map_add, Polynomial.neg_comp]
    ring

theorem polynomialExponentialPath_translate_reflection (x : σ → ℚ)
    (P : MvPolynomial σ ℚ) :
    (polynomialExponentialPath x P).map (polynomialTranslate x).toRingHom =
      Polynomial.C (polynomialExponentialCoordinate (-x) P) -
        (polynomialExponentialPath (-x) P).comp (1 - Polynomial.X) := by
  apply polynomial_eq_of_derivative_of_eval_zero
  · rw [Polynomial.derivative_map, polynomialExponentialPath_derivative,
      polynomialTranslationPath_translate_reflection, Polynomial.derivative_sub,
      Polynomial.derivative_C, Polynomial.derivative_comp_one_sub_X,
      polynomialExponentialPath_derivative, zero_sub, neg_neg]
  · have hz := Polynomial.eval_map_apply (p := polynomialExponentialPath x P)
        (polynomialTranslate x).toRingHom 0
    simp only [map_zero, polynomialExponentialPath_eval_zero] at hz
    rw [hz]
    simp [polynomialExponentialCoordinate, Polynomial.eval_comp]

theorem polynomialTranslate_exponentialCoordinate (x : σ → ℚ)
    (P : MvPolynomial σ ℚ) :
    polynomialTranslate x (polynomialExponentialCoordinate x P) =
      polynomialExponentialCoordinate (-x) P := by
  have h := congrArg (fun Q : Polynomial (MvPolynomial σ ℚ) => Q.eval 1)
    (polynomialExponentialPath_translate_reflection x P)
  have he := Polynomial.eval_map_apply (p := polynomialExponentialPath x P)
    (polynomialTranslate x).toRingHom 1
  simp only [map_one] at he
  rw [he] at h
  simpa [polynomialExponentialCoordinate, Polynomial.eval_comp] using h

end Erdos3

end

section

namespace Erdos3

open MvPolynomial

variable {σ : Type*}

theorem polynomialTranslate_comp (h k : σ → ℚ) (V : MvPolynomial σ ℚ) :
    polynomialTranslate h (polynomialTranslate k V) = polynomialTranslate (h + k) V := by
  induction V using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp, polynomialTranslate_X, map_add, polynomialTranslate_C,
      Pi.add_apply]
    rw [add_assoc]

@[ext] structure PolynomialTranslationGroup (σ : Type*) where
  base : σ → ℚ
  polynomial : MvPolynomial σ ℚ

namespace PolynomialTranslationGroup

noncomputable instance : Mul (PolynomialTranslationGroup σ) where
  mul a b := ⟨a.base + b.base, polynomialTranslate (-b.base) a.polynomial + b.polynomial⟩

noncomputable instance : One (PolynomialTranslationGroup σ) where
  one := ⟨0, 0⟩

noncomputable instance : Inv (PolynomialTranslationGroup σ) where
  inv a := ⟨-a.base, -polynomialTranslate a.base a.polynomial⟩

@[simp] theorem base_mul (a b : PolynomialTranslationGroup σ) :
    (a * b).base = a.base + b.base := rfl

@[simp] theorem polynomial_mul (a b : PolynomialTranslationGroup σ) :
    (a * b).polynomial = polynomialTranslate (-b.base) a.polynomial + b.polynomial := rfl

@[simp] theorem base_one : (1 : PolynomialTranslationGroup σ).base = 0 := rfl
@[simp] theorem polynomial_one : (1 : PolynomialTranslationGroup σ).polynomial = 0 := rfl
@[simp] theorem base_inv (a : PolynomialTranslationGroup σ) : (a⁻¹).base = -a.base := rfl
@[simp] theorem polynomial_inv (a : PolynomialTranslationGroup σ) :
    (a⁻¹).polynomial = -polynomialTranslate a.base a.polynomial := rfl

noncomputable instance : Group (PolynomialTranslationGroup σ) :=
  Group.ofLeftAxioms
    (by
      intro a b c
      apply PolynomialTranslationGroup.ext
      · exact add_assoc _ _ _
      · simp only [polynomial_mul, base_mul, map_add, polynomialTranslate_comp,
          neg_add_rev, add_assoc])
    (by intro a; apply PolynomialTranslationGroup.ext <;> simp)
    (by
      intro a
      apply PolynomialTranslationGroup.ext
      · simp
      · simp [polynomialTranslate_comp])

noncomputable def potentialElement (V : MvPolynomial σ ℚ) (x : σ → ℚ) :
    PolynomialTranslationGroup σ := ⟨x, V - polynomialTranslate (-x) V⟩

@[simp] theorem potentialElement_base (V : MvPolynomial σ ℚ) (x : σ → ℚ) :
    (potentialElement V x).base = x := rfl

@[simp] theorem potentialElement_polynomial (V : MvPolynomial σ ℚ) (x : σ → ℚ) :
    (potentialElement V x).polynomial = V - polynomialTranslate (-x) V := rfl

@[simp] theorem potentialElement_zero (V : MvPolynomial σ ℚ) :
    potentialElement V 0 = 1 := by
  apply PolynomialTranslationGroup.ext <;> simp

theorem potentialElement_add (V : MvPolynomial σ ℚ) (x z : σ → ℚ) :
    potentialElement V (x + z) = potentialElement V x * potentialElement V z := by
  apply PolynomialTranslationGroup.ext
  · rfl
  · simp only [potentialElement_polynomial, polynomial_mul, potentialElement_base,
      map_sub, polynomialTranslate_comp, neg_add_rev]
    abel

theorem potentialElement_neg (V : MvPolynomial σ ℚ) (x : σ → ℚ) :
    potentialElement V (-x) = (potentialElement V x)⁻¹ := by
  apply PolynomialTranslationGroup.ext
  · rfl
  · simp only [potentialElement_polynomial, polynomial_inv, potentialElement_base,
      map_sub, polynomialTranslate_comp, neg_neg, add_neg_cancel, polynomialTranslate_zero]
    abel

noncomputable def potentialSubgroup (V : MvPolynomial σ ℚ) :
    Subgroup (PolynomialTranslationGroup σ) where
  carrier := {g | g = potentialElement V g.base}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    change a * b = potentialElement V (a * b).base
    rw [base_mul, potentialElement_add, ← ha, ← hb]
  inv_mem' := by
    intro a ha
    change a⁻¹ = potentialElement V a⁻¹.base
    rw [base_inv, potentialElement_neg, ← ha]

theorem mem_potentialSubgroup (V : MvPolynomial σ ℚ) (g : PolynomialTranslationGroup σ) :
    g ∈ potentialSubgroup V ↔ g.polynomial = V - polynomialTranslate (-g.base) V := by
  change (g = potentialElement V g.base) ↔ _
  constructor
  · intro h
    exact congrArg PolynomialTranslationGroup.polynomial h
  · intro h
    exact PolynomialTranslationGroup.ext rfl h

noncomputable def exponentialElement (x : σ → ℚ) (P : MvPolynomial σ ℚ) :
    PolynomialTranslationGroup σ := ⟨x, polynomialExponentialCoordinate x P⟩

theorem exponentialElement_potential [Fintype σ] (x : σ → ℚ) (V : MvPolynomial σ ℚ) :
    exponentialElement x (scalarDirectionalDerivative x V) = potentialElement V x := by
  apply PolynomialTranslationGroup.ext
  · rfl
  · exact polynomialExponentialCoordinate_potential x V

noncomputable def potentialFlow [Fintype σ] (x : σ → ℚ) (V : MvPolynomial σ ℚ)
    (t : ℚ) : PolynomialTranslationGroup σ :=
  ⟨t • x, (polynomialExponentialPath x (scalarDirectionalDerivative x V)).eval (C t)⟩

theorem potentialFlow_eq [Fintype σ] (x : σ → ℚ) (V : MvPolynomial σ ℚ) (t : ℚ) :
    potentialFlow x V t = potentialElement V (t • x) := by
  apply PolynomialTranslationGroup.ext
  · rfl
  · change (polynomialExponentialPath x (scalarDirectionalDerivative x V)).eval (C t) = _
    rw [polynomialExponentialPath_eval_potential, potentialElement_polynomial]
    congr 2

@[simp] theorem potentialFlow_zero [Fintype σ] (x : σ → ℚ) (V : MvPolynomial σ ℚ) :
    potentialFlow x V 0 = 1 := by
  rw [potentialFlow_eq, zero_smul, potentialElement_zero]

theorem potentialFlow_add [Fintype σ] (x : σ → ℚ) (V : MvPolynomial σ ℚ) (t u : ℚ) :
    potentialFlow x V (t + u) = potentialFlow x V t * potentialFlow x V u := by
  simp only [potentialFlow_eq, add_smul, potentialElement_add]

theorem potentialFlow_initial_tangent [Fintype σ] (x : σ → ℚ) (V : MvPolynomial σ ℚ) :
    (polynomialExponentialPath x (scalarDirectionalDerivative x V)).derivative.eval 0 =
      scalarDirectionalDerivative x V := by
  simp

theorem potential_identity_of_mem_closure [Fintype σ] (V : MvPolynomial σ ℚ)
    {S : Set (PolynomialTranslationGroup σ)}
    (hS : ∀ g ∈ S, ∃ x, g = exponentialElement x (scalarDirectionalDerivative x V))
    {g : PolynomialTranslationGroup σ} (hg : g ∈ Subgroup.closure S) :
    g.polynomial = V - polynomialTranslate (-g.base) V := by
  apply (mem_potentialSubgroup V g).mp
  apply ((Subgroup.closure_le _).mpr ?_ : Subgroup.closure S ≤ potentialSubgroup V) hg
  intro a ha
  obtain ⟨x, rfl⟩ := hS a ha
  rw [exponentialElement_potential]
  change potentialElement V x = potentialElement V (potentialElement V x).base
  rfl

end PolynomialTranslationGroup
end Erdos3

end

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators

variable {σ : Type*} [Fintype σ]

structure PolynomialPotentialRelation (σ : Type*) [Fintype σ] where
  space : Submodule ℚ ((σ → ℚ) × MvPolynomial σ ℚ)
  bracket_mem : ∀ x P z Q, (x, P) ∈ space → (z, Q) ∈ space →
    (0, scalarDirectionalDerivative x Q - scalarDirectionalDerivative z P) ∈ space
  pure_constant_zero : ∀ Q, (0, Q) ∈ space → Q.coeff 0 = 0

@[simp] theorem scalarDirectionalDerivative_zero (P : MvPolynomial σ ℚ) :
    scalarDirectionalDerivative (0 : σ → ℚ) P = 0 := by
  simp [scalarDirectionalDerivative_apply]

@[simp] theorem scalarDirectionalDerivative_single [DecidableEq σ] (i : σ)
    (P : MvPolynomial σ ℚ) :
    scalarDirectionalDerivative (Pi.single i 1) P = pderiv i P := by
  simp [scalarDirectionalDerivative_apply, Pi.single_apply]

namespace PolynomialPotentialRelation

variable [DecidableEq σ] (A : PolynomialPotentialRelation σ)
  (P : σ → MvPolynomial σ ℚ)
  (hlift : ∀ i, (Pi.single i 1, P i) ∈ A.space)

include hlift

theorem pure_eq_zero (Q : MvPolynomial σ ℚ) (hQ : (0, Q) ∈ A.space) : Q = 0 := by
  apply polynomial_eq_zero_of_pderiv_closed {Q | (0, Q) ∈ A.space} ?_ ?_ Q hQ
  · intro R hR i
    change (0, pderiv i R) ∈ A.space
    have h := A.bracket_mem (Pi.single i 1) (P i) 0 R (hlift i) hR
    simpa only [scalarDirectionalDerivative_single, scalarDirectionalDerivative_zero,
      sub_zero] using h
  · exact A.pure_constant_zero

theorem compatible_partials (i j : σ) : pderiv i (P j) = pderiv j (P i) := by
  have h := A.bracket_mem (Pi.single i 1) (P i) (Pi.single j 1) (P j) (hlift i) (hlift j)
  simp only [scalarDirectionalDerivative_single] at h
  exact sub_eq_zero.mp (A.pure_eq_zero P hlift _ h)

theorem linear_combination_mem (x : σ → ℚ) : (x, ∑ i, x i • P i) ∈ A.space := by
  have h : (∑ i, x i • (Pi.single i 1, P i)) ∈ A.space :=
    A.space.sum_mem (fun i _ => A.space.smul_mem (x i) (hlift i))
  have heq : (∑ i, x i • (Pi.single i 1, P i)) = (x, ∑ i, x i • P i) := by
    apply Prod.ext
    · ext j
      simp [Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
    · simp [Prod.snd_sum]
  rwa [heq] at h

theorem polynomial_eq_linear_combination (x : σ → ℚ) (Q : MvPolynomial σ ℚ)
    (hQ : (x, Q) ∈ A.space) : Q = ∑ i, x i • P i := by
  have h := A.space.sub_mem hQ (A.linear_combination_mem P hlift x)
  have hpure : (0, Q - ∑ i, x i • P i) ∈ A.space := by simpa using h
  exact sub_eq_zero.mp (A.pure_eq_zero P hlift _ hpure)

theorem weighted_potential_derivative (w : σ → ℕ) {d : ℕ} (hd : 0 < d)
    (hweight : ∀ i, w i ≤ d)
    (hhom : ∀ i, (P i).IsWeightedHomogeneous w (d - w i))
    (x : σ → ℚ) (Q : MvPolynomial σ ℚ) (hQ : (x, Q) ∈ A.space) :
    scalarDirectionalDerivative x (weightedPolynomialPotential w d P) = Q := by
  rw [scalarDirectionalDerivative_apply]
  simp only [weightedPolynomialPotential_pderiv w hd P hweight hhom
    (A.compatible_partials P hlift)]
  exact (A.polynomial_eq_linear_combination P hlift x Q hQ).symm

theorem exists_weighted_potential (w : σ → ℕ) {d : ℕ} (hd : 0 < d)
    (hweight : ∀ i, w i ≤ d)
    (hhom : ∀ i, (P i).IsWeightedHomogeneous w (d - w i)) :
    ∃ V : MvPolynomial σ ℚ, V.IsWeightedHomogeneous w d ∧
      ∀ x Q, (x, Q) ∈ A.space → scalarDirectionalDerivative x V = Q :=
  ⟨weightedPolynomialPotential w d P, weightedPolynomialPotential_homogeneous w d P hweight hhom,
    A.weighted_potential_derivative P hlift w hd hweight hhom⟩

theorem exponential_potential_identity (w : σ → ℕ) {d : ℕ} (hd : 0 < d)
    (hweight : ∀ i, w i ≤ d)
    (hhom : ∀ i, (P i).IsWeightedHomogeneous w (d - w i))
    (x : σ → ℚ) (Q : MvPolynomial σ ℚ) (hQ : (x, Q) ∈ A.space) :
    polynomialExponentialCoordinate x Q = weightedPolynomialPotential w d P -
      polynomialTranslate (-x) (weightedPolynomialPotential w d P) := by
  rw [← A.weighted_potential_derivative P hlift w hd hweight hhom x Q hQ]
  exact polynomialExponentialCoordinate_potential x _

end PolynomialPotentialRelation
end Erdos3

end

section

namespace Erdos3.PolynomialTranslationGroup

open MvPolynomial
variable {σ : Type*}

noncomputable def actionHom (g : PolynomialTranslationGroup σ) :
    MvPolynomial (σ ⊕ Unit) ℚ →ₐ[ℚ] MvPolynomial (σ ⊕ Unit) ℚ :=
  aeval (Sum.elim (fun i => X (Sum.inl i) + C (g.base i))
    (fun u => X (Sum.inr u) + rename Sum.inl (polynomialTranslate g.base g.polynomial)))

@[simp] theorem actionHom_X_inl (g : PolynomialTranslationGroup σ) (i : σ) :
    actionHom g (X (Sum.inl i)) = X (Sum.inl i) + C (g.base i) := by simp [actionHom]

@[simp] theorem actionHom_X_inr (g : PolynomialTranslationGroup σ) (u : Unit) :
    actionHom g (X (Sum.inr u)) =
      X (Sum.inr u) + rename Sum.inl (polynomialTranslate g.base g.polynomial) := by simp [actionHom]

@[simp] theorem actionHom_C (g : PolynomialTranslationGroup σ) (r : ℚ) :
    actionHom g (C r) = C r := by simp [actionHom]

theorem actionHom_rename (g : PolynomialTranslationGroup σ) (P : MvPolynomial σ ℚ) :
    actionHom g (rename Sum.inl P) = rename Sum.inl (polynomialTranslate g.base P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simp only [map_add,hP,hQ]
  | mul_X P i hP => simp only [map_mul,rename_X,actionHom_X_inl,hP,polynomialTranslate_X,
      map_add,rename_C]

@[simp] theorem actionHom_one (P : MvPolynomial (σ ⊕ Unit) ℚ) : actionHom 1 P = P := by
  have hh : actionHom (1 : PolynomialTranslationGroup σ) = AlgHom.id ℚ _ := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i <;> simp
  exact DFunLike.congr_fun hh P

theorem actionHom_mul (g h : PolynomialTranslationGroup σ)
    (P : MvPolynomial (σ ⊕ Unit) ℚ) :
    actionHom (g*h) P = actionHom g (actionHom h P) := by
  have hh : actionHom (g*h) = (actionHom g).comp (actionHom h) := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i with
    | inl i => simp [Pi.add_apply, add_assoc]
    | inr u =>
      simp only [actionHom_X_inr,base_mul,polynomial_mul,map_add,polynomialTranslate_comp,
        AlgHom.comp_apply,actionHom_rename]
      rw [show g.base + h.base + -h.base = g.base by abel]
      abel
  exact DFunLike.congr_fun hh P

noncomputable def action (g : PolynomialTranslationGroup σ) :
    MvPolynomial (σ ⊕ Unit) ℚ ≃ₐ[ℚ] MvPolynomial (σ ⊕ Unit) ℚ :=
  { actionHom g with
    invFun := actionHom g⁻¹
    left_inv := fun P => by
      change actionHom g⁻¹ (actionHom g P) = P
      rw [← actionHom_mul, inv_mul_cancel, actionHom_one]
    right_inv := fun P => by
      change actionHom g (actionHom g⁻¹ P) = P
      rw [← actionHom_mul, mul_inv_cancel, actionHom_one] }

noncomputable def actionMonoidHom : PolynomialTranslationGroup σ →*
    (MvPolynomial (σ ⊕ Unit) ℚ ≃ₐ[ℚ] MvPolynomial (σ ⊕ Unit) ℚ) where
  toFun := action
  map_one' := by apply AlgEquiv.ext; intro P; exact actionHom_one P
  map_mul' g h := by apply AlgEquiv.ext; intro P; exact actionHom_mul g h P

theorem actionMonoidHom_injective : Function.Injective (actionMonoidHom (σ := σ)) := by
  intro g h heq
  have hb : g.base = h.base := by
    funext i
    have hh := congrArg (fun f : MvPolynomial (σ ⊕ Unit) ℚ ≃ₐ[ℚ]
      MvPolynomial (σ ⊕ Unit) ℚ => f (X (Sum.inl i))) heq
    change actionHom g (X (Sum.inl i)) = actionHom h (X (Sum.inl i)) at hh
    rw [actionHom_X_inl,actionHom_X_inl] at hh
    exact MvPolynomial.C_injective (σ ⊕ Unit) ℚ (add_left_cancel hh)
  apply PolynomialTranslationGroup.ext hb
  have hh := congrArg (fun f : MvPolynomial (σ ⊕ Unit) ℚ ≃ₐ[ℚ]
    MvPolynomial (σ ⊕ Unit) ℚ => f (X (Sum.inr ()))) heq
  change actionHom g (X (Sum.inr ())) = actionHom h (X (Sum.inr ())) at hh
  rw [actionHom_X_inr,actionHom_X_inr] at hh
  have hp := MvPolynomial.rename_injective Sum.inl Sum.inl_injective (add_left_cancel hh)
  have hp' := congrArg (polynomialTranslate (-g.base)) hp
  simpa only [hb, polynomialTranslate_comp, neg_add_cancel, polynomialTranslate_zero] using hp'

end Erdos3.PolynomialTranslationGroup

end

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators

variable {σ : Type*} [Fintype σ]

@[simp] theorem scalarDirectionalDerivative_neg (x : σ → ℚ)
    (P : MvPolynomial σ ℚ) :
    scalarDirectionalDerivative (-x) P = -scalarDirectionalDerivative x P := by
  simp only [scalarDirectionalDerivative_apply, Pi.neg_apply, neg_smul,
    Finset.sum_neg_distrib]

theorem polynomialTranslationPath_neg_derivative (x : σ → ℚ)
    (P : MvPolynomial σ ℚ) :
    (polynomialTranslationPath (-x) P).derivative =
      polynomialTranslationPath (-x) (scalarDirectionalDerivative x P) := by
  rw [polynomialTranslationPath_derivative, scalarDirectionalDerivative_neg, map_neg, neg_neg]

theorem polynomialTranslationPath_neg_coeff (x : σ → ℚ)
    (P : MvPolynomial σ ℚ) (i : ℕ) :
    (polynomialTranslationPath (-x) P).coeff i =
      ((i.factorial : ℚ)⁻¹) • ((scalarDirectionalDerivative x).toLinearMap ^ i) P := by
  induction i generalizing P with
  | zero =>
      simpa only [Nat.factorial_zero, Nat.cast_one, inv_one, one_smul, pow_zero,
        Module.End.one_apply, Polynomial.coeff_zero_eq_eval_zero]
        using polynomialTranslationPath_eval_zero (-x) P
  | succ i ih =>
      have hc := congrArg (fun Q : Polynomial (MvPolynomial σ ℚ) => Q.coeff i)
        (polynomialTranslationPath_neg_derivative x P)
      rw [Polynomial.coeff_derivative] at hc
      have hmul : ((i + 1 : ℕ) : ℚ) • (polynomialTranslationPath (-x) P).coeff (i + 1) =
          (polynomialTranslationPath (-x) (scalarDirectionalDerivative x P)).coeff i := by
        rw [Nat.cast_smul_eq_nsmul ℚ, nsmul_eq_mul']
        simpa only [Nat.cast_add, Nat.cast_one] using hc
      have hinv : (polynomialTranslationPath (-x) P).coeff (i + 1) =
          (((i + 1 : ℕ) : ℚ)⁻¹) •
            (polynomialTranslationPath (-x) (scalarDirectionalDerivative x P)).coeff i := by
        rw [← hmul, smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero i)), one_smul]
      rw [hinv, ih, smul_smul, Nat.factorial_succ, Nat.cast_mul, mul_inv_rev,
        pow_succ, Module.End.mul_apply]
      congr 1
      exact mul_comm _ _

theorem scalarDirectionalDerivative_pow_eq_zero_of_weightedSupport
    (w : σ → ℕ) (hw : ∀ i, 0 < w i) (x : σ → ℚ)
    {P : MvPolynomial σ ℚ} {n : ℕ} (hP : P ∈ weightedSupportLE w n) :
    ((scalarDirectionalDerivative x).toLinearMap ^ (n + 1)) P = 0 := by
  apply weightedDerivation_pow_eq_zero w _ _ hP
  intro i
  rw [scalarDirectionalDerivative_X, weightedSupportDrop_one]
  intro a ha
  have h : Finsupp.weight w a ≤ 0 := weightedSupportLE_C w 0 (x i) ha
  change Finsupp.weight w a < w i
  exact lt_of_le_of_lt h (hw i)

theorem polynomialTranslationPath_neg_support_of_nilpotent (x : σ → ℚ)
    {P : MvPolynomial σ ℚ} {n : ℕ}
    (hP : ((scalarDirectionalDerivative x).toLinearMap ^ (n + 1)) P = 0) :
    (polynomialTranslationPath (-x) P).support ⊆ Finset.range (n + 1) := by
  intro i hi
  apply Finset.mem_range.mpr
  by_contra hn
  obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hn)
  have hz : ((scalarDirectionalDerivative x).toLinearMap ^ i) P = 0 := by
    rw [show i = j + (n + 1) by omega, pow_add, Module.End.mul_apply, hP, map_zero]
  exact Polynomial.mem_support_iff.mp hi (by
    rw [polynomialTranslationPath_neg_coeff, hz, smul_zero])

theorem polynomialExponentialCoordinate_neg_series_of_nilpotent (x : σ → ℚ)
    {P : MvPolynomial σ ℚ} {n : ℕ}
    (hP : ((scalarDirectionalDerivative x).toLinearMap ^ (n + 1)) P = 0) :
    polynomialExponentialCoordinate (-x) P =
      ∑ i ∈ Finset.range (n + 1),
        (((i + 1).factorial : ℚ)⁻¹) • ((scalarDirectionalDerivative x).toLinearMap ^ i) P := by
  classical
  rw [polynomialExponentialCoordinate_formula]
  calc
    _ = ∑ i ∈ Finset.range (n + 1),
        (((i + 1 : ℕ) : ℚ)⁻¹) • (polynomialTranslationPath (-x) P).coeff i := by
      apply Finset.sum_subset (polynomialTranslationPath_neg_support_of_nilpotent x hP)
      intro i hi hni
      rw [Polynomial.notMem_support_iff.mp hni, smul_zero]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [polynomialTranslationPath_neg_coeff, smul_smul, Nat.factorial_succ,
        Nat.cast_mul, mul_inv_rev]
      congr 1
      exact mul_comm _ _

end Erdos3

end

end OAI
