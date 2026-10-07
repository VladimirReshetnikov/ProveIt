import Mathlib.Algebra.MvPolynomial.Derivation
import OAI.Combinatorics.Progressions.Estimates.VectorAlgebraicMajorDecomposition

namespace OAI


namespace Erdos3

open MvPolynomial

variable {σ : Type*}

noncomputable def integerCoefficientPolynomials (σ : Type*) : Subalgebra ℤ (MvPolynomial σ ℚ) :=
  (MvPolynomial.mapAlgHom (Int.castRingHom ℚ).toIntAlgHom).range

theorem mem_integerCoefficientPolynomials (P : MvPolynomial σ ℚ) :
    P ∈ integerCoefficientPolynomials σ ↔ ∃ Q : MvPolynomial σ ℤ,
      MvPolynomial.map (Int.castRingHom ℚ) Q = P := Iff.rfl

theorem mem_integerCoefficientPolynomials_iff (P : MvPolynomial σ ℚ) :
    P ∈ integerCoefficientPolynomials σ ↔ ∀ a, ∃ z : ℤ, P.coeff a = (z : ℚ) := by
  change P ∈ (MvPolynomial.mapAlgHom (Int.castRingHom ℚ).toIntAlgHom).range.toSubmodule ↔ _
  rw [MvPolynomial.range_mapAlgHom, MvPolynomial.mem_coeffsIn]
  constructor
  · intro h a
    obtain ⟨z, hz⟩ := h a
    exact ⟨z, hz.symm⟩
  · intro h a
    obtain ⟨z, hz⟩ := h a
    exact ⟨z, hz.symm⟩

theorem integerCoefficientPolynomials_X (i : σ) :
    (X i : MvPolynomial σ ℚ) ∈ integerCoefficientPolynomials σ :=
  ⟨X i, MvPolynomial.map_X _ _⟩

theorem integerCoefficientPolynomials_C (z : ℤ) :
    (C (z : ℚ) : MvPolynomial σ ℚ) ∈ integerCoefficientPolynomials σ :=
  ⟨C z, MvPolynomial.map_C _ _⟩

theorem integerCoefficientPolynomials_rat_smul {c : ℚ} (hc : ∃ z : ℤ, c = (z : ℚ))
    {P : MvPolynomial σ ℚ} (hP : P ∈ integerCoefficientPolynomials σ) :
    c • P ∈ integerCoefficientPolynomials σ := by
  obtain ⟨z, rfl⟩ := hc
  apply (mem_integerCoefficientPolynomials_iff _).mpr
  intro a
  obtain ⟨v, hv⟩ := (mem_integerCoefficientPolynomials_iff P).mp hP a
  refine ⟨z * v, ?_⟩
  simp [hv]

theorem integerPolynomialHom_preserves
    (F : MvPolynomial σ ℚ →ₐ[ℚ] MvPolynomial σ ℚ)
    (hF : ∀ i, F (X i) ∈ integerCoefficientPolynomials σ)
    {P : MvPolynomial σ ℚ} (hP : P ∈ integerCoefficientPolynomials σ) :
    F P ∈ integerCoefficientPolynomials σ := by
  obtain ⟨Q, rfl⟩ := (mem_integerCoefficientPolynomials P).mp hP
  clear hP
  induction Q using MvPolynomial.induction_on with
  | C z =>
    rw [MvPolynomial.map_C]
    change F (C (z : ℚ)) ∈ integerCoefficientPolynomials σ
    rw [show F (C (z : ℚ)) = C (z : ℚ) from F.commutes _]
    exact integerCoefficientPolynomials_C z
  | add P Q hP hQ =>
    simpa only [map_add] using (integerCoefficientPolynomials σ).add_mem hP hQ
  | mul_X P i hP =>
    simpa only [map_mul, MvPolynomial.map_X] using
      (integerCoefficientPolynomials σ).mul_mem hP (hF i)

theorem integerPolynomialDerivation_preserves
    (D : Derivation ℚ (MvPolynomial σ ℚ) (MvPolynomial σ ℚ))
    (hD : ∀ i, D (X i) ∈ integerCoefficientPolynomials σ)
    {P : MvPolynomial σ ℚ} (hP : P ∈ integerCoefficientPolynomials σ) :
    D P ∈ integerCoefficientPolynomials σ := by
  obtain ⟨Q, rfl⟩ := (mem_integerCoefficientPolynomials P).mp hP
  clear hP
  induction Q using MvPolynomial.induction_on with
  | C z =>
    simp only [MvPolynomial.map_C, MvPolynomial.derivation_C]
    exact (integerCoefficientPolynomials σ).zero_mem
  | add P Q hP hQ =>
    simpa only [map_add] using (integerCoefficientPolynomials σ).add_mem hP hQ
  | mul_X P i hP =>
    rw [map_mul, MvPolynomial.map_X, D.leibniz, smul_eq_mul, smul_eq_mul]
    exact (integerCoefficientPolynomials σ).add_mem
      ((integerCoefficientPolynomials σ).mul_mem ⟨P, rfl⟩ (hD i))
      ((integerCoefficientPolynomials σ).mul_mem (integerCoefficientPolynomials_X i) hP)

theorem integerPolynomialDerivation_pow
    (D : Derivation ℚ (MvPolynomial σ ℚ) (MvPolynomial σ ℚ))
    (hD : ∀ i, D (X i) ∈ integerCoefficientPolynomials σ)
    {P : MvPolynomial σ ℚ} (hP : P ∈ integerCoefficientPolynomials σ) (k : ℕ) :
    (D.toLinearMap ^ k) P ∈ integerCoefficientPolynomials σ := by
  induction k with
  | zero => exact hP
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact integerPolynomialDerivation_preserves D hD ih

end Erdos3


namespace Erdos3.PolynomialTranslationGroupOver

open MvPolynomial
variable {R σ : Type*} [CommRing R]

noncomputable def actionHom (g : PolynomialTranslationGroupOver R σ) :
    MvPolynomial (σ ⊕ Unit) R →ₐ[R] MvPolynomial (σ ⊕ Unit) R :=
  aeval (Sum.elim (fun i => X (Sum.inl i) + C (g.base i))
    (fun u => X (Sum.inr u) + rename Sum.inl (polynomialTranslate g.base g.polynomial)))

@[simp] theorem actionHom_X_inl (g : PolynomialTranslationGroupOver R σ) (i : σ) :
    actionHom g (X (Sum.inl i)) = X (Sum.inl i) + C (g.base i) := by simp [actionHom]

@[simp] theorem actionHom_X_inr (g : PolynomialTranslationGroupOver R σ) (u : Unit) :
    actionHom g (X (Sum.inr u)) =
      X (Sum.inr u) + rename Sum.inl (polynomialTranslate g.base g.polynomial) := by simp [actionHom]

@[simp] theorem actionHom_C (g : PolynomialTranslationGroupOver R σ) (r : R) :
    actionHom g (C r) = C r := by simp [actionHom]

theorem actionHom_rename (g : PolynomialTranslationGroupOver R σ) (P : MvPolynomial σ R) :
    actionHom g (rename Sum.inl P) = rename Sum.inl (polynomialTranslate g.base P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simp only [map_add,hP,hQ]
  | mul_X P i hP => simp only [map_mul,rename_X,actionHom_X_inl,hP,polynomialTranslate_X,
      map_add,rename_C]

@[simp] theorem actionHom_one (P : MvPolynomial (σ ⊕ Unit) R) : actionHom 1 P = P := by
  have hh : actionHom (1 : PolynomialTranslationGroupOver R σ) = AlgHom.id R _ := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i <;> simp
  exact DFunLike.congr_fun hh P

theorem actionHom_mul (g h : PolynomialTranslationGroupOver R σ)
    (P : MvPolynomial (σ ⊕ Unit) R) :
    actionHom (g*h) P = actionHom g (actionHom h P) := by
  have hh : actionHom (g*h) = (actionHom g).comp (actionHom h) := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i with
    | inl i => simp [Pi.add_apply, add_assoc]
    | inr u =>
      simp only [actionHom_X_inr,base_mul,polynomial_mul,map_add,polynomialTranslate_comp_ring,
        AlgHom.comp_apply,actionHom_rename]
      rw [show g.base + h.base + -h.base = g.base by abel]
      abel
  exact DFunLike.congr_fun hh P

noncomputable def action (g : PolynomialTranslationGroupOver R σ) :
    MvPolynomial (σ ⊕ Unit) R ≃ₐ[R] MvPolynomial (σ ⊕ Unit) R :=
  { actionHom g with
    invFun := actionHom g⁻¹
    left_inv := fun P => by
      change actionHom g⁻¹ (actionHom g P) = P
      rw [← actionHom_mul, inv_mul_cancel, actionHom_one]
    right_inv := fun P => by
      change actionHom g (actionHom g⁻¹ P) = P
      rw [← actionHom_mul, mul_inv_cancel, actionHom_one] }

noncomputable def actionMonoidHom : PolynomialTranslationGroupOver R σ →*
    (MvPolynomial (σ ⊕ Unit) R ≃ₐ[R] MvPolynomial (σ ⊕ Unit) R) where
  toFun := action
  map_one' := by apply AlgEquiv.ext; intro P; exact actionHom_one P
  map_mul' g h := by apply AlgEquiv.ext; intro P; exact actionHom_mul g h P

theorem actionMonoidHom_injective : Function.Injective (actionMonoidHom (R := R) (σ := σ)) := by
  intro g h heq
  have hb : g.base = h.base := by
    funext i
    have hh := congrArg (fun f : MvPolynomial (σ ⊕ Unit) R ≃ₐ[R]
      MvPolynomial (σ ⊕ Unit) R => f (X (Sum.inl i))) heq
    change actionHom g (X (Sum.inl i)) = actionHom h (X (Sum.inl i)) at hh
    rw [actionHom_X_inl,actionHom_X_inl] at hh
    exact MvPolynomial.C_injective (σ ⊕ Unit) R (add_left_cancel hh)
  apply PolynomialTranslationGroupOver.ext hb
  have hh := congrArg (fun f : MvPolynomial (σ ⊕ Unit) R ≃ₐ[R]
    MvPolynomial (σ ⊕ Unit) R => f (X (Sum.inr ()))) heq
  change actionHom g (X (Sum.inr ())) = actionHom h (X (Sum.inr ())) at hh
  rw [actionHom_X_inr,actionHom_X_inr] at hh
  have hp := MvPolynomial.rename_injective Sum.inl Sum.inl_injective (add_left_cancel hh)
  have hp' := congrArg (polynomialTranslate (-g.base)) hp
  simpa only [hb, polynomialTranslate_comp_ring, neg_add_cancel, polynomialTranslate_zero_ring] using hp'

end Erdos3.PolynomialTranslationGroupOver


namespace Erdos3

open MvPolynomial

variable {B R S : Type*} [CommRing R] [CommRing S]

theorem polynomialTranslate_map_ring (φ : R →+* S) (h : B → R)
    (P : MvPolynomial B R) :
    MvPolynomial.map φ (polynomialTranslate h P) =
      polynomialTranslate (fun i => φ (h i)) (MvPolynomial.map φ P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp only [map_mul, hp, polynomialTranslate_X, map_add, map_X, map_C]

namespace PolynomialTranslationGroupOver

noncomputable def map (φ : R →+* S) :
    PolynomialTranslationGroupOver R B →* PolynomialTranslationGroupOver S B where
  toFun g := ⟨fun i => φ (g.base i), MvPolynomial.map φ g.polynomial⟩
  map_one' := by ext <;> simp
  map_mul' g h := by
    apply PolynomialTranslationGroupOver.ext
    · ext i; simp
    · simp only [polynomial_mul, map_add, polynomialTranslate_map_ring]
      congr 1
      congr 1
      exact congrArg polynomialTranslate (funext (fun i => map_neg φ (h.base i)))

@[simp] theorem map_base (φ : R →+* S) (g : PolynomialTranslationGroupOver R B) (i : B) :
    (PolynomialTranslationGroupOver.map φ g).base i = φ (g.base i) := rfl

@[simp] theorem map_polynomial (φ : R →+* S) (g : PolynomialTranslationGroupOver R B) :
    (PolynomialTranslationGroupOver.map φ g).polynomial = MvPolynomial.map φ g.polynomial := rfl

end PolynomialTranslationGroupOver

end Erdos3


namespace Erdos3.PolynomialTranslationGroupOver

open MvPolynomial
variable {σ R : Type*} [CommRing R]

noncomputable def actionElement (x : σ → R) (Q : MvPolynomial σ R) :
    PolynomialTranslationGroupOver R σ := ⟨x, polynomialTranslate (-x) Q⟩

@[simp] theorem actionElement_X_inl (x : σ → R) (Q : MvPolynomial σ R) (i : σ) :
    actionMonoidHom (actionElement x Q) (X (Sum.inl i)) = X (Sum.inl i) + C (x i) :=
  actionHom_X_inl _ i

@[simp] theorem actionElement_X_inr (x : σ → R) (Q : MvPolynomial σ R) (u : Unit) :
    actionMonoidHom (actionElement x Q) (X (Sum.inr u)) = X (Sum.inr u) + rename Sum.inl Q := by
  change actionHom (actionElement x Q) (X (Sum.inr u)) = _
  rw [actionHom_X_inr]
  change X (Sum.inr u) + rename Sum.inl (polynomialTranslate x (polynomialTranslate (-x) Q)) = _
  rw [polynomialTranslate_comp_ring, add_neg_cancel, polynomialTranslate_zero_ring]

theorem action_eq_of_shape
    (f : MvPolynomial (σ ⊕ Unit) R ≃ₐ[R] MvPolynomial (σ ⊕ Unit) R)
    (x : σ → R) (Q : MvPolynomial σ R)
    (hbase : ∀ i, f (X (Sum.inl i)) = X (Sum.inl i) + C (x i))
    (hextra : f (X (Sum.inr ())) = X (Sum.inr ()) + rename Sum.inl Q) :
    actionMonoidHom (actionElement x Q) = f := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply MvPolynomial.algHom_ext
  intro i
  cases i with
  | inl i => exact (actionElement_X_inl x Q i).trans (hbase i).symm
  | inr u => cases u; exact (actionElement_X_inr x Q ()).trans hextra.symm

theorem existsUnique_action_of_shape
    (f : MvPolynomial (σ ⊕ Unit) R ≃ₐ[R] MvPolynomial (σ ⊕ Unit) R)
    (x : σ → R) (Q : MvPolynomial σ R)
    (hbase : ∀ i, f (X (Sum.inl i)) = X (Sum.inl i) + C (x i))
    (hextra : f (X (Sum.inr ())) = X (Sum.inr ()) + rename Sum.inl Q) :
    ∃! g : PolynomialTranslationGroupOver R σ, actionMonoidHom g = f := by
  refine ⟨actionElement x Q, action_eq_of_shape f x Q hbase hextra, ?_⟩
  intro g hg
  exact actionMonoidHom_injective (hg.trans (action_eq_of_shape f x Q hbase hextra).symm)

end Erdos3.PolynomialTranslationGroupOver


namespace Erdos3

open MvPolynomial
variable {σ R : Type*} [CommRing R]

theorem eval_polynomialTranslate_ring (z h : σ → R) (P : MvPolynomial σ R) :
    eval z (polynomialTranslate h P) = eval (z+h) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp,hq]
  | mul_X p i hp => simp [hp,Pi.add_apply]

namespace PolynomialTranslationGroupOver

theorem action_inverse_X_inl_eval (g : PolynomialTranslationGroupOver R σ)
    (β : σ → R) (y : R) (i : σ) :
    eval (Sum.elim β (fun _ : Unit => y))
      ((actionMonoidHom g).symm (X (Sum.inl i))) = β i - g.base i := by
  have he : (actionMonoidHom g).symm = actionMonoidHom g⁻¹ := (map_inv actionMonoidHom g).symm
  rw [he]
  change eval _ (actionHom g⁻¹ (X (Sum.inl i))) = _
  rw [actionHom_X_inl]
  simp [sub_eq_add_neg]

theorem action_inverse_X_inr_eval (g : PolynomialTranslationGroupOver R σ)
    (β : σ → R) (y : R) :
    eval (Sum.elim β (fun _ : Unit => y))
      ((actionMonoidHom g).symm (X (Sum.inr ()))) = y - eval β g.polynomial := by
  have he : (actionMonoidHom g).symm = actionMonoidHom g⁻¹ := (map_inv actionMonoidHom g).symm
  rw [he]
  change eval _ (actionHom g⁻¹ (X (Sum.inr ()))) = _
  rw [actionHom_X_inr]
  simp only [base_inv,polynomial_inv,map_neg,polynomialTranslate_comp_ring,
    neg_add_cancel,polynomialTranslate_zero_ring]
  simp [MvPolynomial.eval_rename,sub_eq_add_neg]

theorem phase_argument_eq_inverse_point
    (g : PolynomialTranslationGroupOver R σ) (D₀ : MvPolynomial σ R) (β : σ → R) :
    eval β g.polynomial + eval (β - g.base) D₀ =
      eval (fun i => eval (Sum.elim β (fun _ : Unit => (0:R)))
        ((actionMonoidHom g).symm (X (Sum.inl i)))) D₀ -
      eval (Sum.elim β (fun _ : Unit => (0:R)))
        ((actionMonoidHom g).symm (X (Sum.inr ()))) := by
  simp only [action_inverse_X_inl_eval,action_inverse_X_inr_eval,zero_sub,sub_neg_eq_add]
  exact add_comm _ _

end PolynomialTranslationGroupOver
end Erdos3


namespace Erdos3

open MvPolynomial

variable {σ τ : Type*}

theorem integerCoefficientPolynomials_C_iff (c : ℚ) :
    (C c : MvPolynomial σ ℚ) ∈ integerCoefficientPolynomials σ ↔
      ∃ z : ℤ, c = (z : ℚ) := by
  constructor
  · intro hc
    simpa using
      (mem_integerCoefficientPolynomials_iff (C c)).mp hc 0
  · rintro ⟨z, rfl⟩
    exact integerCoefficientPolynomials_C z

theorem integerCoefficientPolynomials_rename (f : σ → τ)
    {P : MvPolynomial σ ℚ} (hP : P ∈ integerCoefficientPolynomials σ) :
    rename f P ∈ integerCoefficientPolynomials τ := by
  obtain ⟨Q, rfl⟩ := (mem_integerCoefficientPolynomials P).mp hP
  exact ⟨rename f Q, MvPolynomial.map_rename _ _ _⟩

theorem integerCoefficientPolynomials_rename_iff (f : σ → τ)
    (hf : Function.Injective f) (P : MvPolynomial σ ℚ) :
    rename f P ∈ integerCoefficientPolynomials τ ↔
      P ∈ integerCoefficientPolynomials σ := by
  constructor
  · intro hP
    apply (mem_integerCoefficientPolynomials_iff P).mpr
    intro a
    simpa only [MvPolynomial.coeff_rename_mapDomain f hf] using
      (mem_integerCoefficientPolynomials_iff (rename f P)).mp hP (a.mapDomain f)
  · exact integerCoefficientPolynomials_rename f

theorem integerCoefficientPolynomials_translate (b : σ → ℚ)
    (hb : ∀ i, ∃ z : ℤ, b i = (z : ℚ))
    {P : MvPolynomial σ ℚ} (hP : P ∈ integerCoefficientPolynomials σ) :
    polynomialTranslate b P ∈ integerCoefficientPolynomials σ := by
  apply integerPolynomialHom_preserves (polynomialTranslate b) _ hP
  intro i
  rw [polynomialTranslate_X]
  exact (integerCoefficientPolynomials σ).add_mem
    (integerCoefficientPolynomials_X i)
    ((integerCoefficientPolynomials_C_iff (b i)).mpr (hb i))

theorem integerCoefficientPolynomials_translate_iff (b : σ → ℚ)
    (hb : ∀ i, ∃ z : ℤ, b i = (z : ℚ)) (P : MvPolynomial σ ℚ) :
    polynomialTranslate b P ∈ integerCoefficientPolynomials σ ↔
      P ∈ integerCoefficientPolynomials σ := by
  constructor
  · intro hP
    have hneg : ∀ i, ∃ z : ℤ, (-b) i = (z : ℚ) := by
      intro i
      obtain ⟨z, hz⟩ := hb i
      exact ⟨-z, by simp [hz]⟩
    have h := integerCoefficientPolynomials_translate (-b) hneg hP
    simpa only [polynomialTranslate_comp_ring, neg_add_cancel,
      polynomialTranslate_zero_ring] using h
  · exact integerCoefficientPolynomials_translate b hb

end Erdos3


namespace Erdos3.PolynomialTranslationGroupOver

open MvPolynomial
variable {σ R S : Type*} [CommRing R] [CommRing S]

theorem map_actionHom (φ : R →+* S) (g : PolynomialTranslationGroupOver R σ)
    (P : MvPolynomial (σ ⊕ Unit) R) :
    MvPolynomial.map φ (actionHom g P) =
      actionHom (PolynomialTranslationGroupOver.map φ g) (MvPolynomial.map φ P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simp only [map_add,hP,hQ]
  | mul_X P i hP =>
      simp only [map_mul,hP,MvPolynomial.map_X]
      congr 1
      cases i with
      | inl i => simp
      | inr u =>
          simp only [actionHom_X_inr,map_add,map_X,MvPolynomial.map_rename,
            polynomialTranslate_map_ring,map_polynomial]
          rfl

noncomputable def rationalEquiv : PolynomialTranslationGroup σ ≃* PolynomialTranslationGroupOver ℚ σ where
  toFun g := ⟨g.base,g.polynomial⟩
  invFun g := ⟨g.base,g.polynomial⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem rationalEquiv_action (g : PolynomialTranslationGroup σ) :
    actionMonoidHom (rationalEquiv g) = PolynomialTranslationGroup.actionMonoidHom g := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply MvPolynomial.algHom_ext
  intro i
  cases i <;> rfl

end Erdos3.PolynomialTranslationGroupOver

end OAI
