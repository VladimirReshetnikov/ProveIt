import Surreal.Foundations.SignSequenceStandardPart
import Surreal.Surcomplex.ComplexEmbedding

/-!
# Standard parts of actual finite surcomplex numbers

Coordinatewise real standard part gives the homomorphism in `a:eq:st`
on the constructed surcomplex field. The coordinate finiteness and
infinitesimal predicates agree with the document's modulus bounds.
The infinitesimal kernel is maximal, the residue field is ordinary `ℂ`,
and every finite element has a unique ordinary-complex plus infinitesimal
decomposition. Identification with Hahn coefficient extraction remains
a separate normal-form obligation.
-/

universe u

namespace Surreal.Surcomplex

open Foundations

noncomputable section

/-- Finiteness of both actual surreal coordinates. -/
def IsFinite (z : Surcomplex.{u}) : Prop :=
  SignSequence.IsFinite z.re ∧ SignSequence.IsFinite z.im

/-- Infinitesimality of both coordinates, including zero. -/
def IsInfinitesimal (z : Surcomplex.{u}) : Prop :=
  SignSequence.IsInfinitesimal z.re ∧ SignSequence.IsInfinitesimal z.im

theorem modulus_le_abs_re_add_abs_im (z : Surcomplex.{u}) :
    modulus z ≤ |z.re| + |z.im| := by
  simpa only [re_add_im_mul_I, modulus_ofReal, modulus_mul, modulus_I, mul_one] using
    modulus_add_le (ofReal z.re) (ofReal z.im * I)

theorem isFinite_iff_exists_nat_modulus_lt (z : Surcomplex.{u}) :
    IsFinite z ↔ ∃ n : ℕ, modulus z < n := by
  constructor
  · rintro ⟨hre, him⟩
    obtain ⟨n, hn⟩ := (SignSequence.isFinite_iff_exists_nat_abs_lt z.re).mp hre
    obtain ⟨m, hm⟩ := (SignSequence.isFinite_iff_exists_nat_abs_lt z.im).mp him
    exact ⟨n + m, by simpa only [Nat.cast_add] using
      (modulus_le_abs_re_add_abs_im z).trans_lt (_root_.add_lt_add hn hm)⟩
  · rintro ⟨n, hn⟩
    exact ⟨(SignSequence.isFinite_iff_exists_nat_abs_lt z.re).mpr
      ⟨n, (abs_re_le_modulus z).trans_lt hn⟩,
      (SignSequence.isFinite_iff_exists_nat_abs_lt z.im).mpr
      ⟨n, (abs_im_le_modulus z).trans_lt hn⟩⟩

theorem isFinite_iff_modulus (z : Surcomplex.{u}) :
    IsFinite z ↔ SignSequence.IsFinite (modulus z) := by
  rw [isFinite_iff_exists_nat_modulus_lt, SignSequence.isFinite_iff_exists_nat_abs_lt,
    abs_of_nonneg (modulus_nonneg z)]

theorem isInfinitesimal_iff_forall_real_modulus_lt (z : Surcomplex.{u}) :
    IsInfinitesimal z ↔ ∀ r : ℝ, 0 < r → modulus z < SignSequence.ofReal r := by
  constructor
  · rintro ⟨hre, him⟩ r hr
    have hhalf : 0 < r / 2 := half_pos hr
    have ha := (SignSequence.isInfinitesimal_iff_forall_real_abs_lt z.re).mp hre (r / 2) hhalf
    have hb := (SignSequence.isInfinitesimal_iff_forall_real_abs_lt z.im).mp him (r / 2) hhalf
    have h := (modulus_le_abs_re_add_abs_im z).trans_lt (_root_.add_lt_add ha hb)
    simpa only [← map_add, add_halves] using h
  · intro h
    exact ⟨(SignSequence.isInfinitesimal_iff_forall_real_abs_lt z.re).mpr
      (fun r hr => (abs_re_le_modulus z).trans_lt (h r hr)),
      (SignSequence.isInfinitesimal_iff_forall_real_abs_lt z.im).mpr
      (fun r hr => (abs_im_le_modulus z).trans_lt (h r hr))⟩

theorem isInfinitesimal_iff_modulus (z : Surcomplex.{u}) :
    IsInfinitesimal z ↔ SignSequence.IsInfinitesimal (modulus z) := by
  rw [isInfinitesimal_iff_forall_real_modulus_lt,
    SignSequence.isInfinitesimal_iff_forall_real_abs_lt, abs_of_nonneg (modulus_nonneg z)]

/-- Exactly the reciprocal-natural modulus bounds in the source. -/
theorem isInfinitesimal_iff_forall_nat_modulus_lt (z : Surcomplex.{u}) :
    IsInfinitesimal z ↔ ∀ n : ℕ, 0 < n → modulus z < 1 / (n : SignSequence.{u}) := by
  rw [isInfinitesimal_iff_modulus, SignSequence.isInfinitesimal_iff_forall_nat_abs_lt,
    abs_of_nonneg (modulus_nonneg z)]

theorem finite_of_infinitesimal {z : Surcomplex.{u}} (hz : IsInfinitesimal z) : IsFinite z :=
  ⟨SignSequence.finite_of_infinitesimal hz.1, SignSequence.finite_of_infinitesimal hz.2⟩

/-- The subring of finite elements of the actual surcomplex field. -/
def finiteSubring : Subring Surcomplex.{u} where
  carrier := {z | IsFinite z}
  zero_mem' := ⟨SignSequence.finite_zero, SignSequence.finite_zero⟩
  one_mem' := ⟨SignSequence.finite_one, SignSequence.finite_zero⟩
  add_mem' hz hw := ⟨SignSequence.finite_add hz.1 hw.1, SignSequence.finite_add hz.2 hw.2⟩
  neg_mem' hz := ⟨SignSequence.finite_neg hz.1, SignSequence.finite_neg hz.2⟩
  mul_mem' {z w} hz hw := by
    constructor
    · rw [mul_re]
      exact SignSequence.finite_sub (SignSequence.finite_mul hz.1 hw.1)
        (SignSequence.finite_mul hz.2 hw.2)
    · rw [mul_im]
      exact SignSequence.finite_add (SignSequence.finite_mul hz.1 hw.2)
        (SignSequence.finite_mul hz.2 hw.1)

@[simp] theorem mem_finiteSubring (z : Surcomplex.{u}) : z ∈ finiteSubring ↔ IsFinite z := Iff.rfl

/-- Finiteness defines an actual valuation subring: either an element or its inverse is finite. -/
def finiteValuationSubring : ValuationSubring Surcomplex.{u} where
  __ := finiteSubring
  mem_or_inv_mem' z := by
    have h := (ArchimedeanClass.addValuation SignSequence.{u}).toValuation.valuationSubring.mem_or_inv_mem
      (modulus z)
    change SignSequence.IsFinite (modulus z) ∨ SignSequence.IsFinite (modulus z)⁻¹ at h
    exact h.imp (isFinite_iff_modulus z).mpr
      (fun hi => (isFinite_iff_modulus z⁻¹).mpr (by rwa [modulus_inv]))

@[simp] theorem mem_finiteValuationSubring (z : Surcomplex.{u}) :
    z ∈ finiteValuationSubring ↔ IsFinite z := Iff.rfl

theorem finite_ofComplex (z : ℂ) : IsFinite (ofComplex z : Surcomplex.{u}) :=
  ⟨SignSequence.finite_ofReal z.re, SignSequence.finite_ofReal z.im⟩

/-- Coordinatewise real standard part, with no ring-hom assertion on infinite inputs. -/
def standardPart (z : Surcomplex.{u}) : ℂ :=
  ⟨SignSequence.standardPart z.re, SignSequence.standardPart z.im⟩

@[simp] theorem standardPart_re (z : Surcomplex.{u}) :
    (standardPart z).re = SignSequence.standardPart z.re := rfl
@[simp] theorem standardPart_im (z : Surcomplex.{u}) :
    (standardPart z).im = SignSequence.standardPart z.im := rfl

@[simp] theorem standardPart_ofComplex (z : ℂ) :
    standardPart (ofComplex z : Surcomplex.{u}) = z := by
  apply Complex.ext <;> simp

/-- Standard part is a ring homomorphism on the finite subring. -/
def standardPartHom : finiteSubring.{u} →+* ℂ where
  toFun z := standardPart z.1
  map_zero' := by apply Complex.ext <;> simp
  map_one' := by apply Complex.ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_add' z w := by
    apply Complex.ext
    · exact SignSequence.standardPart_add z.2.1 w.2.1
    · exact SignSequence.standardPart_add z.2.2 w.2.2
  map_mul' z w := by
    apply Complex.ext
    · change SignSequence.standardPart ((z.1 * w.1).re) = _
      rw [mul_re, SignSequence.standardPart_sub
        (SignSequence.finite_mul z.2.1 w.2.1) (SignSequence.finite_mul z.2.2 w.2.2),
        SignSequence.standardPart_mul z.2.1 w.2.1, SignSequence.standardPart_mul z.2.2 w.2.2]
      rfl
    · change SignSequence.standardPart ((z.1 * w.1).im) = _
      rw [mul_im, SignSequence.standardPart_add
        (SignSequence.finite_mul z.2.1 w.2.2) (SignSequence.finite_mul z.2.2 w.2.1),
        SignSequence.standardPart_mul z.2.1 w.2.2, SignSequence.standardPart_mul z.2.2 w.2.1]
      rfl

@[simp] theorem standardPartHom_apply (z : finiteSubring.{u}) :
    standardPartHom z = standardPart z.1 := rfl

theorem standardPart_add {z w : Surcomplex.{u}} (hz : IsFinite z) (hw : IsFinite w) :
    standardPart (z + w) = standardPart z + standardPart w :=
  standardPartHom.map_add ⟨z, hz⟩ ⟨w, hw⟩

theorem standardPart_mul {z w : Surcomplex.{u}} (hz : IsFinite z) (hw : IsFinite w) :
    standardPart (z * w) = standardPart z * standardPart w :=
  standardPartHom.map_mul ⟨z, hz⟩ ⟨w, hw⟩

@[simp] theorem standardPart_neg (z : Surcomplex.{u}) :
    standardPart (-z) = -standardPart z := by
  apply Complex.ext <;> simp

@[simp] theorem standardPart_conj (z : Surcomplex.{u}) :
    standardPart (conj z) = star (standardPart z) := by
  apply Complex.ext <;> simp

/-- Standard part also respects the modulus of a finite surcomplex. -/
theorem standardPart_modulus {z : Surcomplex.{u}} (hz : IsFinite z) :
    SignSequence.standardPart (modulus z) = norm (standardPart z) := by
  have hm := (isFinite_iff_modulus z).mp hz
  have h := congrArg SignSequence.standardPart (modulus_sq z)
  simp only [normSq_eq, pow_two, SignSequence.standardPart_mul hm hm,
    SignSequence.standardPart_add (SignSequence.finite_mul hz.1 hz.1)
      (SignSequence.finite_mul hz.2 hz.2),
    SignSequence.standardPart_mul hz.1 hz.1, SignSequence.standardPart_mul hz.2 hz.2] at h
  have hnorm := Complex.sq_norm (standardPart z)
  simp only [Complex.normSq_apply, standardPart_re, standardPart_im] at hnorm
  have hn : 0 ≤ SignSequence.standardPart (modulus z) :=
    ArchimedeanClass.stdPart_nonneg (modulus_nonneg z)
  have hc := norm_nonneg (standardPart z)
  nlinarith

theorem standardPartHom_surjective :
    Function.Surjective (standardPartHom : finiteSubring.{u} → ℂ) :=
  fun z => ⟨⟨ofComplex z, finite_ofComplex z⟩, standardPart_ofComplex z⟩

theorem standardPart_eq_zero_iff {z : Surcomplex.{u}} (hz : IsFinite z) :
    standardPart z = 0 ↔ IsInfinitesimal z := by
  rw [Complex.ext_iff]
  exact and_congr (SignSequence.standardPart_eq_zero_iff hz.1)
    (SignSequence.standardPart_eq_zero_iff hz.2)

/-- The infinitesimal ideal of the actual finite subring. -/
def infinitesimalIdeal : Ideal finiteSubring.{u} := RingHom.ker standardPartHom

@[simp] theorem mem_infinitesimalIdeal (z : finiteSubring.{u}) :
    z ∈ infinitesimalIdeal ↔ IsInfinitesimal z.1 := standardPart_eq_zero_iff z.2

theorem infinitesimalIdeal_isMaximal : (infinitesimalIdeal.{u}).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective standardPartHom standardPartHom_surjective

/-- The actual finite surcomplex residue field is ordinary `ℂ`. -/
def standardPartQuotientEquiv : finiteSubring.{u} ⧸ infinitesimalIdeal ≃+* ℂ :=
  RingHom.quotientKerEquivOfSurjective standardPartHom_surjective

@[simp] theorem standardPartQuotientEquiv_mk (z : finiteSubring.{u}) :
    standardPartQuotientEquiv (Ideal.Quotient.mk infinitesimalIdeal z) = standardPart z.1 := rfl

theorem infinitesimal_sub_ofComplex_iff {z : Surcomplex.{u}} (hz : IsFinite z) {a : ℂ} :
    IsInfinitesimal (z - ofComplex a) ↔ standardPart z = a := by
  change (SignSequence.IsInfinitesimal (z.re - SignSequence.ofReal a.re) ∧
    SignSequence.IsInfinitesimal (z.im - SignSequence.ofReal a.im)) ↔ _
  rw [SignSequence.infinitesimal_sub_ofReal_iff hz.1,
    SignSequence.infinitesimal_sub_ofReal_iff hz.2, Complex.ext_iff]
  rfl

theorem infinitesimal_sub_standardPart {z : Surcomplex.{u}} (hz : IsFinite z) :
    IsInfinitesimal (z - ofComplex (standardPart z)) :=
  (infinitesimal_sub_ofComplex_iff hz).mpr rfl

theorem existsUnique_complex_part {z : Surcomplex.{u}} (hz : IsFinite z) :
    ∃! a : ℂ, IsInfinitesimal (z - ofComplex a) := by
  refine ⟨standardPart z, infinitesimal_sub_standardPart hz, ?_⟩
  intro a ha
  exact ((infinitesimal_sub_ofComplex_iff hz).mp ha).symm

/-- Uniqueness of both terms in the complex-plus-infinitesimal decomposition. -/
theorem existsUnique_complex_infinitesimal_decomposition {z : Surcomplex.{u}} (hz : IsFinite z) :
    ∃! p : ℂ × Surcomplex.{u}, IsInfinitesimal p.2 ∧ z = ofComplex p.1 + p.2 := by
  refine ⟨⟨standardPart z, z - ofComplex (standardPart z)⟩,
    ⟨infinitesimal_sub_standardPart hz, by simp⟩, ?_⟩
  rintro ⟨a, ε⟩ ⟨hε, hzε⟩
  have heq : z - ofComplex a = ε := by rw [hzε]; simp
  have ha : standardPart z = a := (infinitesimal_sub_ofComplex_iff hz).mp (heq ▸ hε)
  exact Prod.ext ha.symm (by simpa only [ha] using heq.symm)

end

end Surreal.Surcomplex
