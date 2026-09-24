import Surreal.Foundations.SignSequenceReal
import Mathlib.Algebra.Order.Ring.StandardPart

/-!
# Standard parts of finite elements of the actual sign field

These are the real-coordinate prerequisites for `a:eq:st` in
`docs/surcomplex/analysis/article.tex`. Finiteness and infinitesimality are
defined by the native Archimedean valuation, and identified with the
document's natural-number bounds. Mathlib's standard part then supplies a
surjective ordered ring homomorphism from the finite-element valuation ring
to `ℝ`, with the infinitesimals as its kernel, and a unique decomposition
using the already constructed `SignSequence.ofReal` embedding.

This does not identify an Archimedean class with a Hahn exponent or extract
a Hahn coefficient; those identifications require the normal-form bridge.
-/

universe u

namespace Surreal.Foundations.SignSequence

noncomputable section

/-- A sign-field element is finite when its Archimedean valuation is nonnegative. -/
def IsFinite (x : SignSequence.{u}) : Prop := 0 ≤ ArchimedeanClass.mk x

/-- Infinitesimals include zero, whose Archimedean valuation is infinity. -/
def IsInfinitesimal (x : SignSequence.{u}) : Prop := 0 < ArchimedeanClass.mk x

/-- The native valuation ring of finite elements of the actual sign field. -/
abbrev FiniteElement := ArchimedeanClass.FiniteElement SignSequence.{u}

theorem isFinite_iff_exists_nat_abs_le (x : SignSequence.{u}) :
    IsFinite x ↔ ∃ n : ℕ, |x| ≤ n := by
  change ArchimedeanClass.mk (1 : SignSequence.{u}) ≤ ArchimedeanClass.mk x ↔ _
  rw [ArchimedeanClass.mk_le_mk]
  simp

/-- The strict natural bound used in the document's definition of finite elements. -/
theorem isFinite_iff_exists_nat_abs_lt (x : SignSequence.{u}) :
    IsFinite x ↔ ∃ n : ℕ, |x| < n := by
  rw [isFinite_iff_exists_nat_abs_le]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n + 1, hn.trans_lt (by exact_mod_cast Nat.lt_succ_self n)⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, hn.le⟩

/-- The reciprocal-natural bounds used in the document's definition of infinitesimals. -/
theorem isInfinitesimal_iff_forall_nat_abs_lt (x : SignSequence.{u}) :
    IsInfinitesimal x ↔ ∀ n : ℕ, 0 < n → |x| < 1 / (n : SignSequence.{u}) := by
  change ArchimedeanClass.mk (1 : SignSequence.{u}) < ArchimedeanClass.mk x ↔ _
  rw [ArchimedeanClass.mk_lt_mk]
  simp only [abs_one, nsmul_eq_mul]
  constructor
  · intro h n hn
    exact (lt_div_iff₀ (Nat.cast_pos.mpr hn)).mpr (by simpa [mul_comm] using h n)
  · intro h n
    obtain rfl | hn := Nat.eq_zero_or_pos n
    · simp
    · simpa [mul_comm] using (lt_div_iff₀ (Nat.cast_pos.mpr hn)).mp (h n hn)

/-- Equivalently, an infinitesimal is smaller in absolute value than every positive real. -/
theorem isInfinitesimal_iff_forall_real_abs_lt (x : SignSequence.{u}) :
    IsInfinitesimal x ↔ ∀ r : ℝ, 0 < r → |x| < ofReal r := by
  constructor
  · intro hx r hr
    apply ArchimedeanClass.lt_of_pos_of_archimedean ofReal _ hr
    simpa only [IsInfinitesimal, ArchimedeanClass.mk_abs] using hx
  · intro hx
    apply (isInfinitesimal_iff_forall_nat_abs_lt x).mpr
    intro n hn
    simpa only [ofReal_div, ofReal_one, ofReal_natCast] using
      hx (1 / n) (one_div_pos.mpr (Nat.cast_pos.mpr hn))

@[simp] theorem finite_zero : IsFinite (0 : SignSequence.{u}) := by
  simp [IsFinite]

@[simp] theorem finite_one : IsFinite (1 : SignSequence.{u}) := by
  simp [IsFinite]

@[simp] theorem infinitesimal_zero : IsInfinitesimal (0 : SignSequence.{u}) := by
  simp [IsInfinitesimal]

theorem finite_of_infinitesimal {x : SignSequence.{u}} (hx : IsInfinitesimal x) :
    IsFinite x := hx.le

theorem finite_add {x y : SignSequence.{u}} (hx : IsFinite x) (hy : IsFinite y) :
    IsFinite (x + y) :=
  (le_min hx hy).trans (ArchimedeanClass.min_le_mk_add x y)

theorem finite_neg {x : SignSequence.{u}} (hx : IsFinite x) : IsFinite (-x) := by
  simpa only [IsFinite, ArchimedeanClass.mk_neg] using hx

theorem finite_sub {x y : SignSequence.{u}} (hx : IsFinite x) (hy : IsFinite y) :
    IsFinite (x - y) := by
  simpa only [sub_eq_add_neg] using finite_add hx (finite_neg hy)

theorem finite_mul {x y : SignSequence.{u}} (hx : IsFinite x) (hy : IsFinite y) :
    IsFinite (x * y) := by
  simpa only [IsFinite, ArchimedeanClass.mk_mul] using add_nonneg hx hy

theorem finite_ofReal (r : ℝ) : IsFinite (ofReal r : SignSequence.{u}) :=
  ArchimedeanClass.mk_map_nonneg_of_archimedean ofReal r

/-- Mathlib's total standard-part function. Its value on infinite inputs is zero;
the ring-homomorphism statements below always retain finiteness. -/
def standardPart (x : SignSequence.{u}) : ℝ := ArchimedeanClass.stdPart x

@[simp] theorem standardPart_zero : standardPart (0 : SignSequence.{u}) = 0 :=
  ArchimedeanClass.stdPart_zero

@[simp] theorem standardPart_one : standardPart (1 : SignSequence.{u}) = 1 :=
  ArchimedeanClass.stdPart_one

@[simp] theorem standardPart_ofReal (r : ℝ) :
    standardPart (ofReal r : SignSequence.{u}) = r :=
  ArchimedeanClass.stdPart_map_real ofReal r

theorem standardPart_add {x y : SignSequence.{u}} (hx : IsFinite x) (hy : IsFinite y) :
    standardPart (x + y) = standardPart x + standardPart y :=
  ArchimedeanClass.stdPart_add hx hy

@[simp] theorem standardPart_neg (x : SignSequence.{u}) :
    standardPart (-x) = -standardPart x := ArchimedeanClass.stdPart_neg x

theorem standardPart_sub {x y : SignSequence.{u}} (hx : IsFinite x) (hy : IsFinite y) :
    standardPart (x - y) = standardPart x - standardPart y :=
  ArchimedeanClass.stdPart_sub hx hy

theorem standardPart_mul {x y : SignSequence.{u}} (hx : IsFinite x) (hy : IsFinite y) :
    standardPart (x * y) = standardPart x * standardPart y :=
  ArchimedeanClass.stdPart_mul hx hy

theorem standardPart_eq_zero_iff {x : SignSequence.{u}} (hx : IsFinite x) :
    standardPart x = 0 ↔ IsInfinitesimal x := by
  rw [standardPart, ArchimedeanClass.stdPart_eq_zero]
  exact ⟨fun h => lt_of_le_of_ne hx h.symm, fun h => h.ne'⟩

/-- Standard part as an ordered ring homomorphism on its genuine finite domain. -/
def standardPartHom : FiniteElement.{u} →+*o ℝ where
  toFun x := standardPart x.1
  map_zero' := standardPart_zero
  map_one' := standardPart_one
  map_add' x y := standardPart_add x.2 y.2
  map_mul' x y := standardPart_mul x.2 y.2
  monotone' x y h := ArchimedeanClass.stdPart_monotoneOn x.2 y.2 h

@[simp] theorem standardPartHom_apply (x : FiniteElement.{u}) :
    standardPartHom x = standardPart x.1 := rfl

/-- The actual real embedding lands in the finite-element valuation ring. -/
def finiteOfReal : ℝ →+*o FiniteElement.{u} where
  toFun r := ArchimedeanClass.FiniteElement.mk (ofReal r) (finite_ofReal r)
  map_zero' := ArchimedeanClass.FiniteElement.ext ofReal_zero
  map_one' := ArchimedeanClass.FiniteElement.ext ofReal_one
  map_add' r s := ArchimedeanClass.FiniteElement.ext (ofReal_add r s)
  map_mul' r s := ArchimedeanClass.FiniteElement.ext (ofReal_mul r s)
  monotone' _ _ h := ofReal.monotone' h

@[simp] theorem finiteOfReal_val (r : ℝ) :
    (finiteOfReal r : FiniteElement.{u}).1 = ofReal r := rfl

@[simp] theorem standardPartHom_finiteOfReal (r : ℝ) :
    standardPartHom (finiteOfReal r : FiniteElement.{u}) = r := standardPart_ofReal r

theorem standardPartHom_surjective :
    Function.Surjective (standardPartHom : FiniteElement.{u} → ℝ) :=
  fun r => ⟨finiteOfReal r, standardPartHom_finiteOfReal r⟩

/-- The kernel consists exactly of the infinitesimal finite elements. -/
theorem mem_ker_standardPartHom (x : FiniteElement.{u}) :
    x ∈ RingHom.ker standardPartHom.toRingHom ↔ IsInfinitesimal x.1 :=
  standardPart_eq_zero_iff x.2

/-- The ideal of infinitesimals inside the finite-element valuation ring. -/
def infinitesimalIdeal : Ideal FiniteElement.{u} := RingHom.ker standardPartHom.toRingHom

@[simp] theorem mem_infinitesimalIdeal (x : FiniteElement.{u}) :
    x ∈ infinitesimalIdeal ↔ IsInfinitesimal x.1 := mem_ker_standardPartHom x

/-- The infinitesimals form the valuation ring's native maximal ideal. -/
theorem infinitesimalIdeal_eq_maximalIdeal :
    infinitesimalIdeal = IsLocalRing.maximalIdeal FiniteElement.{u} := by
  ext x
  rw [mem_infinitesimalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    ArchimedeanClass.FiniteElement.not_isUnit_iff_mk_pos]
  rfl

/-- The real-coordinate residue-field identification in `a:eq:st`. -/
def standardPartQuotientEquiv : FiniteElement.{u} ⧸ infinitesimalIdeal ≃+* ℝ :=
  RingHom.quotientKerEquivOfSurjective standardPartHom_surjective

/-- A finite element differs infinitesimally from exactly its standard real part. -/
theorem infinitesimal_sub_ofReal_iff {x : SignSequence.{u}} (hx : IsFinite x) {r : ℝ} :
    IsInfinitesimal (x - ofReal r) ↔ standardPart x = r :=
  ArchimedeanClass.mk_sub_pos_iff ofReal hx

theorem infinitesimal_sub_standardPart {x : SignSequence.{u}} (hx : IsFinite x) :
    IsInfinitesimal (x - ofReal (standardPart x)) :=
  (infinitesimal_sub_ofReal_iff hx).mpr rfl

theorem existsUnique_real_part {x : SignSequence.{u}} (hx : IsFinite x) :
    ∃! r : ℝ, IsInfinitesimal (x - ofReal r) := by
  refine ⟨standardPart x, infinitesimal_sub_standardPart hx, ?_⟩
  intro r hr
  exact ((infinitesimal_sub_ofReal_iff hx).mp hr).symm

/-- The explicit real-plus-infinitesimal decomposition, including uniqueness of both parts. -/
theorem existsUnique_real_infinitesimal_decomposition {x : SignSequence.{u}} (hx : IsFinite x) :
    ∃! p : ℝ × SignSequence.{u}, IsInfinitesimal p.2 ∧ x = ofReal p.1 + p.2 := by
  refine ⟨⟨standardPart x, x - ofReal (standardPart x)⟩,
    ⟨infinitesimal_sub_standardPart hx, by simp⟩, ?_⟩
  rintro ⟨r, ε⟩ ⟨hε, hxε⟩
  have heq : x - ofReal r = ε := by rw [hxε]; simp
  have hr : standardPart x = r := (infinitesimal_sub_ofReal_iff hx).mp (heq ▸ hε)
  exact Prod.ext hr.symm (by simpa only [hr] using heq.symm)

end

end Surreal.Foundations.SignSequence
