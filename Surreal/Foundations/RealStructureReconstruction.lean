import Surreal.Surcomplex.MultiplierFormulas
import Surreal.Foundations.SignSequenceRealClosed

/-!
# Reconstruction of the actual real structure from the omnific ring

The literal formulas of `odg:def:thm:realrecovery`. The ambient field
is already the proved fraction field of the actual omnific ring.
Only its field operations and the fraction-pair coefficient predicate
occur in the new definitions; their meanings are proved below.
-/

universe u
namespace Surreal.Foundations.SignSequence.RealReconstruction

noncomputable section

/-- The real coefficient predicate interpreted from omnific fraction pairs. -/
def Coefficient (x : SignSequence.{u}) : Prop :=
  ∃ a b : OmnificInteger.{u}, IdealReconstruction.Coeff a b ∧
    x = omnificToSurreal a / omnificToSurreal b

/-- Positivity defined using only a nonzero square in the interpreted field. -/
def Positive (x : SignSequence.{u}) : Prop := x ≠ 0 ∧ ∃ z : SignSequence.{u}, z ^ 2 = x

/-- Strict order in the ring language of the interpreted field. -/
def Less (x y : SignSequence.{u}) : Prop := Positive (y - x)

/-- Nonstrict order obtained from equality and the strict-order formula. -/
def AtMost (x y : SignSequence.{u}) : Prop := x = y ∨ Less x y

/-- The source's finite-element formula, bounded by a positive reconstructed real. -/
def Finite (x : SignSequence.{u}) : Prop :=
  ∃ r : SignSequence.{u}, Coefficient r ∧ Positive r ∧ AtMost (-r) x ∧ AtMost x r

/-- The source's infinitesimal formula, including zero. -/
def Infinitesimal (x : SignSequence.{u}) : Prop :=
  ∀ r : SignSequence.{u}, Coefficient r → Positive r → Less (-r) x ∧ Less x r

/-- Standard part reconstructed as the real coefficient infinitely close to a finite input. -/
def StandardPartGraph (x r : SignSequence.{u}) : Prop :=
  Finite x ∧ Coefficient r ∧ Infinitesimal (x - r)

/-- The interpreted coefficient predicate picks out the actual embedded reals. -/
theorem coefficient_iff (x : SignSequence.{u}) : Coefficient x ↔ ∃ r : ℝ, x = ofReal r := by
  constructor
  · rintro ⟨a, b, hc, rfl⟩
    exact ((omnific_coefficientFormula_iff a b).mp hc).2
  · intro hx
    obtain ⟨a, b, _, _, hb, he⟩ := surreal_eq_omnific_fraction x
    refine ⟨a, b, (omnific_coefficientFormula_iff a b).mpr ⟨hb, ?_⟩, he⟩
    rwa [← he]

/-- The positive-square formula agrees with the actual order, including exclusion of zero. -/
theorem positive_iff (x : SignSequence.{u}) : Positive x ↔ 0 < x := by
  constructor
  · rintro ⟨hx, z, rfl⟩
    exact lt_of_le_of_ne (sq_nonneg z) hx.symm
  · intro hx
    exact ⟨ne_of_gt hx, sqrt x, by simpa only [pow_two] using sqrt_sq hx.le⟩

theorem less_iff (x y : SignSequence.{u}) : Less x y ↔ x < y := by
  rw [Less, positive_iff, sub_pos]

theorem atMost_iff (x y : SignSequence.{u}) : AtMost x y ↔ x ≤ y := by
  rw [AtMost, less_iff]
  exact ⟨fun h => h.elim le_of_eq le_of_lt, fun h => (eq_or_lt_of_le h)⟩

private theorem finite_iff_real_bound (x : SignSequence.{u}) :
    IsFinite x ↔ ∃ r : ℝ, 0 < r ∧ |x| ≤ ofReal r := by
  rw [isFinite_iff_exists_nat_abs_le]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨(n : ℝ) + 1, by positivity, ?_⟩
    rw [map_add, ofReal_natCast, map_one]
    exact hn.trans (le_add_of_nonneg_right zero_le_one)
  · rintro ⟨r, _, hr⟩
    obtain ⟨n, hn⟩ := exists_nat_gt r
    refine ⟨n, hr.trans ?_⟩
    simpa only [ofReal_natCast] using ((ofReal_lt_iff r n).mpr hn).le

/-- Reconstructed finiteness is the existing native valuation-ring predicate. -/
theorem finite_iff (x : SignSequence.{u}) : Finite x ↔ IsFinite x := by
  simp only [Finite, coefficient_iff, positive_iff, atMost_iff]
  rw [finite_iff_real_bound]
  constructor
  · rintro ⟨_, ⟨r, rfl⟩, hr, hl, hu⟩
    refine ⟨r, ?_, abs_le.mpr ⟨hl, hu⟩⟩
    exact (ofReal_lt_iff 0 r).mp (by simpa only [map_zero] using hr)
  · rintro ⟨r, hr, hx⟩
    refine ⟨ofReal r, ⟨r, rfl⟩, ?_, (abs_le.mp hx).1, (abs_le.mp hx).2⟩
    simpa only [map_zero] using (ofReal_lt_iff 0 r).mpr hr

/-- Reconstructed infinitesimality agrees with the existing native maximal-ideal predicate. -/
theorem infinitesimal_iff (x : SignSequence.{u}) : Infinitesimal x ↔ IsInfinitesimal x := by
  simp only [Infinitesimal, coefficient_iff, positive_iff, less_iff]
  rw [isInfinitesimal_iff_forall_real_abs_lt]
  constructor
  · intro h r hr
    apply abs_lt.mpr
    exact h (ofReal r) ⟨r, rfl⟩ (by simpa only [map_zero] using (ofReal_lt_iff 0 r).mpr hr)
  · rintro h _ ⟨r, rfl⟩ hr
    apply abs_lt.mp
    apply h r
    exact (ofReal_lt_iff 0 r).mp (by simpa only [map_zero] using hr)

/-- The literal graph formula defines the actual standard-part map, with a field-valued output. -/
theorem standardPartGraph_iff (x r : SignSequence.{u}) :
    StandardPartGraph x r ↔ IsFinite x ∧ r = ofReal (standardPart x) := by
  rw [StandardPartGraph, finite_iff, coefficient_iff, infinitesimal_iff]
  constructor
  · rintro ⟨hx, ⟨c, rfl⟩, hc⟩
    exact ⟨hx, congrArg ofReal ((infinitesimal_sub_ofReal_iff hx).mp hc).symm⟩
  · rintro ⟨hx, rfl⟩
    exact ⟨hx, ⟨standardPart x, rfl⟩, infinitesimal_sub_standardPart hx⟩

/-- Every finite input has exactly one output satisfying the reconstructed graph. -/
theorem standardPartGraph_existsUnique (x : SignSequence.{u}) (hx : IsFinite x) :
    ∃! r : SignSequence.{u}, StandardPartGraph x r :=
  ⟨ofReal (standardPart x), (standardPartGraph_iff x _).mpr ⟨hx, rfl⟩,
    fun r hr => ((standardPartGraph_iff x r).mp hr).2⟩

/-- The graph has an output exactly on the finite ring; no standard part is assigned to infinity. -/
theorem exists_standardPartGraph_iff (x : SignSequence.{u}) :
    (∃ r : SignSequence.{u}, StandardPartGraph x r) ↔ Finite x := by
  rw [finite_iff]
  exact ⟨fun ⟨r, hr⟩ => ((standardPartGraph_iff x r).mp hr).1,
    fun hx => (standardPartGraph_existsUnique x hx).exists⟩

/-- The printed support-ring example has constant term seven. -/
theorem constantTerm_omega_add_seven :
    omnificConstantCoeff (omnificMonomial (1 : SignSequence.{u}) zero_lt_one + 7) = 7 := by
  have h : omnificConstantCoeff (omnificMonomial (1 : SignSequence.{u}) zero_lt_one) = 0 :=
    omnificMonomial_mem_purelyInfinite _ _
  simp [map_add, map_ofNat, h]

/-- The input of that constant-term example is outside the finite ring. -/
theorem omega_add_seven_not_finite : ¬ Finite (omegaPower (1 : SignSequence.{u}) + 7) := by
  rw [finite_iff]
  intro hx
  have h := abs_lt_omegaPower_one_of_finite hx
  have hle : omegaPower (1 : SignSequence.{u}) ≤ |omegaPower 1 + 7| :=
    (by linarith : omegaPower (1 : SignSequence.{u}) ≤ omegaPower 1 + 7).trans (le_abs_self _)
  exact (not_lt_of_ge hle) h

/-- The reciprocal monomial gives the printed standard-part example, with output seven. -/
theorem standardPartGraph_seven_add_inv_omega :
    StandardPartGraph (7 + (omegaPower (1 : SignSequence.{u}))⁻¹) 7 := by
  have hi : IsInfinitesimal ((omegaPower (1 : SignSequence.{u}))⁻¹) := by
    rw [← omegaPower_neg, isInfinitesimal_iff_valuation_pos, valuation_omegaPower]
    norm_num
  have hf : IsFinite (7 + (omegaPower (1 : SignSequence.{u}))⁻¹) :=
    finite_add (by simpa only [map_ofNat] using finite_ofReal (7 : ℝ)) (finite_of_infinitesimal hi)
  rw [standardPartGraph_iff]
  refine ⟨hf, ?_⟩
  have hs : standardPart (7 + (omegaPower (1 : SignSequence.{u}))⁻¹) = 7 :=
    (infinitesimal_sub_ofReal_iff hf).mp (by
      simpa only [map_ofNat, _root_.add_sub_cancel_left] using hi)
  simp only [hs, map_ofNat]

end
end Surreal.Foundations.SignSequence.RealReconstruction
