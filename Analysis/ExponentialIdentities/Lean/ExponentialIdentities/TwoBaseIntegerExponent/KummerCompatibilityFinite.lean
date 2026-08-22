import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Exact finite compatibility counts

This file isolates the finite linear algebra behind a two-coordinate Kummer
compatibility condition.  A datum is a pair `(u, v)` of vectors in `F^2`, and
it is compatible when `v = t u` for some scalar `t`.

There are exactly `q^3 - q + 1` compatible data over a finite field of size
`q`.  Intersecting them with a hyperplane whose two coefficient rows have
nonzero determinant leaves exactly `q^2 - q + 1` data.  Both counts are proved
by explicit equivalences, with no distribution or realization hypothesis.
-/

namespace LeanProofs.TwoBaseIntegerExponent
namespace KummerCompatibilityFinite

/-- A two-coordinate vector over `F`. -/
abbrev Vec2 (F : Type*) := F × F

/-- A source/target pair `(u, v)` of two-coordinate vectors. -/
abbrev Datum (F : Type*) := Vec2 F × Vec2 F

variable {F : Type*} [Field F]

/-- Coordinatewise scalar multiplication on `F^2`. -/
def scalarVec (t : F) (u : Vec2 F) : Vec2 F :=
  (t * u.1, t * u.2)

/-- Compatibility with a specified scalar. -/
def FixedCompatible (t : F) (z : Datum F) : Prop :=
  z.2 = scalarVec t z.1

/-- A datum is compatible when its target is a scalar multiple of its source. -/
def Compatible (z : Datum F) : Prop :=
  ∃ t : F, FixedCompatible t z

/-- The finite type whose cardinality is the unrestricted compatibility count. -/
abbrev CompatibleDatum (F : Type*) [Field F] := {z : Datum F // Compatible z}

/-- Nonzero source vectors. -/
abbrev NonzeroVec2 (F : Type*) [Zero F] := {u : Vec2 F // u ≠ 0}

/-- Nonzero scalar parameters. -/
abbrev NonzeroScalar (F : Type*) [Zero F] := {s : F // s ≠ 0}

theorem compatible_iff_exists_fixed (z : Datum F) :
    Compatible z ↔ ∃ t : F, FixedCompatible t z :=
  Iff.rfl

@[simp] theorem scalarVec_zero (t : F) : scalarVec t (0 : Vec2 F) = 0 := by
  simp [scalarVec]

@[simp] theorem compatible_zero_source_iff (v : Vec2 F) :
    Compatible ((0 : Vec2 F), v) ↔ v = 0 := by
  constructor
  · rintro ⟨t, ht⟩
    simpa [FixedCompatible] using ht
  · rintro rfl
    exact ⟨0, by simp [FixedCompatible]⟩

/-- A nonzero source determines its compatibility scalar uniquely. -/
theorem scalarVec_scalar_unique {u : Vec2 F} (hu : u ≠ 0) {s t : F}
    (h : scalarVec s u = scalarVec t u) : s = t := by
  have hcoord : u.1 ≠ 0 ∨ u.2 ≠ 0 := by
    by_contra h'
    push Not at h'
    apply hu
    exact Prod.ext h'.1 h'.2
  rcases hcoord with hfst | hsnd
  · exact mul_right_cancel₀ hfst (congrArg Prod.fst h)
  · exact mul_right_cancel₀ hsnd (congrArg Prod.snd h)

theorem compatible_scalar_unique {z : Datum F} (hu : z.1 ≠ 0) {s t : F}
    (hs : FixedCompatible s z) (ht : FixedCompatible t z) : s = t :=
  scalarVec_scalar_unique hu (hs.symm.trans ht)

private noncomputable def compatibleScalar (z : CompatibleDatum F) : F :=
  Classical.choose z.property

private theorem compatibleScalar_spec (z : CompatibleDatum F) :
    z.1.2 = scalarVec (compatibleScalar z) z.1.1 :=
  Classical.choose_spec z.property

/-- Compatible data split into the zero datum and a unique scalar above each
nonzero source. -/
noncomputable def compatibleEquiv :
    CompatibleDatum F ≃ Unit ⊕ (NonzeroVec2 F × F) := by
  classical
  refine
    { toFun := fun z =>
        if hu : z.1.1 = 0 then Sum.inl ()
        else Sum.inr (⟨z.1.1, hu⟩, compatibleScalar z)
      invFun := fun y => match y with
        | Sum.inl _ =>
            ⟨((0 : Vec2 F), (0 : Vec2 F)), ⟨0, by simp [FixedCompatible]⟩⟩
        | Sum.inr p =>
            ⟨(p.1.1, scalarVec p.2 p.1.1), ⟨p.2, rfl⟩⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro z
    apply Subtype.ext
    by_cases hu : z.1.1 = 0
    · simp only [hu, dite_true]
      have hv : z.1.2 = 0 := by
        rw [compatibleScalar_spec z, hu, scalarVec_zero]
      exact Prod.ext hu.symm hv.symm
    · simp only [hu, dite_false]
      exact Prod.ext rfl (compatibleScalar_spec z).symm
  · intro y
    rcases y with _ | ⟨u, t⟩
    · simp
    · have hu : u.1 ≠ 0 := u.2
      simp only [hu, dite_false, Sum.inr.injEq, Prod.mk.injEq, true_and]
      apply scalarVec_scalar_unique hu
      exact (compatibleScalar_spec
        ⟨(u.1, scalarVec t u.1), ⟨t, rfl⟩⟩).symm

/-- Membership in the hyperplane with coefficient rows `(rho.1, rho.2)`. -/
def InHyperplane (rho z : Datum F) : Prop :=
  rho.1.1 * z.1.1 + rho.1.2 * z.1.2 +
    rho.2.1 * z.2.1 + rho.2.2 * z.2.2 = 0

/-- The hyperplane is transverse when its two coefficient rows are independent. -/
def Transverse (rho : Datum F) : Prop :=
  rho.1.1 * rho.2.2 - rho.1.2 * rho.2.1 ≠ 0

/-- The source linear form left after substituting `v = t u`. -/
def sourceForm (rho : Datum F) (t : F) (u : Vec2 F) : F :=
  (rho.1.1 + t * rho.2.1) * u.1 +
    (rho.1.2 + t * rho.2.2) * u.2

theorem inHyperplane_fixedCompatible_iff (rho : Datum F) (t : F) (u : Vec2 F) :
    InHyperplane rho (u, scalarVec t u) ↔ sourceForm rho t u = 0 := by
  simp only [InHyperplane, scalarVec, sourceForm]
  constructor <;> intro h
  · linear_combination h
  · linear_combination h

/-- Transversality makes the substituted source form nonzero for every scalar. -/
theorem sourceCoefficients_ne_zero {rho : Datum F} (hrho : Transverse rho) (t : F) :
    (rho.1.1 + t * rho.2.1, rho.1.2 + t * rho.2.2) ≠ 0 := by
  intro h
  have h₁ : rho.1.1 + t * rho.2.1 = 0 := congrArg Prod.fst h
  have h₂ : rho.1.2 + t * rho.2.2 = 0 := congrArg Prod.snd h
  apply hrho
  linear_combination h₁ * rho.2.2 - h₂ * rho.2.1

/-- A canonical parametrization of the kernel of `sourceForm rho t`. -/
def kernelVec (rho : Datum F) (t s : F) : Vec2 F :=
  ((rho.1.2 + t * rho.2.2) * s, -(rho.1.1 + t * rho.2.1) * s)

@[simp] theorem sourceForm_kernelVec (rho : Datum F) (t s : F) :
    sourceForm rho t (kernelVec rho t s) = 0 := by
  simp only [sourceForm, kernelVec]
  ring

theorem kernelVec_injective {rho : Datum F} (hrho : Transverse rho) (t : F) :
    Function.Injective (kernelVec rho t) := by
  intro s₁ s₂ h
  have hcoeff := sourceCoefficients_ne_zero hrho t
  have hcoord :
      rho.1.1 + t * rho.2.1 ≠ 0 ∨ rho.1.2 + t * rho.2.2 ≠ 0 := by
    by_contra h'
    push Not at h'
    exact hcoeff (Prod.ext h'.1 h'.2)
  rcases hcoord with hfirst | hsecond
  · have hsnd := congrArg Prod.snd h
    simp only [kernelVec, neg_mul] at hsnd
    have hsnd' :
        (rho.1.1 + t * rho.2.1) * s₁ =
          (rho.1.1 + t * rho.2.1) * s₂ :=
      neg_injective hsnd
    exact mul_left_cancel₀ hfirst hsnd'
  · exact mul_left_cancel₀ hsecond (congrArg Prod.fst h)

theorem exists_kernelParameter {rho : Datum F} (hrho : Transverse rho)
    (t : F) {u : Vec2 F} (hu : sourceForm rho t u = 0) :
    ∃ s : F, kernelVec rho t s = u := by
  have hcoord := sourceCoefficients_ne_zero hrho t
  by_cases hsecond : rho.1.2 + t * rho.2.2 = 0
  · have hfirst : rho.1.1 + t * rho.2.1 ≠ 0 := by
      intro hzero
      exact hcoord (Prod.ext hzero hsecond)
    refine ⟨-u.2 / (rho.1.1 + t * rho.2.1), Prod.ext ?_ ?_⟩
    · simp only [kernelVec, hsecond, zero_mul]
      have hform : (rho.1.1 + t * rho.2.1) * u.1 = 0 := by
        simpa [sourceForm, hsecond] using hu
      exact ((mul_eq_zero.mp hform).resolve_left hfirst).symm
    · simp only [kernelVec]
      field_simp
  · refine ⟨u.1 / (rho.1.2 + t * rho.2.2), Prod.ext ?_ ?_⟩
    · simp only [kernelVec]
      field_simp
    · simp only [kernelVec]
      field_simp [hsecond]
      rw [sourceForm] at hu
      linear_combination -hu

/-- Compatible data lying in the hyperplane `rho`. -/
abbrev HyperplaneCompatibleDatum (rho : Datum F) :=
  {z : Datum F // Compatible z ∧ InHyperplane rho z}

private def asCompatible {rho : Datum F} (z : HyperplaneCompatibleDatum rho) :
    CompatibleDatum F :=
  ⟨z.1, z.2.1⟩

private noncomputable def transverseScalar {rho : Datum F}
    (z : HyperplaneCompatibleDatum rho) : F :=
  compatibleScalar (asCompatible z)

private theorem transverseScalar_spec {rho : Datum F}
    (z : HyperplaneCompatibleDatum rho) :
    z.1.2 = scalarVec (transverseScalar z) z.1.1 :=
  compatibleScalar_spec (asCompatible z)

private theorem transverseScalar_sourceForm {rho : Datum F}
    (z : HyperplaneCompatibleDatum rho) :
    sourceForm rho (transverseScalar z) z.1.1 = 0 := by
  apply (inHyperplane_fixedCompatible_iff rho (transverseScalar z) z.1.1).mp
  rw [← transverseScalar_spec z]
  exact z.2.2

private noncomputable def transverseKernelParameter {rho : Datum F}
    (hrho : Transverse rho) (z : HyperplaneCompatibleDatum rho) : F :=
  Classical.choose (exists_kernelParameter hrho (transverseScalar z)
    (transverseScalar_sourceForm z))

private theorem transverseKernelParameter_spec {rho : Datum F}
    (hrho : Transverse rho) (z : HyperplaneCompatibleDatum rho) :
    kernelVec rho (transverseScalar z) (transverseKernelParameter hrho z) = z.1.1 :=
  Classical.choose_spec (exists_kernelParameter hrho (transverseScalar z)
    (transverseScalar_sourceForm z))

private theorem transverseKernelParameter_ne_zero {rho : Datum F}
    (hrho : Transverse rho) (z : HyperplaneCompatibleDatum rho) (hz : z.1.1 ≠ 0) :
    transverseKernelParameter hrho z ≠ 0 := by
  intro hs
  apply hz
  rw [← transverseKernelParameter_spec hrho z, hs]
  simp [kernelVec]

/-- Under transversality, the hyperplane-compatible data split into the zero
datum and a nonzero kernel parameter for each compatibility scalar. -/
noncomputable def transverseCompatibleEquiv {rho : Datum F} (hrho : Transverse rho) :
    HyperplaneCompatibleDatum rho ≃ Unit ⊕ (F × NonzeroScalar F) := by
  classical
  refine
    { toFun := fun z =>
        if hz : z.1.1 = 0 then Sum.inl ()
        else Sum.inr
          (transverseScalar z, ⟨transverseKernelParameter hrho z,
            transverseKernelParameter_ne_zero hrho z hz⟩)
      invFun := fun y => match y with
        | Sum.inl _ =>
            ⟨((0 : Vec2 F), (0 : Vec2 F)),
              ⟨⟨0, by simp [FixedCompatible]⟩, by simp [InHyperplane]⟩⟩
        | Sum.inr p =>
            let u := kernelVec rho p.1 p.2.1
            ⟨(u, scalarVec p.1 u),
              ⟨⟨p.1, rfl⟩,
                (inHyperplane_fixedCompatible_iff rho p.1 u).mpr
                  (sourceForm_kernelVec rho p.1 p.2.1)⟩⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro z
    apply Subtype.ext
    by_cases hz : z.1.1 = 0
    · simp only [hz, dite_true]
      have hv : z.1.2 = 0 := by
        rw [transverseScalar_spec z, hz, scalarVec_zero]
      exact Prod.ext hz.symm hv.symm
    · simp only [hz, dite_false]
      apply Prod.ext
      · exact transverseKernelParameter_spec hrho z
      · calc
          scalarVec (transverseScalar z)
              (kernelVec rho (transverseScalar z) (transverseKernelParameter hrho z)) =
              scalarVec (transverseScalar z) z.1.1 :=
                congrArg (scalarVec (transverseScalar z))
                  (transverseKernelParameter_spec hrho z)
          _ = z.1.2 := (transverseScalar_spec z).symm
  · intro y
    rcases y with _ | ⟨t, s⟩
    · simp
    · let u := kernelVec rho t s.1
      have hu : u ≠ 0 := by
        intro huzero
        have heq : kernelVec rho t s.1 = kernelVec rho t 0 := by
          simpa [u, kernelVec] using huzero
        exact s.2 (kernelVec_injective hrho t heq)
      let z : HyperplaneCompatibleDatum rho :=
        ⟨(u, scalarVec t u),
          ⟨⟨t, rfl⟩,
            (inHyperplane_fixedCompatible_iff rho t u).mpr
              (sourceForm_kernelVec rho t s.1)⟩⟩
      have ht : transverseScalar z = t := by
        apply scalarVec_scalar_unique hu
        exact (transverseScalar_spec z).symm
      have hs : transverseKernelParameter hrho z = s.1 := by
        apply kernelVec_injective hrho t
        have hparam := transverseKernelParameter_spec hrho z
        rw [ht] at hparam
        simpa [u] using hparam
      have hz : z.1.1 ≠ 0 := hu
      change (if hz : z.1.1 = 0 then Sum.inl () else
        Sum.inr (transverseScalar z,
          ⟨transverseKernelParameter hrho z,
            transverseKernelParameter_ne_zero hrho z hz⟩)) = Sum.inr (t, s)
      rw [dif_neg hz]
      apply congrArg Sum.inr
      apply Prod.ext ht
      exact Subtype.ext hs

section Cardinalities

variable [Fintype F]

noncomputable instance : Fintype (CompatibleDatum F) :=
  Fintype.ofFinite _

noncomputable instance : Fintype (NonzeroVec2 F) :=
  Fintype.ofFinite _

noncomputable instance : Fintype (NonzeroScalar F) :=
  Fintype.ofFinite _

noncomputable instance (rho : Datum F) : Fintype (HyperplaneCompatibleDatum rho) :=
  Fintype.ofFinite _

theorem card_nonzero_vec2 :
    Fintype.card (NonzeroVec2 F) = Fintype.card F ^ 2 - 1 := by
  classical
  letI : Fintype {u : Vec2 F // u = 0} := Fintype.ofFinite _
  rw [Fintype.card_subtype_compl (fun u : Vec2 F => u = 0)]
  have hone : Fintype.card {u : Vec2 F // u = 0} = 1 := by
    rw [Fintype.card_eq_one_iff]
    exact ⟨⟨0, rfl⟩, fun y => Subtype.ext y.2⟩
  rw [hone, Fintype.card_prod]
  simp [pow_two]

/-- Exact unrestricted compatibility count over any finite field. -/
theorem card_compatible :
    Fintype.card (CompatibleDatum F) =
      Fintype.card F ^ 3 - Fintype.card F + 1 := by
  rw [Fintype.card_congr compatibleEquiv, Fintype.card_sum,
    Fintype.card_unique, Fintype.card_prod, card_nonzero_vec2]
  have hq : 0 < Fintype.card F := Fintype.card_pos
  rw [Nat.sub_mul]
  rw [show Fintype.card F ^ 2 * Fintype.card F = Fintype.card F ^ 3 by ring]
  omega

theorem card_nonzero_scalar :
    Fintype.card (NonzeroScalar F) = Fintype.card F - 1 := by
  classical
  letI : Fintype {s : F // s = 0} := Fintype.ofFinite _
  rw [Fintype.card_subtype_compl (fun s : F => s = 0)]
  have hone : Fintype.card {s : F // s = 0} = 1 := by
    rw [Fintype.card_eq_one_iff]
    exact ⟨⟨0, rfl⟩, fun y => Subtype.ext y.2⟩
  rw [hone]

/-- Exact compatible count in a transverse hyperplane over any finite field. -/
theorem card_transverse_compatible {rho : Datum F} (hrho : Transverse rho) :
    Fintype.card (HyperplaneCompatibleDatum rho) =
      Fintype.card F ^ 2 - Fintype.card F + 1 := by
  rw [Fintype.card_congr (transverseCompatibleEquiv hrho), Fintype.card_sum,
    Fintype.card_unique, Fintype.card_prod, card_nonzero_scalar]
  rw [Nat.mul_sub_left_distrib]
  rw [show Fintype.card F * Fintype.card F = Fintype.card F ^ 2 by ring]
  have hq : 0 < Fintype.card F := Fintype.card_pos
  omega

end Cardinalities

/-- Exact compatibility count over the prime field `ZMod p`. -/
theorem card_compatible_zmod (p : ℕ) [Fact p.Prime] :
    Fintype.card (CompatibleDatum (ZMod p)) = p ^ 3 - p + 1 := by
  simpa only [ZMod.card] using (card_compatible (F := ZMod p))

/-- Exact transverse-hyperplane compatibility count over `ZMod p`. -/
theorem card_transverse_compatible_zmod (p : ℕ) [Fact p.Prime]
    {rho : Datum (ZMod p)} (hrho : Transverse rho) :
    Fintype.card (HyperplaneCompatibleDatum rho) = p ^ 2 - p + 1 := by
  simpa only [ZMod.card] using
    (card_transverse_compatible (F := ZMod p) hrho)

end KummerCompatibilityFinite
end LeanProofs.TwoBaseIntegerExponent
