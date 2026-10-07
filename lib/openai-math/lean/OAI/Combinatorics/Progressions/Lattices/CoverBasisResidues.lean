import Mathlib.GroupTheory.QuotientGroup.Basic
import OAI.Combinatorics.Progressions.Estimates.LinearQuotientCoverAverage
import OAI.Combinatorics.Progressions.Lattices.ResidueRefinedPeriod

namespace OAI

section

namespace Erdos3

variable {E : Type*} [AddCommGroup E] [Module ℝ E] (Γ : AddSubgroup E)

noncomputable def coverLatticePoint (d : ℕ) (hd : 0 < d) :
    Γ →+ (quotientIntegerCover Γ d).ker where
  toFun x := ⟨QuotientAddGroup.mk' Γ ((d : ℝ)⁻¹ • x.val), by
    change quotientIntegerCover Γ d (QuotientAddGroup.mk' Γ _) = 0
    rw [quotientIntegerCover_mk, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hd.ne'), one_smul]
    exact (QuotientAddGroup.eq_zero_iff _).mpr x.property⟩
  map_zero' := by apply Subtype.ext; simp
  map_add' x y := by apply Subtype.ext; simp [smul_add]

theorem coverLatticePoint_val (d : ℕ) (hd : 0 < d) (x : Γ) :
    (coverLatticePoint Γ d hd x).val =
      QuotientAddGroup.mk' Γ ((d : ℝ)⁻¹ • x.val) := rfl

theorem coverLatticePoint_surjective (d : ℕ) (hd : 0 < d) :
    Function.Surjective (coverLatticePoint Γ d hd) := by
  intro y
  obtain ⟨x, hx⟩ := QuotientAddGroup.mk'_surjective Γ y.val
  have hxΓ : (d : ℝ) • x ∈ Γ := by
    apply (QuotientAddGroup.eq_zero_iff _).mp
    change QuotientAddGroup.mk' Γ ((d : ℝ) • x) = 0
    rw [← quotientIntegerCover_mk, hx]
    exact y.property
  refine ⟨⟨(d : ℝ) • x, hxΓ⟩, ?_⟩
  apply Subtype.ext
  rw [coverLatticePoint_val, smul_smul,
    inv_mul_cancel₀ (by exact_mod_cast hd.ne'), one_smul]
  exact hx

theorem coverLatticePoint_ker (d : ℕ) (hd : 0 < d) :
    (coverLatticePoint Γ d hd).ker = (nsmulAddMonoidHom (α := Γ) d).range := by
  ext x
  constructor
  · intro hx
    have he : QuotientAddGroup.mk' Γ ((d : ℝ)⁻¹ • x.val) = 0 :=
      congrArg Subtype.val hx
    have hΓ := (QuotientAddGroup.eq_zero_iff _).mp he
    refine ⟨⟨(d : ℝ)⁻¹ • x.val, hΓ⟩, ?_⟩
    apply Subtype.ext
    change d • ((d : ℝ)⁻¹ • x.val) = x.val
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
      mul_inv_cancel₀ (by exact_mod_cast hd.ne'), one_smul]
  · rintro ⟨y, rfl⟩
    change coverLatticePoint Γ d hd (d • y) = 0
    apply Subtype.ext
    rw [coverLatticePoint_val]
    change QuotientAddGroup.mk' Γ ((d : ℝ)⁻¹ • (d • y.val)) = 0
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
      inv_mul_cancel₀ (by exact_mod_cast hd.ne'), one_smul]
    exact (QuotientAddGroup.eq_zero_iff _).mpr y.property

abbrev CoverLatticeResidue (d : ℕ) := Γ ⧸ (nsmulAddMonoidHom (α := Γ) d).range

noncomputable def coverLatticeResidueEquiv (d : ℕ) (hd : 0 < d) :
    CoverLatticeResidue Γ d ≃+ (quotientIntegerCover Γ d).ker :=
  (QuotientAddGroup.quotientAddEquivOfEq (coverLatticePoint_ker Γ d hd)).symm.trans
    (QuotientAddGroup.quotientKerEquivOfSurjective (coverLatticePoint Γ d hd)
      (coverLatticePoint_surjective Γ d hd))

theorem coverLatticeResidueEquiv_mk (d : ℕ) (hd : 0 < d) (x : Γ) :
    coverLatticeResidueEquiv Γ d hd (QuotientAddGroup.mk' _ x) =
      coverLatticePoint Γ d hd x := rfl

end Erdos3

end

section

namespace Erdos3

open Module

variable {E I : Type*} [AddCommGroup E] [Module ℝ E] [Fintype I]
variable (Γ : AddSubgroup E) (b : Basis I ℤ Γ)

noncomputable def latticeBasisResidue (d : ℕ) : Γ →+ (I → ZMod d) :=
  (integerResidueMap I d).toAddMonoidHom.comp b.equivFun.toAddMonoidHom

omit [Module ℝ E] in
theorem latticeBasisResidue_surjective (d : ℕ) :
    Function.Surjective (latticeBasisResidue Γ b d) :=
  (integerResidueMap_surjective I d).comp b.equivFun.surjective

omit [Module ℝ E] in
theorem latticeBasisResidue_ker (d : ℕ) :
    (latticeBasisResidue Γ b d).ker = (nsmulAddMonoidHom (α := Γ) d).range := by
  ext x
  constructor
  · intro hx
    have hz : b.equivFun x ∈ integerScalarLattice I (d : ℤ) := by
      rw [← integerResidueMap_ker]
      exact hx
    obtain ⟨z, hz⟩ := (integerScalarLattice_mem _ _).mp hz
    refine ⟨b.equivFun.symm z, ?_⟩
    apply b.equivFun.injective
    change b.equivFun (d • b.equivFun.symm z) = b.equivFun x
    rw [map_nsmul, LinearEquiv.apply_symm_apply]
    simpa only [natCast_zsmul] using hz
  · rintro ⟨y, rfl⟩
    change integerResidueMap I d (b.equivFun (d • y)) = 0
    have hz : b.equivFun (d • y) ∈ integerScalarLattice I (d : ℤ) := by
      apply (integerScalarLattice_mem _ _).mpr
      exact ⟨b.equivFun y, by simp only [map_nsmul, natCast_zsmul]⟩
    rw [← integerResidueMap_ker] at hz
    exact hz

noncomputable def coverLatticeBasisEquiv (d : ℕ) :
    CoverLatticeResidue Γ d ≃+ (I → ZMod d) :=
  (QuotientAddGroup.quotientAddEquivOfEq (latticeBasisResidue_ker Γ b d)).symm.trans
    (QuotientAddGroup.quotientKerEquivOfSurjective (latticeBasisResidue Γ b d)
      (latticeBasisResidue_surjective Γ b d))

omit [Module ℝ E] in
theorem coverLatticeBasisEquiv_mk (d : ℕ) (x : Γ) :
    coverLatticeBasisEquiv Γ b d (QuotientAddGroup.mk' _ x) =
      latticeBasisResidue Γ b d x := rfl

noncomputable def coverKernelBasisEquiv (d : ℕ) (hd : 0 < d) :
    (I → ZMod d) ≃+ (quotientIntegerCover Γ d).ker :=
  (coverLatticeBasisEquiv Γ b d).symm.trans (coverLatticeResidueEquiv Γ d hd)

theorem coverKernelBasisEquiv_residue (d : ℕ) (hd : 0 < d) (x : Γ) :
    coverKernelBasisEquiv Γ b d hd (latticeBasisResidue Γ b d x) =
      coverLatticePoint Γ d hd x := by
  rw [← coverLatticeBasisEquiv_mk]
  simp only [coverKernelBasisEquiv, AddEquiv.trans_apply, AddEquiv.symm_apply_apply]
  exact coverLatticeResidueEquiv_mk Γ d hd x

include b in
theorem coverKernel_card (d : ℕ) (hd : 0 < d) :
    Nat.card (quotientIntegerCover Γ d).ker = d ^ Fintype.card I := by
  calc
    _ = Nat.card (I → ZMod d) := Nat.card_congr (coverKernelBasisEquiv Γ b d hd).symm.toEquiv
    _ = (Nat.card (ZMod d)) ^ Nat.card I := Nat.card_fun
    _ = _ := by rw [Nat.card_zmod, Nat.card_eq_fintype_card]

end Erdos3

end

end OAI
