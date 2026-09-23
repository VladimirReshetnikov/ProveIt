import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Independent formal coordinate changes and quotient algebras

For the angular multiplicity transport in `trigonometry:sec:coupled`,
independent one-variable series with zero constant term and invertible
linear term induce an algebra automorphism of the multivariate series ring.
Mathlib supplies each compositional inverse. The induced quotient equivalence
retains nilpotents and hence native algebra dimensions.
-/

namespace Surreal.FormalCoordinate

open MvPowerSeries

noncomputable section

variable {R σ : Type*} [CommRing R] [Finite σ]

/-- Mutually inverse substitution families give a formal algebra automorphism. -/
def ofFamilies (a b : σ → MvPowerSeries σ R) (ha : HasSubst a) (hb : HasSubst b)
    (hab : ∀ i, subst a (b i) = X i) (hba : ∀ i, subst b (a i) = X i) :
    MvPowerSeries σ R ≃ₐ[R] MvPowerSeries σ R :=
  AlgEquiv.ofAlgHom (substAlgHom ha) (substAlgHom hb) (by
    apply AlgHom.ext
    intro p
    simp only [AlgHom.comp_apply, substAlgHom_apply, AlgHom.id_apply]
    rw [subst_comp_subst_apply hb ha, funext hab, subst_self]
    rfl) (by
    apply AlgHom.ext
    intro p
    simp only [AlgHom.comp_apply, substAlgHom_apply, AlgHom.id_apply]
    rw [subst_comp_subst_apply ha hb, funext hba, subst_self]
    rfl)

/-- Place a separate univariate germ in each coordinate. -/
def coordinates (f : σ → PowerSeries R) (i : σ) : MvPowerSeries σ R :=
  (f i).subst (X i)

theorem hasSubst_coordinates (f : σ → PowerSeries R)
    (hf : ∀ i, (f i).constantCoeff = 0) : HasSubst (coordinates f) := by
  apply hasSubst_of_constantCoeff_zero
  intro i
  exact PowerSeries.constantCoeff_subst_eq_zero (by simp) (f i) (hf i)

omit [Finite σ] in
/-- Substituting a multivariate family into a series in one variable
is the same as substituting that family's indicated component. -/
theorem subst_coordinate {a : σ → MvPowerSeries σ R} (ha : HasSubst a)
    (f : PowerSeries R) (i : σ) :
    subst a (f.subst (X i : MvPowerSeries σ R)) = f.subst (a i) := by
  rw [PowerSeries.subst_def,
    MvPowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.X i).const ha]
  simp only [subst_X ha]
  rfl

/-- Independent inverse coordinate families cancel on all formal series. -/
theorem subst_coordinates_inverse (f g : σ → PowerSeries R)
    (hf : ∀ i, (f i).constantCoeff = 0) (hg : ∀ i, (g i).constantCoeff = 0)
    (hfg : ∀ i, (f i).subst (g i) = PowerSeries.X) (p : MvPowerSeries σ R) :
    subst (coordinates g) (subst (coordinates f) p) = p := by
  rw [subst_comp_subst_apply (hasSubst_coordinates f hf) (hasSubst_coordinates g hg)]
  have h : (fun i => subst (coordinates g) (coordinates f i)) = X := by
    funext i
    rw [coordinates, subst_coordinate (hasSubst_coordinates g hg)]
    change (f i).subst ((g i).subst (X i)) = X i
    rw [← PowerSeries.subst_comp_subst_apply
      (PowerSeries.HasSubst.of_constantCoeff_zero' (hg i)) (PowerSeries.HasSubst.X i),
      hfg i, PowerSeries.subst_X (PowerSeries.HasSubst.X i)]
  rw [h, subst_self]
  rfl

/-- The explicit inverse families give an actual algebra equivalence. -/
def ofInverse (f g : σ → PowerSeries R)
    (hf : ∀ i, (f i).constantCoeff = 0) (hg : ∀ i, (g i).constantCoeff = 0)
    (hfg : ∀ i, (f i).subst (g i) = PowerSeries.X)
    (hgf : ∀ i, (g i).subst (f i) = PowerSeries.X) :
    MvPowerSeries σ R ≃ₐ[R] MvPowerSeries σ R :=
  AlgEquiv.ofAlgHom (substAlgHom (hasSubst_coordinates f hf))
    (substAlgHom (hasSubst_coordinates g hg)) (by
      apply AlgHom.ext
      intro p
      simp only [AlgHom.comp_apply, substAlgHom_apply, AlgHom.id_apply]
      exact subst_coordinates_inverse g f hg hf hgf p) (by
      apply AlgHom.ext
      intro p
      simp only [AlgHom.comp_apply, substAlgHom_apply, AlgHom.id_apply]
      exact subst_coordinates_inverse f g hf hg hfg p)

/-- A unit linear coefficient supplies every independent formal inverse. -/
def ofUnitLinear (f : σ → PowerSeries R) (hf : ∀ i, (f i).constantCoeff = 0)
    (hu : ∀ i, IsUnit ((f i).coeff 1)) : MvPowerSeries σ R ≃ₐ[R] MvPowerSeries σ R :=
  ofInverse f (fun i => (f i).substInvOfIsUnit (hu i)) hf
    (fun i => PowerSeries.constantCoeff_substInvOfIsUnit (f i) (hu i))
    (fun i => PowerSeries.subst_substInvOfIsUnit_right (f i) (hf i) (hu i))
    (fun i => PowerSeries.subst_substInvOfIsUnit_left (f i) (hf i) (hu i))

/-- The automorphism sends each variable to exactly the specified germ. -/
@[simp] theorem ofUnitLinear_X (f : σ → PowerSeries R) (hf : ∀ i, (f i).constantCoeff = 0)
    (hu : ∀ i, IsUnit ((f i).coeff 1)) (i : σ) :
    ofUnitLinear f hf hu (X i) = coordinates f i :=
  substAlgHom_X (hasSubst_coordinates f hf) i

/-- Any defining ideal transports through the verified coordinate change. -/
def quotientEquiv (f : σ → PowerSeries R) (hf : ∀ i, (f i).constantCoeff = 0)
    (hu : ∀ i, IsUnit ((f i).coeff 1)) (J : Ideal (MvPowerSeries σ R)) :
    (MvPowerSeries σ R ⧸ J) ≃ₐ[R]
      MvPowerSeries σ R ⧸ J.map (ofUnitLinear f hf hu).toRingHom :=
  Ideal.quotientEquivAlg J _ (ofUnitLinear f hf hu) rfl

end
end Surreal.FormalCoordinate
