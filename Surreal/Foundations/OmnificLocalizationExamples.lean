import Surreal.Surcomplex.OmnificLocalizationCalculus
import Surreal.Foundations.OmnificPrincipalImages
import Surreal.Foundations.OmnificMonomialLocalization

/-!
# Ordinary reflections of concrete omnific localizations

The four reflection examples in `osq:ex:localizations`, together with
the previously proved nonzero-domain and principal-quotient results.
The module obstruction for unit constant principal generators is proved
for every such generator, not just omega plus one.
-/

universe u v
namespace Surreal.Foundations.SignSequence
noncomputable section

/-- Inverting n plus omega has the same small-target maps as the ordinary ring Z[1/n]. -/
def omnificShiftedOmegaAwaySmallHomEquiv (n : ℤ) (B : Type v) [Ring B] [Small.{u} B] :
    (Localization.Away (omnificShiftedOmega.{u} n) →+* B) ≃ (Localization.Away n →+* B) := by
  exact Eq.mp (congrArg (fun d : ℤ =>
    (Localization.Away (omnificShiftedOmega.{u} n) →+* B) ≃ (Localization.Away d →+* B))
      (omnificShiftedOmega_constant.{u} n))
    (omnificAwaySmallHomEquiv (omnificShiftedOmega.{u} n) B)

/-- The report's localization at omega plus two reflects precisely to the ordinary ring Z[1/2]. -/
def omnificOmegaPlusTwoAwaySmallHomEquiv (B : Type v) [Ring B] [Small.{u} B] :
    (Localization.Away (omnificShiftedOmega.{u} 2) →+* B) ≃ (Localization.Away (2 : ℤ) →+* B) :=
  omnificShiftedOmegaAwaySmallHomEquiv 2 B

/-- Inverting an ordinary integer has exactly the corresponding ordinary localization as reflection. -/
def omnificIntAwaySmallHomEquiv (n : ℤ) (B : Type v) [Ring B] [Small.{u} B] :
    (Localization.Away (omnificIntCast.{u} n) →+* B) ≃ (Localization.Away n →+* B) := by
  exact Eq.mp (congrArg (fun d : ℤ =>
    (Localization.Away (omnificIntCast.{u} n) →+* B) ≃ (Localization.Away d →+* B))
      (omnificConstantCoeff_intCast.{u} n))
    (omnificAwaySmallHomEquiv (omnificIntCast.{u} n) B)

/-- Inverting a constant-zero omnific element has the zero ring as ordinary reflection. -/
theorem omnificAway_constant_reflection_subsingleton (s : OmnificInteger.{u})
    (hs : omnificConstantCoeff s = 0) : Subsingleton (Localization.Away (omnificConstantCoeff s)) := by
  apply IsLocalization.subsingleton (M := Submonoid.powers (omnificConstantCoeff s))
  rw [hs]
  exact Submonoid.mem_powers (0 : ℤ)

/-- A principal quotient by an element with unit constant has only trivial small modules. -/
theorem omnific_principal_small_module_of_unit_constant (f : OmnificInteger.{u})
    (hf : IsUnit (omnificConstantCoeff f)) (M : Type v) [AddCommGroup M]
    [Module (OmnificInteger.{u} ⧸ Ideal.span {f}) M] [Small.{u} M] : Subsingleton M := by
  letI : Module OmnificInteger.{u} M := Module.compHom M (Ideal.Quotient.mk (Ideal.span {f}))
  have hz (m : M) : m = 0 := by
    apply hf.smul_eq_zero.mp
    rw [← omnific_smul_small_eq_constant f m]
    change (Ideal.Quotient.mk (Ideal.span {f}) f) • m = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton f))]
    exact _root_.zero_smul (OmnificInteger.{u} ⧸ Ideal.span {f}) m
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

/-- Although Oz/(omega+1) is nonzero, every small unital module over it is zero. -/
theorem omnific_one_add_omega_quotient_small_module (M : Type v) [AddCommGroup M]
    [Module (OmnificInteger.{u} ⧸ Ideal.span {omnificShiftedOmega.{u} 1}) M] [Small.{u} M] :
    Subsingleton M :=
  omnific_principal_small_module_of_unit_constant _
    (by rw [omnificShiftedOmega_constant]; exact isUnit_one) M

end
end Surreal.Foundations.SignSequence
