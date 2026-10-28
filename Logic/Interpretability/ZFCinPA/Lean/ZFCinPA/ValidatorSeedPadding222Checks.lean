import ZFCinPA.ValidatorSeedPadding222

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace LeanProofs.ZFCinPA.ValidatorSeedPadding222Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open _root_.SetTheory.BusyBeaver.ZFC ArithmeticCode254
open ValidatorProvability222 ValidatorRelationalCore222 ValidatorSeedImage222 ValidatorEnvironmentVacuity222
open ValidatorSeedPadding222
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (bound p : V) : bound<seedLabel bound p ∧ seedLabel bound p%2=0 :=
  ⟨bound_lt_seedLabel bound p,seedLabel_mod_two bound p⟩

-- Arbitrary numeric matrices include zero, and the two input roles may coincide.
example : CProv (ex (seedLabel (3 : V) 0) (imageBody 1 1 (seedLabel (3 : V) 0) 0)) :=
  bounded_seed_image 3 0 1 1 (by simp) (by simp)

-- Future odd labels never equal the chosen self-label, for every internal index.
example (bound p s k : V) (hs : s%2=1) : seedLabel bound p≠s+2*k :=
  seedLabel_stream bound p s hs k

example (bound F B p : V) (hF : F≤bound) (hB : B≤bound) :
    FreeAvoid (seedLabel bound p) F ∧ Avoid (seedLabel bound p) B :=
  ⟨seedLabel_free bound p F hF,seedLabel_avoids bound p B hB⟩

example :
    let c := seedLabel (3 : V) 0
    CProv (ex c (imageBody 1 3 c 0)) ∧ ValidatorRelationalCore222.Vac c 0 := by
  simpa only [ValidatorFormulaEncoder222.encode_verum] using
    typed_seed_vacuity (n := (0 : V)) (p := (^⊤ : V)) (by simp)
      3 0 0 3 1 3 (by simp) (by simp) (by simp)
      (by simp [←two_add_one_eq_three]) (by simp) (by simp)

#print axioms seedLabel_definable
#print axioms bound_lt_seedLabel
#print axioms seedLabel_mod_two
#print axioms raised_equiv
#print axioms seedLabel_equiv
#print axioms bounded_seed_image
#print axioms seedLabel_avoids
#print axioms seedLabel_free
#print axioms seedLabel_stream
#print axioms typed_seed_vacuity
#print axioms typed_seed_witnesses
end LeanProofs.ZFCinPA.ValidatorSeedPadding222Checks
