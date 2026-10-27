import ZFCinPA.ValidatorSeedGicImages222

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace LeanProofs.ZFCinPA.ValidatorSeedGicImages222Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LO.FirstOrder.SetTheory
open ValidatorFullSeedTheory222 ValidatorSeedSourceBasis222 ValidatorSeedMarkerDischarge222
open ValidatorSeedMarkerRelativization222 ValidatorSeedGicImages222
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (j : V) (K : Semiformula V ℒₛₑₜ 2) :
    (swapped j K).subst ![(Bootstrapping.Semiterm.bvar 1 : Semiterm V ℒₛₑₜ 3),Bootstrapping.Semiterm.bvar 0]=
      (tagged j K).subst ![Bootstrapping.Semiterm.bvar 0,Bootstrapping.Semiterm.bvar 1] :=
  swapped_support j K
example (j : V) (K : Semiformula V ℒₛₑₜ 2) :
    (swapped j K).subst ![(Bootstrapping.Semiterm.bvar 0 : Semiterm V ℒₛₑₜ 3),Bootstrapping.Semiterm.bvar 1]=
      (tagged j K).subst ![Bootstrapping.Semiterm.bvar 1,Bootstrapping.Semiterm.bvar 0] :=
  swapped_coverage j K

-- A nested quantified matrix, with its free label equal to the marker.
example (j : V) : Provable seedTheory
    (imp ℒₛₑₜ (emptyCode j) (tagRel j (gicBodyVal
      (∀⁰ ∃⁰ memTerm (Bootstrapping.Semiterm.bvar 0)
        (Bootstrapping.Semiterm.fvar j) : Semiformula V ℒₛₑₜ 2).val))) :=
  gic_body_image _ j
example (K : Semiformula V ℒₛₑₜ 2) :
    Provable seedTheory (imp ℒₛₑₜ (emptyCode 0) (tagRel 0 (gicBodyVal K.val))) :=
  gic_body_image K 0

-- The closure theorem has no m<=j or positive-marker restriction.
example (m b : V) (hb : IsSemiformula ℒₛₑₜ m b) (hs : shift ℒₛₑₜ b=b)
    (h : Provable seedTheory (imp ℒₛₑₜ (emptyCode m)
      (tagRel m (subst ℒₛₑₜ (fvarVec m) b)))) :
    Provable seedTheory (imp ℒₛₑₜ (emptyCode 0) (tagRel 0 (qqAlls b m))) := by
  exact close_guarded hb hs (by simpa using h)
example (j b : V) (hb : IsFormula ℒₛₑₜ b) (hs : shift ℒₛₑₜ b=b)
    (h : Provable seedTheory (imp ℒₛₑₜ (emptyCode j)
      (tagRel j (subst ℒₛₑₜ (fvarVec 0) b)))) :
    Provable seedTheory (imp ℒₛₑₜ (emptyCode j) (tagRel j b)) := by
  simpa using (close_guarded (j := j) hb hs (by simpa using h))
example (p j : V) (hp : GicR p) :
    Provable seedTheory (imp ℒₛₑₜ (emptyCode j) (tagRel j p)) := recognized_gic_image hp j
example (p j : V) (hp : IsFormula ℒₛₑₜ p) (hT : p∈gicTheory.Δ₁Class) (hj : p<j) :
    Derivable seedTheory (insert (tagRel j p) (insert (emptyGuard j) (sideSet j))) :=
  axiomImages_gicTheory p j hp hT hj

#print axioms tagged_imp
#print axioms tagged_all
#print axioms tagged_subst
#print axioms tagged_free
#print axioms swapped_support
#print axioms swapped_coverage
#print axioms gic_open_binding
#print axioms gic_body_image
#print axioms close_step
#print axioms close_guarded
#print axioms recognized_gic_image
#print axioms axiomImages_gicTheory
end LeanProofs.ZFCinPA.ValidatorSeedGicImages222Checks
