import ZFCinPA.ValidatorEnvironmentInstantiation254

set_option autoImplicit false
noncomputable section
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.ZFCinPA.ValidatorEnvironmentLabels254
open LeanProofs.ZFCinPA.ValidatorEnvironmentOpening254
open LeanProofs.ZFCinPA.ValidatorEnvironmentInstantiation254
open scoped LO.FirstOrder.Arithmetic

#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentInstantiation254.instantiationVec_typed
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentInstantiation254.term_labels_instantiate
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentInstantiation254.vec_labels_instantiate
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentInstantiation254.instantiateAt_isSemiformula
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentInstantiation254.instantiateAt_rel
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentInstantiation254.instantiateAt_nrel
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentInstantiation254.instantiateAt_all
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentInstantiation254.instantiateAt_exs
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentInstantiation254.encode_instantiateAt
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentInstantiation254.encode_substs1_fvar
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentInstantiation254.term_is_fvar
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentInstantiation254.encode_substs1

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (d j : V) : IsSemitermVec ℒₛₑₜ (d+1) d (instantiationVec d j) :=
  instantiationVec_typed d j
example (d j : V) : instantiationVec (d+1) j=qVec ℒₛₑₜ (instantiationVec d j) :=
  instantiationVec_succ d j
example (d t F B B' j : V) (ht : IsSemiterm ℒₛₑₜ (d+1) t)
    (hB : Ext d B B' (freeLabel F j)) :
    TermLabels.term F B (termInstantiateAt d j t)=TermLabels.term F B' t :=
  term_labels_instantiate ht F B B' j hB
example (d k ts F B B' j : V) (ht : IsSemitermVec ℒₛₑₜ k (d+1) ts)
    (hB : Ext d B B' (freeLabel F j)) :
    TermLabels.vec F B k (termSubstVec ℒₛₑₜ k (instantiationVec d j) ts)=
      TermLabels.vec F B' k ts := vec_labels_instantiate ht F B B' j hB
example (d p j : V) (hp : IsSemiformula ℒₛₑₜ (d+1) p) :
    IsSemiformula ℒₛₑₜ d (instantiateAt d j p) := instantiateAt_isSemiformula j hp
example (d j k R ts : V) (hr : (ℒₛₑₜ).IsRel k R) (ht : IsUTermVec ℒₛₑₜ k ts) :
    instantiateAt d j (^rel k R ts)=^rel k R (termSubstVec ℒₛₑₜ k (instantiationVec d j) ts) :=
  instantiateAt_rel d j hr ht
example (d j k R ts : V) (hr : (ℒₛₑₜ).IsRel k R) (ht : IsUTermVec ℒₛₑₜ k ts) :
    instantiateAt d j (^nrel k R ts)=^nrel k R (termSubstVec ℒₛₑₜ k (instantiationVec d j) ts) :=
  instantiateAt_nrel d j hr ht
example (d j p : V) (hp : IsUFormula ℒₛₑₜ p) :
    instantiateAt d j (^∀ p)=^∀ (instantiateAt (d+1) j p) := instantiateAt_all d j hp
example (d j p : V) (hp : IsUFormula ℒₛₑₜ p) :
    instantiateAt d j (^∃ p)=^∃ (instantiateAt (d+1) j p) := instantiateAt_exs d j hp
example (d p F B B' j fresh : V) (hp : IsSemiformula ℒₛₑₜ (d+1) p)
    (hB : Ext d B B' (freeLabel F j)) :
    encode F B fresh (instantiateAt d j p)=encode F B' fresh p :=
  encode_instantiateAt hp F B B' j fresh hB
example (p F j fresh : V) (hp : IsSemiformula ℒₛₑₜ 1 p) :
    encode F 0 fresh (substs1 ℒₛₑₜ (^&j) p)=encode F (freeLabel F j∷0) fresh p :=
  encode_substs1_fvar hp F j fresh
example (t : V) (ht : IsTerm ℒₛₑₜ t) : ∃ j : V, t=^&j := term_is_fvar ht
example (p t F fresh : V) (hp : IsSemiformula ℒₛₑₜ 1 p) (ht : IsTerm ℒₛₑₜ t) :
    encode F 0 fresh (substs1 ℒₛₑₜ t p)=encode F (TermLabels.term F 0 t∷0) fresh p :=
  encode_substs1 hp ht F fresh
example (p j fresh : V) (hp : IsSemiformula ℒₛₑₜ 1 p) :
    encode 0 0 fresh (substs1 ℒₛₑₜ (^&j) p)=encode 0 (1∷0) fresh p := by
  simpa only [freeLabel_nil] using encode_substs1_fvar hp 0 j fresh
example (d j F B B' : V) (hB : Ext d B B' (freeLabel F j)) :
    encode F B 0 (instantiateAt d j (^⊥ : V))=1 := by simp
example (p F j fresh : V) (hp : IsSemiformula ℒₛₑₜ 1 p) :
    encode F 0 fresh (substs1 ℒₛₑₜ (^&j) p)=
      encode (freeLabel F j∷F) 0 fresh (free ℒₛₑₜ p) := by
  rw [encode_substs1_fvar hp, encode_free hp]
