import ZFCinPA.ValidatorEnvironmentOpening254
import ZFCinPA.ValidatorEnvironmentSubstitution254

set_option autoImplicit false
noncomputable section

/-!
Internal instantiation by a source-language free variable, with the free
label environment unchanged. The generalized bound slot carries its interpreted
label; under binders the extension is pushed on both sides. This proves a
syntax identity for the actual EXS substitution, not its CProv rule.
-/
namespace LeanProofs.ZFCinPA.ValidatorEnvironmentInstantiation254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open ValidatorEnvironmentLabels254 ValidatorEnvironmentOpening254 ModelCodedSpecialization
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def instantiationVec (d index : V) : V := qVecIter ℒₛₑₜ d (^&index∷0)
lemma instantiationVec_typed (d index : V) : IsSemitermVec ℒₛₑₜ (d+1) d (instantiationVec d index) := by
  simpa [instantiationVec,add_comm] using qVecIter_isSemitermVec (L := ℒₛₑₜ)
    (show IsSemitermVec (V := V) ℒₛₑₜ 1 0 (^&index∷0) by simp) d
@[simp] lemma instantiationVec_succ (d index : V) : instantiationVec (d+1) index=qVec ℒₛₑₜ (instantiationVec d index) :=
  qVecIter_succ d _

noncomputable def termInstantiateAt (d index source : V) : V :=
  termSubst ℒₛₑₜ (instantiationVec d index) source
noncomputable def instantiateAt (d index source : V) : V :=
  subst ℒₛₑₜ (instantiationVec d index) source

private lemma instantiation_matches (d F B B' index : V)
    (hB : Ext d B B' (freeLabel F index)) :
    ValidatorEnvironmentSubstitution254.Matches F B B' (d+1) (instantiationVec d index) := by
  intro i hi
  by_cases hid : i<d
  · rw [show (instantiationVec d index).[i]=(^#i : V) from
      (qVecIter_free_spec (L := ℒₛₑₜ) d index).1 i hid]
    rw [TermLabels.term_bvar,hB.2.2.1 i hid]
  · have he : i=d := le_antisymm (lt_succ_iff_le.mp hi) (le_of_not_gt hid)
    subst i
    rw [show (instantiationVec d index).[d]=(^&index : V) from
      (qVecIter_free_spec (L := ℒₛₑₜ) d index).2]
    rw [TermLabels.term_fvar,hB.2.2.2]

lemma term_labels_instantiate {d source : V} (ht : IsSemiterm ℒₛₑₜ (d+1) source)
    (F B B' index : V) (hB : Ext d B B' (freeLabel F index)) :
    TermLabels.term F B (termInstantiateAt d index source)=TermLabels.term F B' source :=
  ValidatorEnvironmentSubstitution254.term_labels_subst ht (instantiation_matches d F B B' index hB)

lemma vec_labels_instantiate {d arity terms : V} (ht : IsSemitermVec ℒₛₑₜ arity (d+1) terms)
    (F B B' index : V) (hB : Ext d B B' (freeLabel F index)) :
    TermLabels.vec F B arity
      (termSubstVec ℒₛₑₜ arity (instantiationVec d index) terms)=
      TermLabels.vec F B' arity terms :=
  ValidatorEnvironmentSubstitution254.vec_labels_subst ht (instantiationVec_typed d index)
    (instantiation_matches d F B B' index hB)

lemma instantiateAt_isSemiformula {d p : V} (index : V) (hp : IsSemiformula ℒₛₑₜ (d+1) p) :
    IsSemiformula ℒₛₑₜ d (instantiateAt d index p) := hp.subst (instantiationVec_typed d index)

lemma instantiateAt_rel (d index : V) {arity R terms : V}
    (hr : (ℒₛₑₜ).IsRel arity R) (ht : IsUTermVec ℒₛₑₜ arity terms) :
    instantiateAt d index (^rel arity R terms)=
      ^rel arity R (termSubstVec ℒₛₑₜ arity (instantiationVec d index) terms) := by
  rw [instantiateAt,substs_rel hr ht]
lemma instantiateAt_nrel (d index : V) {arity R terms : V}
    (hr : (ℒₛₑₜ).IsRel arity R) (ht : IsUTermVec ℒₛₑₜ arity terms) :
    instantiateAt d index (^nrel arity R terms)=
      ^nrel arity R (termSubstVec ℒₛₑₜ arity (instantiationVec d index) terms) := by
  rw [instantiateAt,substs_nrel hr ht]
@[simp] lemma instantiateAt_verum (d index : V) : instantiateAt d index (^⊤ : V)=^⊤ := by simp [instantiateAt]
@[simp] lemma instantiateAt_falsum (d index : V) : instantiateAt d index (^⊥ : V)=^⊥ := by simp [instantiateAt]
lemma instantiateAt_and (d index : V) {p q : V} (hp : IsUFormula ℒₛₑₜ p) (hq : IsUFormula ℒₛₑₜ q) :
    instantiateAt d index (p ^⋏ q)=instantiateAt d index p ^⋏ instantiateAt d index q := by
  rw [instantiateAt,substs_and hp hq];rfl
lemma instantiateAt_or (d index : V) {p q : V} (hp : IsUFormula ℒₛₑₜ p) (hq : IsUFormula ℒₛₑₜ q) :
    instantiateAt d index (p ^⋎ q)=instantiateAt d index p ^⋎ instantiateAt d index q := by
  rw [instantiateAt,substs_or hp hq];rfl
lemma instantiateAt_all (d index : V) {p : V} (hp : IsUFormula ℒₛₑₜ p) :
    instantiateAt d index (^∀ p)=^∀ (instantiateAt (d+1) index p) := by
  rw [instantiateAt,substs_all hp,←instantiationVec_succ];rfl
lemma instantiateAt_exs (d index : V) {p : V} (hp : IsUFormula ℒₛₑₜ p) :
    instantiateAt d index (^∃ p)=^∃ (instantiateAt (d+1) index p) := by
  rw [instantiateAt,substs_ex hp,←instantiationVec_succ];rfl

private instance qVecIter_delta : 𝚫₁-Function₂[V] (qVecIter ℒₛₑₜ) :=
  qVecIter_defined.graph_delta.to_definable
private instance subst_delta : 𝚫₁-Function₂[V] (subst ℒₛₑₜ) :=
  subst.defined.graph_delta.to_definable
private instance len_delta : 𝚫₁-Function₁[V] (len : V→V) :=
  len_defined.graph_delta.to_definable

lemma encode_instantiateAt {d p : V} (hp : IsSemiformula ℒₛₑₜ (d+1) p)
    (F B B' index fresh : V) (hB : Ext d B B' (freeLabel F index)) :
    encode F B fresh (instantiateAt d index p)=encode F B' fresh p := by
  exact ValidatorEnvironmentSubstitution254.encode_subst hp (instantiationVec_typed d index)
    F B B' fresh (instantiation_matches d F B B' index hB)

/-- Actual single-variable source substitution at depth zero. -/
lemma encode_substs1_fvar {p : V} (hp : IsSemiformula ℒₛₑₜ 1 p)
    (F index fresh : V) :
    encode F 0 fresh (substs1 ℒₛₑₜ (^&index) p)=
      encode F (freeLabel F index∷0) fresh p := by
  simpa [instantiateAt,instantiationVec,substs1] using
    encode_instantiateAt (d := 0) (by simpa using hp)
      F 0 (freeLabel F index∷0) index fresh (ext_zero _)

/-- In the fixed set language every internal term is a free variable. -/
lemma term_is_fvar {t : V} (ht : IsTerm ℒₛₑₜ t) : ∃ index : V, t=^&index := by
  rcases ht.case with (⟨i,hi,rfl⟩ | ⟨index,rfl⟩ | ⟨k,f,args,hf,_,rfl⟩)
  · simp at hi
  · exact ⟨index,rfl⟩
  · have hf' : V ⊧/![k,f] (LeanProofs.ZFCinPA.instLORDefinableSet.func).val := hf
    rw [show (LeanProofs.ZFCinPA.instLORDefinableSet.func : 𝚺₀.Semisentence 2) =
      .mkSigma “k f. ⊥” from rfl] at hf'
    simp at hf'

/-- The source EXS rule's arbitrary internally typed term is interpreted by
its actual free label, including the environment's fallback label. -/
theorem encode_substs1 {p t : V} (hp : IsSemiformula ℒₛₑₜ 1 p) (ht : IsTerm ℒₛₑₜ t)
    (F fresh : V) :
    encode F 0 fresh (substs1 ℒₛₑₜ t p)=
      encode F (TermLabels.term F 0 t∷0) fresh p := by
  obtain ⟨index,rfl⟩ := term_is_fvar ht
  simpa only [TermLabels.term_fvar] using encode_substs1_fvar hp F index fresh

end LeanProofs.ZFCinPA.ValidatorEnvironmentInstantiation254
