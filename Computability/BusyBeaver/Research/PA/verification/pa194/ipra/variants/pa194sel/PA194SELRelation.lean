import PA194SELFinite
import PA194BRelation

set_option autoImplicit false
set_option maxRecDepth 25000
set_option maxHeartbeats 2000000

namespace PA194SELSimulation
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder
open PA194SELRows PA194BModelSteps
open PA194BSimulation (matchControls matchControlsDef)

abbrev primaryTable := PA194GenericBridge.denseTable
abbrev variantTable := table actions
def controlPairs : List (Nat × Nat) := (List.range 195).map fun i => (i,rho i)

section models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def histories (fs : List Fold) (q l : V) : Prop :=
  ∀ f ∈ fs, q = (f.origin : V) → l%2 = (f.history : V)

theorem historiesDef (fs : List Fold) : 𝚺₁-Relation (histories (V := V) fs) := by
  induction fs with
  | nil =>
    have e : histories (V := V) [] = fun _ _ => True := by funext q l; simp [histories]
    rw [e]
    definability
  | cons f fs ih =>
    letI := ih
    have e : histories (V := V) (f::fs) = fun q l =>
        (q ≠ (f.origin : V) ∨ l%2 = (f.history : V)) ∧ histories fs q l := by
      classical
      funext q l
      apply propext
      constructor
      · intro h
        exact ⟨imp_iff_not_or.mp (h f List.mem_cons_self), fun g hg => h g (List.mem_cons_of_mem _ hg)⟩
      · rintro ⟨h,hs⟩ g hg
        rcases List.mem_cons.mp hg with rfl | hg
        · exact imp_iff_not_or.mpr h
        · exact hs g hg
    rw [e]
    definability

noncomputable def Relation (x y : V) : Prop :=
  matchControls controlPairs (π₁ x) (π₁ y) ∧ π₂ x = π₂ y ∧ histories folds (π₁ x) (π₁ (π₂ x))

theorem relationDef : 𝚺₁-Relation (Relation (V := V)) := by
  haveI := matchControlsDef (V := V) controlPairs
  haveI := historiesDef (V := V) folds
  unfold Relation
  definability

theorem configBounded (q : Nat) (hq : q ≤ 194) (l r : V)
    (hg : ∀ f ∈ folds, q = f.origin → l%2 = (f.history : V)) :
    Relation (config q l r) (config (rho q) l r) := by
  simp only [Relation,config,pi₁_pair,pi₂_pair]
  refine ⟨⟨(q,rho q),?_,rfl,rfl⟩,trivial,?_⟩
  · simp only [controlPairs,List.mem_map,List.mem_range]
    exact ⟨q,by omega,rfl⟩
  · intro f hf hq
    exact hg f hf (by exact_mod_cast hq)

theorem configs {x y : V} (h : Relation x y) :
    ∃ (q : Nat) (l r : V), q ≤ 194 ∧ x = config q l r ∧ y = config (rho q) l r ∧
      ∀ f ∈ folds, q = f.origin → l%2 = (f.history : V) := by
  obtain ⟨⟨row,hr,hx,hy⟩,ht,hguard⟩ := h
  simp only [controlPairs,List.mem_map,List.mem_range] at hr
  obtain ⟨q,hq,rfl⟩ := hr
  refine ⟨q,π₁ (π₂ x),π₂ (π₂ x),by omega,?_,?_,?_⟩
  · unfold config
    rw [←hx,pair_unpair,pair_unpair]
  · unfold config
    rw [←hy,pair_unpair,ht,pair_unpair]
  · rintro f hf rfl
    exact hguard f hf hx

theorem initial : Relation (0 : V) 0 := by
  have h := configBounded 0 (by decide) (0 : V) 0
    (fun f hf e => False.elim (blankNotFolded f hf e.symm))
  simpa [rhoStart,config,pair] using h

theorem halt_iff {x y : V} (h : Relation x y) :
    π₁ x = (194 : V) ↔ π₁ y = (194 : V) := by
  obtain ⟨q,l,r,hq,rfl,rfl,_⟩ := configs h
  simp only [config,pi₁_pair]
  by_cases he : q = 194
  · simp [he,rhoHalt]
  · have hq' : q < 194 := by omega
    have hl := rhoLive ⟨q,hq'⟩
    have ha : (q : V) ≠ 194 := by exact_mod_cast he
    have hb : (rho q : V) ≠ 194 := by exact_mod_cast (ne_of_lt hl)
    simp [ha,hb]

theorem variantFixed (y : V) (h : π₁ y = (194 : V)) :
    ConPA.Machine.step variantTable y = y := by
  have he : y = config 194 (π₁ (π₂ y)) (π₂ (π₂ y)) := by
    unfold config
    change π₁ y = ((194 : Nat) : V) at h
    rw [←h,pair_unpair,pair_unpair]
  conv_lhs => rw [he]
  rw [halted actions counts.1,←he]

#print axioms relationDef
#print axioms initial
#print axioms halt_iff
#print axioms variantFixed
end models
end PA194SELSimulation
