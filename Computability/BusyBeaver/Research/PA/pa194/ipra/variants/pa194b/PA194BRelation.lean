import PA194BFinite
import PA194BModelSteps

set_option autoImplicit false
set_option maxRecDepth 25000
set_option maxHeartbeats 1800000

namespace PA194BSimulation
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
open PA194BRows PA194BModelSteps

abbrev primaryTable := PA194GenericBridge.denseTable
abbrev variantTable := table actions

def controlPairs : List (Nat × Nat) := (List.range 195).map fun i => (i,rho i)

section models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def matchControls (rows : List (Nat × Nat)) (q p : V) : Prop :=
  ∃ row ∈ rows, q = (row.1 : V) ∧ p = (row.2 : V)

theorem matchControlsDef (rows : List (Nat × Nat)) : 𝚺₁-Relation (matchControls (V := V) rows) := by
  induction rows with
  | nil =>
    have h : matchControls (V := V) [] = fun _ _ => False := by
      funext q p
      simp [matchControls]
    rw [h]
    definability
  | cons r rs ih =>
    letI := ih
    have h : matchControls (V := V) (r::rs) =
        fun q p => (q = (r.1 : V) ∧ p = (r.2 : V)) ∨ matchControls rs q p := by
      funext q p
      apply propext
      constructor
      · rintro ⟨row,hr,hq,hp⟩
        rcases List.mem_cons.mp hr with rfl | hr
        · exact Or.inl ⟨hq,hp⟩
        · exact Or.inr ⟨row,hr,hq,hp⟩
      · rintro (⟨hq,hp⟩ | ⟨row,hr,hq,hp⟩)
        · exact ⟨r,List.mem_cons_self,hq,hp⟩
        · exact ⟨row,List.mem_cons_of_mem _ hr,hq,hp⟩
    rw [h]
    definability

/-- The aligned PA194 and PA194B boundary configurations share their tape.
The leading bit of the left half distinguishes the two folded controls. -/
noncomputable def Relation (x y : V) : Prop :=
  matchControls controlPairs (π₁ x) (π₁ y) ∧ π₂ x = π₂ y ∧
    (π₁ x = (39 : V) → π₁ (π₂ x) % 2 = 1) ∧
    (π₁ x = (52 : V) → π₁ (π₂ x) % 2 = 0)

theorem relationDef : 𝚺₁-Relation (Relation (V := V)) := by
  letI := matchControlsDef (V := V) controlPairs
  have e : Relation (V := V) = fun x y =>
      matchControls controlPairs (π₁ x) (π₁ y) ∧ π₂ x = π₂ y ∧
      (π₁ x ≠ (39 : V) ∨ π₁ (π₂ x) % 2 = 1) ∧
      (π₁ x ≠ (52 : V) ∨ π₁ (π₂ x) % 2 = 0) := by
    classical
    funext x y
    simp only [Relation,imp_iff_not_or]
  rw [e]
  definability

theorem configBounded (q : Nat) (hq : q ≤ 194) (l r : V)
    (h39 : q = 39 → l%2 = 1) (h52 : q = 52 → l%2 = 0) :
    Relation (config q l r) (config (rho q) l r) := by
  simp only [Relation,config,pi₁_pair,pi₂_pair]
  refine ⟨⟨(q,rho q),?_,rfl,rfl⟩,trivial,?_,?_⟩
  · simp only [controlPairs,List.mem_map,List.mem_range]
    exact ⟨q,by omega,rfl⟩
  · intro h
    exact h39 (by exact_mod_cast h)
  · intro h
    exact h52 (by exact_mod_cast h)

theorem configs {x y : V} (h : Relation x y) :
    ∃ (q : Nat) (l r : V), q ≤ 194 ∧ x = config q l r ∧ y = config (rho q) l r ∧
      (q = 39 → l%2 = 1) ∧ (q = 52 → l%2 = 0) := by
  obtain ⟨⟨row,hr,hx,hy⟩,ht,h39,h52⟩ := h
  simp only [controlPairs,List.mem_map,List.mem_range] at hr
  obtain ⟨q,hq,rfl⟩ := hr
  refine ⟨q,π₁ (π₂ x),π₂ (π₂ x),by omega,?_,?_,?_,?_⟩
  · unfold config
    rw [←hx,pair_unpair,pair_unpair]
  · unfold config
    rw [←hy,pair_unpair,ht,pair_unpair]
  · rintro rfl
    exact h39 (by exact_mod_cast hx)
  · rintro rfl
    exact h52 (by exact_mod_cast hx)

theorem initial : Relation (0 : V) 0 := by
  have h := configBounded 0 (by decide) (0 : V) 0
    (fun f => False.elim ((by decide : (0 : Nat) ≠ 39) f))
    (fun f => False.elim ((by decide : (0 : Nat) ≠ 52) f))
  simpa [rhoStart,config,pair] using h

theorem halt_iff {x y : V} (h : Relation x y) :
    π₁ x = (194 : V) ↔ π₁ y = (194 : V) := by
  obtain ⟨q,l,r,hq,rfl,rfl,_,_⟩ := configs h
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
end PA194BSimulation
