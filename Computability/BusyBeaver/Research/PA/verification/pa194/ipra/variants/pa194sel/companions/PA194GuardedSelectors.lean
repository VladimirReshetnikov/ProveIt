import PA194SELSegment
import ConPAMachineStutter

set_option autoImplicit false
set_option maxRecDepth 25000
set_option maxHeartbeats 3200000

namespace PA194GuardedSelectors
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
open PA194BModelSteps
open PA194BRows (Action)
open PA194SELRows (Fold)
open PA194BSimulation (matchControls matchControlsDef)
open PA194SELSimulation (histories historiesDef selectorThree)

def action (rows : List Action) (q b : Nat) : Action := rows.getD (2*q+b) (0,0,194)

def special (folds : List Fold) (q : Nat) : Option Fold :=
  folds.find? (fun f => f.origin == q)

def translate (rho : Nat → Nat) (a : Action) : Action := (a.1,a.2.1,rho a.2.2)

def checkSpecial (original candidate : List Action) (rho : Nat → Nat) (folds : List Fold)
    (q : Nat) : Bool :=
  match special folds q with
  | none => true
  | some f => decide <| f.history < 2 ∧ f.selector < 194 ∧ f.helper < 194 ∧
      action original q 0 = (0,1,(action original q 0).2.2) ∧
      action candidate (rho q) 0 = (0,0,f.selector) ∧
      action candidate f.selector f.history = (f.history,1,f.helper) ∧
      action candidate f.helper 0 = (0,1,rho (action original q 0).2.2)

structure Certificate where
  original : List Action
  candidate : List Action
  rho : Nat → Nat
  folds : List Fold
  originalCount : original.length = 388
  candidateCount : candidate.length = 388
  start : rho 0 = 0
  halt : rho 194 = 194
  live : ∀ q : Fin 194, rho q.val < 194
  target : ∀ (q : Fin 194) (b : Fin 2), (action original q.val b.val).2.2 ≤ 194
  registered : folds.all (fun f => decide (f.origin ≠ 0 ∧ f.history < 2)) = true
  ordinary : ∀ (q : Fin 194) (b : Fin 2), (special folds q.val).isNone = true ∨ b.val = 1 →
    action candidate (rho q.val) b.val = translate rho (action original q.val b.val)
  exceptional : ∀ q : Fin 194, checkSpecial original candidate rho folds q.val = true
  incoming : ∀ (q : Fin 194) (b : Fin 2), folds.all (fun f =>
    decide ((action original q.val b.val).2.2 = f.origin →
      (action original q.val b.val).1 = f.history ∧ (action original q.val b.val).2.1 = 1)) = true

abbrev originalTable (C : Certificate) := table C.original
abbrev candidateTable (C : Certificate) := table C.candidate
def controlPairs (C : Certificate) : List (Nat × Nat) :=
  (List.range 195).map fun q => (q,C.rho q)

section models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable (C : Certificate)

noncomputable def Related (x y : V) : Prop :=
  matchControls (controlPairs C) (π₁ x) (π₁ y) ∧ π₂ x = π₂ y ∧
    histories C.folds (π₁ x) (π₁ (π₂ x))

theorem relatedDef : 𝚺₁-Relation (Related (V := V) C) := by
  haveI := matchControlsDef (V := V) (controlPairs C)
  haveI := historiesDef (V := V) C.folds
  unfold Related
  definability

theorem relatedConfigs (q : Nat) (hq : q ≤ 194) (l r : V)
    (hg : ∀ f ∈ C.folds, q = f.origin → l%2 = (f.history : V)) :
    Related C (config q l r) (config (C.rho q) l r) := by
  simp only [Related,config,pi₁_pair,pi₂_pair]
  refine ⟨⟨(q,C.rho q),?_,rfl,rfl⟩,trivial,?_⟩
  · simp only [controlPairs,List.mem_map,List.mem_range]
    exact ⟨q,by omega,rfl⟩
  · intro f hf hq
    exact hg f hf (by exact_mod_cast hq)

theorem configs {x y : V} (h : Related C x y) :
    ∃ (q : Nat) (l r : V), q ≤ 194 ∧ x = config q l r ∧ y = config (C.rho q) l r ∧
      ∀ f ∈ C.folds, q = f.origin → l%2 = (f.history : V) := by
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

theorem initial : Related C (0 : V) 0 := by
  have h := relatedConfigs C 0 (by decide) (0 : V) 0 (fun f hf e => False.elim
    ((of_decide_eq_true (List.all_eq_true.mp C.registered f hf)).1 e.symm))
  simpa [C.start,config,pair] using h

theorem haltMatch {x y : V} (h : Related C x y) : π₁ x = (194 : V) ↔ π₁ y = (194 : V) := by
  obtain ⟨q,l,r,hq,rfl,rfl,_⟩ := configs C h
  simp only [config,pi₁_pair]
  by_cases he : q = 194
  · simp [he,C.halt]
  · have hq' : q < 194 := by omega
    have hl := C.live ⟨q,hq'⟩
    have ha : (q : V) ≠ 194 := by exact_mod_cast he
    have hb : (C.rho q : V) ≠ 194 := by exact_mod_cast (ne_of_lt hl)
    simp [ha,hb]

theorem candidateFixed (y : V) (h : π₁ y = (194 : V)) :
    ConPA.Machine.step (candidateTable C) y = y := by
  have he : y = config 194 (π₁ (π₂ y)) (π₂ (π₂ y)) := by
    unfold config
    change π₁ y = ((194 : Nat) : V) at h
    rw [←h,pair_unpair,pair_unpair]
  conv_lhs => rw [he]
  rw [halted C.candidate C.candidateCount,←he]

theorem nextRelated (q : Fin 194) (b : Fin 2) (l r : V) :
    Related C (next (action C.original q.val b.val) l r)
      (next (translate C.rho (action C.original q.val b.val)) l r) := by
  let a := action C.original q.val b.val
  change Related C (next a l r) (next (translate C.rho a) l r)
  have enters (f : Fold) (hf : f ∈ C.folds) (h : a.2.2 = f.origin) :
      a.1 = f.history ∧ a.2.1 = 1 :=
    (of_decide_eq_true (List.all_eq_true.mp (C.incoming q b) f hf)) h
  by_cases d : a.2.1 = 0
  · simp only [next,translate,d,if_pos]
    refine relatedConfigs C a.2.2 (C.target q b) _ _ ?_
    intro f hf h
    exact False.elim (Nat.zero_ne_one (d.symm.trans (enters f hf h).2))
  · simp only [next,translate,d,if_false]
    refine relatedConfigs C a.2.2 (C.target q b) _ _ ?_
    intro f hf h
    rw [(enters f hf h).1]
    have bound : f.history < 2 := (of_decide_eq_true (List.all_eq_true.mp C.registered f hf)).2
    have hb : (f.history : V) < 2 := by exact_mod_cast bound
    exact stackMod l _ hb

private theorem exception (q : Fin 194) (f : Fold) (hf : special C.folds q.val = some f)
    (l r : V) (hl : l % 2 = (f.history : V)) (hr : r % 2 = 0) :
    (ConPA.Machine.step (candidateTable C))^[3] (config (C.rho q.val) l r) =
      next (translate C.rho (action C.original q.val 0)) l r := by
  have hcheck := C.exceptional q
  simp only [checkSpecial,hf,decide_eq_true_eq] at hcheck
  obtain ⟨hbit,hsel,hhelp,hold,hfirst,hsecond,hthird⟩ := hcheck
  have lsplit : stack (l/2) (f.history : V) = l := by simpa only [hl] using components l
  have rsplit : stack (r/2) 0 = r := by simpa only [hr] using components r
  calc
    _ = (ConPA.Machine.step (candidateTable C))^[3]
         (config (C.rho q.val) (stack (l/2) (f.history : V)) (stack (r/2) 0)) := by rw [lsplit,rsplit]
    _ = config (C.rho (action C.original q.val 0).2.2)
        (stack (stack (l/2) (f.history : V)) 0) (r/2) :=
      selectorThree C.candidate C.candidateCount (C.rho q.val) f.selector f.helper f.history
        _ (C.live q) hsel hhelp hbit hfirst hsecond hthird (l/2) (r/2)
    _ = _ := by
      rw [lsplit]
      have hw := congrArg Prod.fst hold
      have hd := congrArg (fun a : Action => a.2.1) hold
      simp [stack,next,translate,hw,hd]

private theorem matching (q : Fin 194) (b : Fin 2) (l r : V)
    (hr : r%2 = (b.val : V)) (hg : ∀ f ∈ C.folds, q.val = f.origin → l%2 = (f.history : V)) :
    ∃ k : Nat, 0 < k ∧
      (ConPA.Machine.step (candidateTable C))^[k] (config (C.rho q.val) l r) =
        next (translate C.rho (action C.original q.val b.val)) l r := by
  have hb := b.isLt
  by_cases ho : (special C.folds q.val).isNone = true ∨ b.val = 1
  · refine ⟨1,by decide,?_⟩
    rw [Function.iterate_one]
    have hl := C.live q
    have he := stepRow C.candidate (C.rho q.val) b.val l r hb (by rw [C.candidateCount]; omega) hr
    change ConPA.Machine.step (candidateTable C) (config (C.rho q.val) l r) =
      next (action C.candidate (C.rho q.val) b.val) l r at he
    rwa [C.ordinary q b ho] at he
  · have hb0 : b.val = 0 := by
      have hb1 : b.val ≠ 1 := fun f => ho (Or.inr f)
      omega
    rw [hb0,Nat.cast_zero] at hr
    obtain ⟨f,hf⟩ : ∃ f, special C.folds q.val = some f := by
      cases he : special C.folds q.val with
      | none => exact False.elim (ho (Or.inl (by simp [he])))
      | some f => exact ⟨f,rfl⟩
    have bit := List.find?_some (p := fun g : Fold => g.origin == q.val) (a := f) (l := C.folds) hf
    have hd : f.origin = q.val := beq_iff_eq.mp bit
    refine ⟨3,by decide,?_⟩
    rw [hb0]
    exact exception C q f hf l r (hg f (List.mem_of_find?_eq_some hf) hd.symm) hr

theorem segment {x y : V} (h : Related C x y) :
    ∃ k : Nat, 0 < k ∧ Related C (ConPA.Machine.step (originalTable C) x)
      ((ConPA.Machine.step (candidateTable C))^[k] y) := by
  obtain ⟨q,l,r,hq,rfl,rfl,hg⟩ := configs C h
  by_cases e : q = 194
  · subst q
    refine ⟨1,by decide,?_⟩
    rw [Function.iterate_one,C.halt]
    rw [halted C.original C.originalCount, halted C.candidate C.candidateCount]
    simpa only [C.halt] using relatedConfigs C 194 (by decide) l r hg
  · have qlt : q < 194 := by omega
    let qf : Fin 194 := ⟨q,qlt⟩
    have go (b : Fin 2) (hr : r % 2 = (b.val : V)) :
        ∃ k : Nat, 0 < k ∧ Related C (ConPA.Machine.step (originalTable C) (config q l r))
          ((ConPA.Machine.step (candidateTable C))^[k] (config (C.rho q) l r)) := by
      obtain ⟨k,hk,hs⟩ := matching C qf b l r hr hg
      have hp := stepRow C.original q b.val l r b.isLt (by rw [C.originalCount]; have := b.isLt; omega) hr
      change ConPA.Machine.step (originalTable C) (config q l r) =
        next (action C.original q b.val) l r at hp
      refine ⟨k,hk,?_⟩
      rw [hp,hs]
      exact nextRelated C qf b l r
    rcases mod_two r with hr | hr
    · exact go 0 (by simpa using hr)
    · exact go 1 (by simpa using hr)

theorem sameHalt :
    (∃ n : V, π₁ (ConPA.Machine.run (candidateTable C) n) = (194 : V)) ↔
      (∃ n : V, π₁ (ConPA.Machine.run (originalTable C) n) = (194 : V)) :=
  ConPA.Machine.Stutter.equivalent (originalTable C) (candidateTable C) 194 194 (Related (V := V) C)
    (relatedDef C) (initial C) (fun _ _ h => haltMatch C h)
    (candidateFixed C) (fun _ _ h _ => segment C h)

#print axioms sameHalt
end models
end PA194GuardedSelectors
