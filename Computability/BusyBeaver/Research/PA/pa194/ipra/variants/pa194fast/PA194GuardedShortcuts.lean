import PA194BModelSteps
import ConPAMachineStutter
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4500000

namespace PA194GuardedShortcuts
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194BModelSteps

abbrev Action := PA194BRows.Action

def atRow (rows : List Action) (q b : Nat) : Action := rows.getD (2*q+b) (0,0,194)

/-- Certificate for the two guarded three-to-one tape identities. -/
structure Certificate where
  original : List Action
  accelerated : List Action
  originalCount : original.length = 388
  acceleratedCount : accelerated.length = 388
  firstSource : Fin 194
  firstNext : Fin 194
  firstTurn : Fin 194
  firstDestination : Fin 194
  secondSource : Fin 194
  secondReturn : Fin 194
  secondDestination : Fin 194
  neighborControl : Fin 194

  firstOriginal : atRow original firstSource 1 = (1,1,firstNext.val)
  firstMiddle : atRow original firstNext 0 = (0,1,firstTurn.val)
  firstLast : atRow original firstTurn 0 = (0,0,firstDestination.val)
  firstFast : atRow accelerated firstSource 1 = (1,1,firstDestination.val)
  secondOriginal : atRow original secondSource 0 = (0,0,firstSource.val)
  secondMiddle : atRow original firstSource 0 = (0,1,secondReturn.val)
  secondLast : atRow original secondReturn 0 = (0,1,secondDestination.val)
  secondFast : atRow accelerated secondSource 0 = (0,1,secondDestination.val)
  ordinary : ∀ q : Fin 194, ∀ b : Fin 2,
    (q.val ≠ firstSource.val ∨ b.val ≠ 1) →
    (q.val ≠ secondSource.val ∨ b.val ≠ 0) →
    atRow accelerated q b = atRow original q b
  incoming : ∀ q : Fin 194, ∀ b : Fin 2,
    let a := atRow accelerated q b
    a.2.2 < 195 ∧
    (a.2.2 = secondSource.val → a.1 = 0 ∧ a.2.1 = 1) ∧
    (a.2.2 = neighborControl.val → a.1 = 0) ∧
    (a.2.2 = firstSource.val → q.val = neighborControl.val ∧ b.val = 0 ∧ a.1 = 0 ∧ a.2.1 = 0)

abbrev acceleratedTable (C : Certificate) := PA194BModelSteps.table C.accelerated
abbrev originalTable (C : Certificate) := PA194BModelSteps.table C.original

section models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable (C : Certificate)

/-- Neighbor bits sufficient for the two literal shortcuts, in the dense
    control names of the primary table. -/
def goodTape (q : Nat) (l r : V) : Prop :=
  (q = C.secondSource.val → l%2 = 0) ∧ (q = C.neighborControl.val → l%2 = 0 ∨ (r/2)%2 = 0) ∧
  (q = C.firstSource.val → (r/2)%2 = 0 ∧ (r%2 = 0 ∨ ((r/2)/2)%2 = 0))

noncomputable def invariant (x : V) : Prop :=
  let q := π₁ x
  let l := π₁ (π₂ x)
  let r := π₂ (π₂ x)
  q < 195 ∧ (q = (C.secondSource.val : V) → l%2 = 0) ∧ (q = (C.neighborControl.val : V) → l%2 = 0 ∨ (r/2)%2 = 0) ∧
    (q = (C.firstSource.val : V) → (r/2)%2 = 0 ∧ (r%2 = 0 ∨ ((r/2)/2)%2 = 0))

theorem invariant_def : 𝚺₁-Predicate (invariant (V := V) C) := by
  unfold invariant
  simp only [imp_iff_not_or]
  definability

theorem config_iff (q : Nat) (l r : V) : invariant C (config q l r) ↔ q < 195 ∧ goodTape C q l r := by
  have hBound : ((q : V) < 195) ↔ q < 195 := Nat.cast_lt
  simp only [invariant,config,pi₁_pair,pi₂_pair,hBound,Nat.cast_inj,goodTape]

private theorem boundedControl (x : V) (n : Nat) (h : x < (n : V)) :
    ∃ q : Nat, q < n ∧ x = (q : V) := by
  induction n with
  | zero => simp at h
  | succ n ih =>
    rw [Nat.cast_succ] at h
    rcases lt_or_eq_of_le (lt_succ_iff_le.mp h) with lt | eq
    · obtain ⟨q,hq,rfl⟩ := ih lt
      exact ⟨q,by omega,rfl⟩
    · exact ⟨n,by omega,eq⟩

theorem unpack {x : V} (h : invariant C x) :
    ∃ q : Nat, ∃ l r : V, q < 195 ∧ goodTape C q l r ∧ x = config q l r := by
  have bound : π₁ x < (195 : V) := h.1
  obtain ⟨q, hq, hc⟩ := boundedControl (π₁ x) 195 bound
  have he : x = config q (π₁ (π₂ x)) (π₂ (π₂ x)) := by
    unfold config
    rw [← hc,pair_unpair,pair_unpair]
  have hg := (config_iff C q (π₁ (π₂ x)) (π₂ (π₂ x))).mp (he ▸ h)
  exact ⟨q,_,_,hq,hg.2,he⟩

theorem init : invariant C (0 : V) := by
  have g : goodTape C 0 (0 : V) 0 := by simp [goodTape]
  have h := (config_iff C 0 (0 : V) 0).mpr ⟨by decide,g⟩
  simpa [config,pair] using h

/-- The accelerated table preserves the invariant. Its only remaining
    incoming row to dense control C.firstSource.val is the left move of control C.neighborControl.val. -/
theorem nextInvariant (q : Fin 194) (b : Fin 2) (l r : V) (old : goodTape C q.val l r) :
    invariant C (next (atRow C.accelerated q.val b.val) l r) := by
  let a := atRow C.accelerated q.val b.val
  obtain ⟨bound, into101, into11, into26⟩ := C.incoming q b
  change a.2.2 < 195 at bound
  change a.2.2 = C.secondSource.val → a.1 = 0 ∧ a.2.1 = 1 at into101
  change a.2.2 = C.neighborControl.val → a.1 = 0 at into11
  change a.2.2 = C.firstSource.val → q.val = C.neighborControl.val ∧ b.val = 0 ∧ a.1 = 0 ∧ a.2.1 = 0 at into26
  change invariant C (next a l r)
  by_cases move : a.2.1 = 0
  · let middle := stack (r/2) (a.1 : V)
    have hbits : 4*(r/2)+2*(a.1 : V)+l%2 = stack middle (l%2) := by
      dsimp [middle,stack]
      ring
    have hb : l%2 < 2 := mod_lt l (by norm_num)
    rw [next,if_pos move,hbits]
    apply (config_iff C _ _ _).mpr
    refine ⟨bound, ?_, ?_, ?_⟩
    · intro ht
      exact False.elim (Nat.zero_ne_one (move.symm.trans (into101 ht).2))
    · intro ht
      right
      rw [stackDiv _ _ hb]
      change stack (r/2) (a.1 : V) % 2 = 0
      rw [into11 ht,Nat.cast_zero,stackMod _ _ (by norm_num)]
    · intro ht
      obtain ⟨q46,_,w0,_⟩ := into26 ht
      obtain ha | hc := old.2.1 q46
      · rw [stackDiv _ _ hb,stackMod _ _ hb,ha]
        change stack (r/2) (a.1 : V) % 2 = 0 ∧ (0 = 0 ∨ _)
        rw [w0,Nat.cast_zero,stackMod _ _ (by norm_num)]
        exact ⟨rfl,Or.inl rfl⟩
      · rw [stackDiv _ _ hb,stackMod _ _ hb]
        change stack (r/2) (a.1 : V) % 2 = 0 ∧
          (l%2 = 0 ∨ (stack (r/2) (a.1 : V)/2)%2 = 0)
        rw [w0,Nat.cast_zero,stackMod _ _ (by norm_num),stackDiv _ _ (by norm_num)]
        exact ⟨rfl,Or.inr hc⟩
  · rw [next,if_neg move]
    apply (config_iff C _ _ _).mpr
    refine ⟨bound, ?_, ?_, ?_⟩
    · intro ht
      change stack l (a.1 : V) % 2 = 0
      rw [(into101 ht).1,Nat.cast_zero,stackMod _ _ (by norm_num)]
    · intro ht
      left
      change stack l (a.1 : V) % 2 = 0
      rw [into11 ht,Nat.cast_zero,stackMod _ _ (by norm_num)]
    · intro ht
      exact False.elim (move (into26 ht).2.2.2)

private theorem three {x y z w : V}
    (h1 : ConPA.Machine.step (originalTable C) x = y) (h2 : ConPA.Machine.step (originalTable C) y = z)
    (h3 : ConPA.Machine.step (originalTable C) z = w) :
    (ConPA.Machine.step (originalTable C))^[3] x = w := by
  rw [show 3 = 2+1 by decide,Function.iterate_succ_apply',
    show 2 = 1+1 by decide,Function.iterate_succ_apply',Function.iterate_one,h1,h2,h3]

/-- Native shortcut 26/1, with both right-neighbor bits zero. -/
theorem shortcut26 (l r : V) (b : r%2 = 1) (b1 : (r/2)%2 = 0) (b2 : ((r/2)/2)%2 = 0) :
    (ConPA.Machine.step (originalTable C))^[3] (config C.firstSource.val l r) =
      ConPA.Machine.step (acceleratedTable C) (config C.firstSource.val l r) := by
  let tail := ((r/2)/2)/2
  have h0 : stack (r/2) 1 = r := by simpa only [b] using components r
  have h1 : stack ((r/2)/2) 0 = r/2 := by simpa only [b1] using components (r/2)
  have h2 : stack tail 0 = (r/2)/2 := by simpa only [tail,b2] using components ((r/2)/2)
  have rForm : stack (stack (stack tail 0) 0) 1 = r := by rw [h2,h1,h0]
  rw [← rForm]
  have hA := right C.original C.originalCount C.firstSource.val 1 1 C.firstNext.val
    C.firstSource.isLt (by decide) l (stack (stack tail 0) 0) C.firstOriginal
  have hB := right C.original C.originalCount C.firstNext.val 0 0 C.firstTurn.val
    C.firstNext.isLt (by decide) (stack l 1) (stack tail 0) C.firstMiddle
  have hC := left C.original C.originalCount C.firstTurn.val 0 0 0 C.firstDestination.val
    C.firstTurn.isLt (by decide) (by decide) (stack l 1) tail C.firstLast
  have hF := right C.accelerated C.acceleratedCount C.firstSource.val 1 1 C.firstDestination.val
    C.firstSource.isLt (by decide) l (stack (stack tail 0) 0) C.firstFast
  simp only [Nat.cast_zero,Nat.cast_one] at hA hB hC hF
  exact (three C hA hB hC).trans hF.symm

/-- Native shortcut 101/0, with the left-neighbor bit zero. -/
theorem shortcut101 (l r : V) (a : l%2 = 0) (b : r%2 = 0) :
    (ConPA.Machine.step (originalTable C))^[3] (config C.secondSource.val l r) =
      ConPA.Machine.step (acceleratedTable C) (config C.secondSource.val l r) := by
  have lf : stack (l/2) 0 = l := by simpa only [a] using components l
  have rf : stack (r/2) 0 = r := by simpa only [b] using components r
  conv_lhs => rw [← lf,← rf]
  conv_rhs => rw [← lf,← rf]
  have hA := left C.original C.originalCount C.secondSource.val 0 0 0 C.firstSource.val
    C.secondSource.isLt (by decide) (by decide) (l/2) (r/2) C.secondOriginal
  have hB := right C.original C.originalCount C.firstSource.val 0 0 C.secondReturn.val
    C.firstSource.isLt (by decide) (l/2) (stack (r/2) 0) C.secondMiddle
  have hC := right C.original C.originalCount C.secondReturn.val 0 0 C.secondDestination.val
    C.secondReturn.isLt (by decide) (stack (l/2) 0) (r/2) C.secondLast
  have hF := right C.accelerated C.acceleratedCount C.secondSource.val 0 0 C.secondDestination.val
    C.secondSource.isLt (by decide) (stack (l/2) 0) (r/2) C.secondFast
  simp only [Nat.cast_zero] at hA hB hC hF
  exact (three C hA hB hC).trans hF.symm

def relation (x y : V) : Prop := invariant C x ∧ x = y

theorem relation_def : 𝚺₁-Relation (relation (V := V) C) := by
  letI := invariant_def (V := V) C
  unfold relation
  definability

private theorem segmentConfig (q : Fin 194) (b : Fin 2) (l r : V)
    (read : r%2 = (b.val : V)) (good : goodTape C q.val l r) :
    ∃ k : Nat, 0 < k ∧ relation C (ConPA.Machine.step (acceleratedTable C) (config q.val l r))
      ((ConPA.Machine.step (originalTable C))^[k] (config q.val l r)) := by
  have hb := b.isLt
  have hq := q.isLt
  have hf := stepRow C.accelerated q.val b.val l r hb (by rw [C.acceleratedCount]; omega) read
  change ConPA.Machine.step (acceleratedTable C) (config q.val l r) = next (atRow C.accelerated q.val b.val) l r at hf
  have inv : invariant C (ConPA.Machine.step (acceleratedTable C) (config q.val l r)) := by
    rw [hf]
    exact nextInvariant C q b l r good
  by_cases h65 : q.val = C.firstSource.val ∧ b.val = 1
  · have readOne : r%2 = 1 := by simpa only [h65.2,Nat.cast_one] using read
    obtain ⟨a, b0 | b2⟩ := good.2.2 h65.1
    · rw [readOne] at b0
      exact False.elim (Arithmetic.one_ne_zero b0)
    · refine ⟨3,by decide,inv,?_⟩
      rw [h65.1]
      exact (shortcut26 C l r readOne a b2).symm
  by_cases h111 : q.val = C.secondSource.val ∧ b.val = 0
  · have readZero : r%2 = 0 := by simpa only [h111.2,Nat.cast_zero] using read
    refine ⟨3,by decide,inv,?_⟩
    rw [h111.1]
    exact (shortcut101 C l r (good.1 h111.1) readZero).symm
  have hold := stepRow C.original q.val b.val l r hb
    (by rw [C.originalCount]; omega) read
  change ConPA.Machine.step (originalTable C) (config q.val l r) = next (atRow C.original q.val b.val) l r at hold
  have ordinary := C.ordinary q b (by simpa only [not_and_or] using h65) (by simpa only [not_and_or] using h111)
  refine ⟨1,by decide,inv,?_⟩
  rw [Function.iterate_one,hf,hold,ordinary]

theorem segment (x y : V) (aligned : relation C x y) (live : π₁ x ≠ (194 : V)) :
    ∃ k : Nat, 0 < k ∧ relation C (ConPA.Machine.step (acceleratedTable C) x) ((ConPA.Machine.step (originalTable C))^[k] y) := by
  obtain ⟨good,rfl⟩ := aligned
  obtain ⟨q,l,r,hq,hg,rfl⟩ := unpack C good
  have hq' : q ≠ 194 := by
    intro he
    apply live
    rw [he]
    simp [config]
  let control : Fin 194 := ⟨q,by omega⟩
  rcases mod_two r with hb | hb
  · exact segmentConfig C control 0 l r (by simpa using hb) hg
  · exact segmentConfig C control 1 l r (by simpa using hb) hg

private theorem absorb (x : V) (hx : π₁ x = (194 : V)) : ConPA.Machine.step (originalTable C) x = x := by
  have hx' : x = config 194 (π₁ (π₂ x)) (π₂ (π₂ x)) := by
    unfold config
    change π₁ x = ((194 : Nat) : V) at hx
    rw [←hx,pair_unpair,pair_unpair]
  conv_lhs => rw [hx']
  rw [halted C.original C.originalCount,←hx']

theorem sameHalt :
    (∃ n : V, π₁ (ConPA.Machine.run (originalTable C) n) = (194 : V)) ↔
      ∃ n : V, π₁ (ConPA.Machine.run (acceleratedTable C) n) = (194 : V) := by
  exact ConPA.Machine.Stutter.equivalent (acceleratedTable C) (originalTable C) 194 194 (relation C) (relation_def C)
    ⟨init C,rfl⟩ (fun _ _ h => by rw [h.2]) (absorb C) (segment C)

#print axioms nextInvariant
#print axioms sameHalt
end models
end PA194GuardedShortcuts
