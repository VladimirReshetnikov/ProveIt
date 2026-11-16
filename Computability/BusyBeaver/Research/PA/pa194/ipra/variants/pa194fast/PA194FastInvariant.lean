import PA194FastRows
import ConPAMachineStutter
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4500000

namespace PA194FastInvariant
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PA194BModelSteps
open PA194FastRows (rows rowCount action incoming)

section models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Neighbor bits sufficient for the two literal shortcuts, in the dense
    control names of the primary table. -/
def goodTape (q : Nat) (l r : V) : Prop :=
  (q = 111 → l%2 = 0) ∧ (q = 46 → l%2 = 0 ∨ (r/2)%2 = 0) ∧
  (q = 65 → (r/2)%2 = 0 ∧ (r%2 = 0 ∨ ((r/2)/2)%2 = 0))

noncomputable def invariant (x : V) : Prop :=
  let q := π₁ x
  let l := π₁ (π₂ x)
  let r := π₂ (π₂ x)
  q < 195 ∧ (q = 111 → l%2 = 0) ∧ (q = 46 → l%2 = 0 ∨ (r/2)%2 = 0) ∧
    (q = 65 → (r/2)%2 = 0 ∧ (r%2 = 0 ∨ ((r/2)/2)%2 = 0))

theorem invariant_def : 𝚺₁-Predicate (invariant (V := V)) := by
  unfold invariant
  simp only [imp_iff_not_or]
  definability

theorem config_iff (q : Nat) (l r : V) : invariant (config q l r) ↔ q < 195 ∧ goodTape q l r := by
  have hBound : ((q : V) < 195) ↔ q < 195 := Nat.cast_lt
  have h111 : ((q : V) = 111) ↔ q = 111 := Nat.cast_inj
  have h46 : ((q : V) = 46) ↔ q = 46 := Nat.cast_inj
  have h65 : ((q : V) = 65) ↔ q = 65 := Nat.cast_inj
  simp only [invariant,config,pi₁_pair,pi₂_pair,hBound,h111,h46,h65,goodTape]

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

theorem unpack {x : V} (h : invariant x) :
    ∃ q : Nat, ∃ l r : V, q < 195 ∧ goodTape q l r ∧ x = config q l r := by
  have bound : π₁ x < (195 : V) := h.1
  obtain ⟨q, hq, hc⟩ := boundedControl (π₁ x) 195 bound
  have he : x = config q (π₁ (π₂ x)) (π₂ (π₂ x)) := by
    unfold config
    rw [← hc,pair_unpair,pair_unpair]
  have hg := (config_iff q (π₁ (π₂ x)) (π₂ (π₂ x))).mp (he ▸ h)
  exact ⟨q,_,_,hq,hg.2,he⟩

theorem init : invariant (0 : V) := by
  have g : goodTape 0 (0 : V) 0 := by simp [goodTape]
  have h := (config_iff 0 (0 : V) 0).mpr ⟨by decide,g⟩
  simpa [config,pair] using h

/-- The accelerated table preserves the invariant. Its only remaining
    incoming row to dense control 65 is the left move of control 46. -/
theorem nextInvariant (q : Fin 194) (b : Fin 2) (l r : V) (old : goodTape q.val l r) :
    invariant (next (action q.val b.val) l r) := by
  let a := action q.val b.val
  obtain ⟨bound, into101, into11, into26⟩ := incoming q b
  change a.2.2 < 195 at bound
  change a.2.2 = 111 → a.1 = 0 ∧ a.2.1 = 1 at into101
  change a.2.2 = 46 → a.1 = 0 at into11
  change a.2.2 = 65 → q.val = 46 ∧ b.val = 0 ∧ a.1 = 0 ∧ a.2.1 = 0 at into26
  change invariant (next a l r)
  by_cases move : a.2.1 = 0
  · let middle := stack (r/2) (a.1 : V)
    have hbits : 4*(r/2)+2*(a.1 : V)+l%2 = stack middle (l%2) := by
      dsimp [middle,stack]
      ring
    have hb : l%2 < 2 := mod_lt l (by norm_num)
    rw [next,if_pos move,hbits]
    apply (config_iff _ _ _).mpr
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
    apply (config_iff _ _ _).mpr
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

#print axioms nextInvariant
end models
end PA194FastInvariant
