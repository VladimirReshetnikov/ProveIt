import PA194FastInvariant

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4500000

namespace PA194FastSegment
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194BModelSteps
open PA194FastRows (table oldTable rows rowCount action oldAction sameExcept)
open PA194FastInvariant

section models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem three {x y z w : V}
    (h1 : ConPA.Machine.step oldTable x = y) (h2 : ConPA.Machine.step oldTable y = z)
    (h3 : ConPA.Machine.step oldTable z = w) :
    (ConPA.Machine.step oldTable)^[3] x = w := by
  rw [show 3 = 2+1 by decide,Function.iterate_succ_apply',
    show 2 = 1+1 by decide,Function.iterate_succ_apply',Function.iterate_one,h1,h2,h3]

/-- Native shortcut 26/1, with both right-neighbor bits zero. -/
theorem shortcut26 (l r : V) (b : r%2 = 1) (b1 : (r/2)%2 = 0) (b2 : ((r/2)/2)%2 = 0) :
    (ConPA.Machine.step oldTable)^[3] (config 65 l r) =
      ConPA.Machine.step table (config 65 l r) := by
  let tail := ((r/2)/2)/2
  have h0 : stack (r/2) 1 = r := by simpa only [b] using components r
  have h1 : stack ((r/2)/2) 0 = r/2 := by simpa only [b1] using components (r/2)
  have h2 : stack tail 0 = (r/2)/2 := by simpa only [tail,b2] using components ((r/2)/2)
  have rForm : stack (stack (stack tail 0) 0) 1 = r := by rw [h2,h1,h0]
  rw [← rForm]
  have hA := right PA194Rows.rows PA194GenericBridge.rowCount 65 1 1 49
    (by decide) (by decide) l (stack (stack tail 0) 0) (by rfl)
  have hB := right PA194Rows.rows PA194GenericBridge.rowCount 49 0 0 69
    (by decide) (by decide) (stack l 1) (stack tail 0) (by rfl)
  have hC := left PA194Rows.rows PA194GenericBridge.rowCount 69 0 0 0 94
    (by decide) (by decide) (by decide) (stack l 1) tail (by rfl)
  have hF := right rows rowCount 65 1 1 94
    (by decide) (by decide) l (stack (stack tail 0) 0) (by rfl)
  simp only [Nat.cast_zero,Nat.cast_one] at hA hB hC hF
  exact (three hA hB hC).trans hF.symm

/-- Native shortcut 101/0, with the left-neighbor bit zero. -/
theorem shortcut101 (l r : V) (a : l%2 = 0) (b : r%2 = 0) :
    (ConPA.Machine.step oldTable)^[3] (config 111 l r) =
      ConPA.Machine.step table (config 111 l r) := by
  have lf : stack (l/2) 0 = l := by simpa only [a] using components l
  have rf : stack (r/2) 0 = r := by simpa only [b] using components r
  conv_lhs => rw [← lf,← rf]
  conv_rhs => rw [← lf,← rf]
  have hA := left PA194Rows.rows PA194GenericBridge.rowCount 111 0 0 0 65
    (by decide) (by decide) (by decide) (l/2) (r/2) (by rfl)
  have hB := right PA194Rows.rows PA194GenericBridge.rowCount 65 0 0 91
    (by decide) (by decide) (l/2) (stack (r/2) 0) (by rfl)
  have hC := right PA194Rows.rows PA194GenericBridge.rowCount 91 0 0 110
    (by decide) (by decide) (stack (l/2) 0) (r/2) (by rfl)
  have hF := right rows rowCount 111 0 0 110
    (by decide) (by decide) (stack (l/2) 0) (r/2) (by rfl)
  simp only [Nat.cast_zero] at hA hB hC hF
  exact (three hA hB hC).trans hF.symm

def relation (x y : V) : Prop := invariant x ∧ x = y

theorem relation_def : 𝚺₁-Relation (relation (V := V)) := by
  letI := invariant_def (V := V)
  unfold relation
  definability

private theorem segmentConfig (q : Fin 194) (b : Fin 2) (l r : V)
    (read : r%2 = (b.val : V)) (good : goodTape q.val l r) :
    ∃ k : Nat, 0 < k ∧ relation (ConPA.Machine.step table (config q.val l r))
      ((ConPA.Machine.step oldTable)^[k] (config q.val l r)) := by
  have hb := b.isLt
  have hq := q.isLt
  have hf := stepRow rows q.val b.val l r hb (by rw [rowCount]; omega) read
  change ConPA.Machine.step table (config q.val l r) = next (action q.val b.val) l r at hf
  have inv : invariant (ConPA.Machine.step table (config q.val l r)) := by
    rw [hf]
    exact nextInvariant q b l r good
  by_cases h65 : q.val = 65 ∧ b.val = 1
  · have readOne : r%2 = 1 := by simpa only [h65.2,Nat.cast_one] using read
    obtain ⟨a, b0 | b2⟩ := good.2.2 h65.1
    · rw [readOne] at b0
      exact False.elim (Arithmetic.one_ne_zero b0)
    · refine ⟨3,by decide,inv,?_⟩
      rw [h65.1]
      exact (shortcut26 l r readOne a b2).symm
  by_cases h111 : q.val = 111 ∧ b.val = 0
  · have readZero : r%2 = 0 := by simpa only [h111.2,Nat.cast_zero] using read
    refine ⟨3,by decide,inv,?_⟩
    rw [h111.1]
    exact (shortcut101 l r (good.1 h111.1) readZero).symm
  have hold := stepRow PA194Rows.rows q.val b.val l r hb
    (by rw [PA194GenericBridge.rowCount]; omega) read
  change ConPA.Machine.step oldTable (config q.val l r) = next (oldAction q.val b.val) l r at hold
  have ordinary := sameExcept q b (by simpa only [not_and_or] using h65) (by simpa only [not_and_or] using h111)
  refine ⟨1,by decide,inv,?_⟩
  rw [Function.iterate_one,hf,hold,ordinary]

theorem segment (x y : V) (aligned : relation x y) (live : π₁ x ≠ (194 : V)) :
    ∃ k : Nat, 0 < k ∧ relation (ConPA.Machine.step table x) ((ConPA.Machine.step oldTable)^[k] y) := by
  obtain ⟨good,rfl⟩ := aligned
  obtain ⟨q,l,r,hq,hg,rfl⟩ := unpack good
  have hq' : q ≠ 194 := by
    intro he
    apply live
    rw [he]
    simp [config]
  let control : Fin 194 := ⟨q,by omega⟩
  rcases mod_two r with hb | hb
  · exact segmentConfig control 0 l r (by simpa using hb) hg
  · exact segmentConfig control 1 l r (by simpa using hb) hg

private theorem absorb (x : V) (hx : π₁ x = (194 : V)) : ConPA.Machine.step oldTable x = x := by
  have hx' : x = config 194 (π₁ (π₂ x)) (π₂ (π₂ x)) := by
    unfold config
    change π₁ x = ((194 : Nat) : V) at hx
    rw [←hx,pair_unpair,pair_unpair]
  conv_lhs => rw [hx']
  rw [halted PA194Rows.rows PA194GenericBridge.rowCount,←hx']

theorem sameHalt :
    (∃ n : V, π₁ (ConPA.Machine.run PA194GenericBridge.denseTable n) = (194 : V)) ↔
      ∃ n : V, π₁ (ConPA.Machine.run table n) = (194 : V) := by
  rw [← tableOld]
  exact ConPA.Machine.Stutter.equivalent table oldTable 194 194 relation relation_def
    ⟨init,rfl⟩ (fun _ _ h => by rw [h.2]) absorb segment

#print axioms shortcut26
#print axioms shortcut101
#print axioms sameHalt
end models
end PA194FastSegment
