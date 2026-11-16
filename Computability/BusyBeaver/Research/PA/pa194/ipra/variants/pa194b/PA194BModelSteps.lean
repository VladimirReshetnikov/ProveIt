import PA194BRows

/-! The generic table step on arithmetic tape halves, specialized to the two
PA194 tables. All tape halves may be nonstandard model values. -/

set_option autoImplicit false
set_option maxRecDepth 25000
set_option maxHeartbeats 2200000

namespace PA194BModelSteps
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194BRows

def indexedRow (values : List Action) (i : Nat) : ConPA.Machine.Row :=
  let a := values.getD i (0,0,194)
  ⟨i/2,i%2,a.1,a.2.1 != 0,a.2.2⟩

def table (values : List Action) : ConPA.Machine.Table :=
  (List.range values.length).map (indexedRow values)

theorem tableOld : table PA194Rows.rows = PA194GenericBridge.denseTable := rfl

theorem find (values : List Action) (q b : Nat) (hb : b < 2) (hi : 2*q+b < values.length) :
    (table values).find? (fun row => row.q == q && row.b == b) = some (indexedRow values (2*q+b)) := by
  rw [List.find?_eq_some_iff_getElem]
  constructor
  · simp only [Bool.and_eq_true, beq_iff_eq, indexedRow]
    constructor <;> omega
  · refine ⟨2*q+b, by simpa [table] using hi, ?_, ?_⟩
    · simp [table,hi]
    · intro j hj
      have hjn : j < values.length := by omega
      simp only [table,List.getElem_map,List.getElem_range,indexedRow,
        Bool.not_and,Bool.not_eq_true',beq_iff_eq]
      have hne : j / 2 ≠ q ∨ j % 2 ≠ b := by omega
      rcases hne with h | h <;> simp [h]

section models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def config (q : Nat) (l r : V) : V := ⟪(q : V),l,r⟫

noncomputable def next (a : Action) (l r : V) : V :=
  if a.2.1 = 0 then config a.2.2 (l/2) (4*(r/2)+2*(a.1 : V)+l%2)
  else config a.2.2 (2*l+(a.1 : V)) (r/2)

theorem stepRow (values : List Action) (q b : Nat) (l r : V) (hb : b < 2)
    (hi : 2*q+b < values.length) (hr : r % 2 = (b : V)) :
    ConPA.Machine.step (table values) (config q l r) =
      next (values.getD (2*q+b) (0,0,194)) l r := by
  classical
  rw [PA194GenericBridge.stepFind]
  simp only [config,pi₁_pair,pi₂_pair,hr]
  have h : (fun row : ConPA.Machine.Row => decide
      ((q : V) = (row.q : V) ∧ (b : V) = (row.b : V))) =
      (fun row => row.q == q && row.b == b) := by
    funext row
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq,Bool.and_eq_true,beq_iff_eq,Nat.cast_inj]
    exact ⟨fun h => ⟨h.1.symm,h.2.symm⟩,fun h => ⟨h.1.symm,h.2.symm⟩⟩
  rw [h,find values q b hb hi]
  simp only [indexedRow,next,ConPA.Machine.out]
  split <;> simp_all [config]

theorem halted (values : List Action) (hv : values.length = 388) (l r : V) :
    ConPA.Machine.step (table values) (config 194 l r) = config 194 l r := by
  classical
  rw [PA194GenericBridge.stepFind]
  have hn : (table values).find? (fun row => decide
      (π₁ (config 194 l r) = (row.q : V) ∧ π₂ (π₂ (config 194 l r)) % 2 = (row.b : V))) = none := by
    apply List.find?_eq_none.mpr
    intro row hrow
    simp only [table,List.mem_map,List.mem_range] at hrow
    obtain ⟨j,hj,rfl⟩ := hrow
    have hq : j/2 ≠ 194 := by omega
    have hq' : (194 : V) ≠ ((j/2 : Nat) : V) := by exact_mod_cast (Ne.symm hq)
    simp [config,indexedRow,hq']
  rw [hn]

def stack (r bit : V) : V := 2*r+bit

theorem stackDiv (r bit : V) (hb : bit < 2) : stack r bit / 2 = r :=
  div_mul_add' r 2 hb

theorem stackMod (r bit : V) (hb : bit < 2) : stack r bit % 2 = bit := by
  rw [stack,mul_comm]
  exact mod_mul_add_of_lt r 2 hb

theorem components (r : V) : stack (r/2) (r%2) = r := div_add_mod r 2

theorem right (values : List Action) (length : values.length = 388)
    (q b w dest : Nat) (hq : q < 194) (hb : b < 2) (l r : V)
    (act : values.getD (2*q+b) (0,0,194) = (w,1,dest)) :
    ConPA.Machine.step (table values) (config q l (stack r (b : V))) =
      config dest (stack l (w : V)) r := by
  have hb' : (b : V) < 2 := by exact_mod_cast hb
  rw [stepRow values q b l _ hb (by omega) (stackMod r _ hb'),act]
  change config dest (2*l+(w : V)) (stack r (b : V)/2) = _
  rw [stackDiv r _ hb']
  rfl

theorem left (values : List Action) (length : values.length = 388)
    (q a b w dest : Nat) (hq : q < 194) (ha : a < 2) (hb : b < 2) (l r : V)
    (act : values.getD (2*q+b) (0,0,194) = (w,0,dest)) :
    ConPA.Machine.step (table values) (config q (stack l (a : V)) (stack r (b : V))) =
      config dest l (stack (stack r (w : V)) (a : V)) := by
  have ha' : (a : V) < 2 := by exact_mod_cast ha
  have hb' : (b : V) < 2 := by exact_mod_cast hb
  rw [stepRow values q b _ _ hb (by omega) (stackMod r _ hb'),act]
  change config dest (stack l (a : V)/2) (4*(stack r (b : V)/2)+2*(w : V)+stack l (a : V)%2) = _
  rw [stackDiv l _ ha',stackDiv r _ hb',stackMod l _ ha']
  simp only [stack,mul_add,←mul_assoc,show (2 : V)*2 = 4 by norm_num]

#print axioms stepRow
#print axioms halted
#print axioms left
#print axioms right
end models
end PA194BModelSteps
