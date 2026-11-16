import PA194SELRows
import PA194BFinite

/-! Kernel certificates for the two simultaneous contextual folds in the
literal PA194SEL table. -/

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0

namespace PA194SELRows
open PA194BRows (primary)

structure Fold where
  origin : Nat
  history : Nat
  selector : Nat
  helper : Nat

/-- Primary dense origin, retained left bit, SEL dense selector and helper. -/
def folds : List Fold := [
  ⟨134,0,67,80⟩,
  ⟨47,1,67,93⟩,
  ⟨88,0,99,89⟩,
  ⟨77,1,99,82⟩
]

def special (q : Nat) : Option Fold := folds.find? (fun f => f.origin == q)

def translated (a : Action) : Action := (a.1,a.2.1,rho a.2.2)

def reorder (q : Nat) : Nat := labels.idxOf (primaryLabels.getD q 254)

def expectedNative (q b : Nat) : Action :=
  match primaryLabels.getD q 254,b with
  | 12,0 => (0,0,38)
  | 38,0 => (0,1,98)
  | 38,1 => (1,1,19)
  | 104,1 => (1,1,127)
  | 124,0 => (0,1,8)
  | 124,1 => (1,1,59)
  | 127,0 => (0,0,124)
  | 312,1 => (1,1,12)
  | _,_ => PA194BRows.nativeAction primaryLabels (primary q b)

theorem counts : actions.length = 388 ∧ labels.length = 195 ∧
    primaryLabels.length = 195 ∧ targets.length = 195 := by decide +kernel

theorem labelTransport : ∀ q : Fin 195,
    labels.getD (reorder q.val) 254 = primaryLabels.getD q.val 254 ∧ reorder q.val < 195 := by
  decide +kernel

theorem nativeDelta : ∀ (q : Fin 194) (b : Fin 2),
    PA194BRows.nativeAction labels (action (reorder q.val) b.val) = expectedNative q.val b.val := by
  decide +kernel

theorem rhoLabels : ∀ q : Fin 195,
    rho q.val = match primaryLabels.getD q.val 254 with
      | 38 => labels.idxOf 12
      | 124 => labels.idxOf 127
      | _ => reorder q.val := by decide +kernel

theorem rhoHalt : rho 194 = 194 := by decide +kernel
theorem rhoStart : rho 0 = 0 := by decide +kernel
theorem rhoLive : ∀ q : Fin 194, rho q.val < 194 := by decide +kernel

theorem ordinary : ∀ (q : Fin 194) (b : Fin 2), (special q.val).isNone = true ∨ b.val = 1 →
    action (rho q.val) b.val = translated (primary q.val b.val) := by decide +kernel

def validSpecial (q : Nat) : Bool :=
  match special q with
  | none => true
  | some f => decide <| f.history < 2 ∧ f.selector < 194 ∧ f.helper < 194 ∧
      primary q 0 = (0,1,(primary q 0).2.2) ∧
      action (rho q) 0 = (0,0,f.selector) ∧
      action f.selector f.history = (f.history,1,f.helper) ∧
      action f.helper 0 = (0,1,rho (primary q 0).2.2)

theorem specialCertificate : ∀ q : Fin 194, validSpecial q.val = true := by decide +kernel

theorem incomingCertificate : ∀ (q : Fin 194) (b : Fin 2),
    folds.all (fun f => decide ((primary q.val b.val).2.2 = f.origin →
      (primary q.val b.val).1 = f.history ∧ (primary q.val b.val).2.1 = 1)) = true := by
  decide +kernel

theorem found {q : Nat} {f : Fold} (h : special q = some f) :
    f ∈ folds ∧ f.origin = q := by
  have hb := List.find?_some (p := fun g : Fold => g.origin == q) (a := f) (l := folds) h
  exact ⟨List.mem_of_find?_eq_some h,beq_iff_eq.mp hb⟩

theorem incoming (q : Fin 194) (b : Fin 2) (f : Fold) (hf : f ∈ folds)
    (h : (primary q.val b.val).2.2 = f.origin) :
    (primary q.val b.val).1 = f.history ∧ (primary q.val b.val).2.1 = 1 :=
  (of_decide_eq_true (List.all_eq_true.mp (incomingCertificate q b) f hf)) h

theorem blankNotFolded : ∀ f ∈ folds, f.origin ≠ 0 := by
  intro f h
  simp only [folds,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl <;> decide

theorem foldBounds : ∀ f ∈ folds, f.origin < 194 ∧ f.history < 2 := by
  intro f h
  simp only [folds,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl <;> decide

#print axioms nativeDelta
#print axioms ordinary
#print axioms specialCertificate
#print axioms incoming
end PA194SELRows
