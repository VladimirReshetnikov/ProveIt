module
public import M6.Logic.NativeNames
@[expose] public section

/-! Literal atom-label replacement from NumericNamed238.v at
jeff87654/busy-beaver@84049b5e753190cf328cbc2d2710791ad32ad59c.
This operation intentionally leaves binder labels unchanged. It is NOT
unconditionally capture-avoiding: the theorem requires both labels absent
from binders, and the concrete collision test demonstrates why.
Finite numeric proof readback and PA-internal compiler correctness are separate. -/
namespace M6.PA.NativeCalculus

def renameLabel (x y a : Nat) : Nat := if a = x then y else a

def Named.replace (x y : Nat) : Named → Named
  | .truth => .truth
  | .imp p q => .imp (p.replace x y) (q.replace x y)
  | .neg p => .neg (p.replace x y)
  | .mem a b => .mem (renameLabel x y a) (renameLabel x y b)
  | .eq a b => .eq (renameLabel x y a) (renameLabel x y b)
  | .all a p => .all a (p.replace x y)

theorem Named.replace_binders (p : Named) (x y v : Nat) :
    (p.replace x y).binders v = p.binders v := by
  induction p <;> simp_all [replace,binders]

/-- Exact node count and nested-binder invariant from NativeNamed238.v. -/
def Named.nodeCount : Named → Nat
  | .truth | .mem _ _ | .eq _ _ => 1
  | .imp p q => p.nodeCount + q.nodeCount + 1
  | .neg p | .all _ p => p.nodeCount + 1

def Named.distinctBinders : Named → Prop
  | .truth | .mem _ _ | .eq _ _ => True
  | .imp p q => p.distinctBinders ∧ q.distinctBinders
  | .neg p => p.distinctBinders
  | .all a p => p.binders a = false ∧ p.distinctBinders

theorem Named.replace_size (p : Named) (x y : Nat) :
    (p.replace x y).nodeCount = p.nodeCount := by
  induction p <;> simp_all [replace,nodeCount]

theorem Named.replace_distinct (p : Named) (x y : Nat) :
    (p.replace x y).distinctBinders ↔ p.distinctBinders := by
  induction p <;> simp_all [replace,distinctBinders,replace_binders]

/-- Inner binders move first. Different sibling branches may reuse labels. -/
def Named.freshen : Named → Nat → Named
  | .truth, _ => .truth
  | .mem a b, _ => .mem a b
  | .eq a b, _ => .eq a b
  | .imp p q, lo => .imp (p.freshen lo) (q.freshen lo)
  | .neg p, lo => .neg (p.freshen lo)
  | .all a p, lo => .all lo ((p.freshen (lo+1)).replace a lo)

theorem Named.freshen_binders_below (p : Named) (lo v : Nat) (hv : v < lo) :
    (p.freshen lo).binders v = false := by
  induction p generalizing lo with
  | truth | mem | eq => rfl
  | neg p ih => exact ih lo hv
  | imp p q ihp ihq => simp [freshen,binders,ihp lo hv,ihq lo hv]
  | all a p ih =>
    have hne : v ≠ lo := Nat.ne_of_lt hv
    simp [freshen,binders,replace_binders,hne,ih (lo+1) (by omega)]

theorem Named.freshen_distinct (p : Named) (lo : Nat) :
    (p.freshen lo).distinctBinders := by
  induction p generalizing lo with
  | truth | mem | eq => trivial
  | neg p ih => exact ih lo
  | imp p q ihp ihq => exact ⟨ihp lo,ihq lo⟩
  | all a p ih =>
    exact ⟨by simpa [freshen,replace_binders] using p.freshen_binders_below (lo+1) lo (by omega),
      (p.freshen (lo+1)).replace_distinct a lo |>.mpr (ih (lo+1))⟩

theorem Named.freshen_size (p : Named) (lo : Nat) :
    (p.freshen lo).nodeCount = p.nodeCount := by
  induction p generalizing lo <;> simp_all [freshen,nodeCount,replace_size]

theorem renameLabel_roundtrip (x y a : Nat) (ha : y ≠ a) :
    renameLabel y x (renameLabel x y a) = a := by
  by_cases h : a = x
  · simp [renameLabel,h]
  · simp [renameLabel,h,Ne.symm ha]

theorem Named.replace_roundtrip (p : Named) (x y : Nat) (hy : p.names y = false) :
    (p.replace x y).replace y x = p := by
  induction p with
  | truth => rfl
  | neg p ih => simp only [names] at hy; simp [replace,ih hy]
  | imp p q ihp ihq =>
    simp only [names,Bool.or_eq_false_iff] at hy
    simp [replace,ihp hy.1,ihq hy.2]
  | mem a b =>
    simp only [names,Bool.or_eq_false_iff,beq_eq_false_iff_ne] at hy
    simp [replace,renameLabel_roundtrip x y a hy.1,renameLabel_roundtrip x y b hy.2]
  | eq a b =>
    simp only [names,Bool.or_eq_false_iff,beq_eq_false_iff_ne] at hy
    simp [replace,renameLabel_roundtrip x y a hy.1,renameLabel_roundtrip x y b hy.2]
  | all a p ih =>
    simp only [names,Bool.or_eq_false_iff] at hy
    simp [replace,ih hy.2]

theorem rename_update {V : Type u} (env : Nat → V) (x y a : Nat) (z : V)
    (hxa : x ≠ a) (hya : y ≠ a) :
    (fun v => if renameLabel x y v = a then z else env (renameLabel x y v)) =
    (fun v => if v = a then z else env (renameLabel x y v)) := by
  funext v
  by_cases hv : v = x
  · simp [renameLabel,hv,hxa,hya]
  · simp [renameLabel,hv]

theorem Named.replace_eval {V : Type u} (R E : V → V → Prop) (p : Named)
    (x y : Nat) (hx : p.binders x = false) (hy : p.binders y = false)
    (env : Nat → V) :
    (p.replace x y).eval R E env ↔
      p.eval R E (fun v => env (renameLabel x y v)) := by
  induction p generalizing env with
  | truth => rfl
  | mem a b => rfl
  | eq a b => rfl
  | neg p ih => exact not_congr (ih hx hy env)
  | imp p q ihp ihq =>
    simp only [binders,Bool.or_eq_false_iff] at hx hy
    simp only [replace,eval,ihp hx.1 hy.1,ihq hx.2 hy.2]
  | all a p ih =>
    simp only [binders,Bool.or_eq_false_iff,beq_eq_false_iff_ne] at hx hy
    simp only [replace,eval]
    apply forall_congr'
    intro z
    rw [ih hx.2 hy.2]
    rw [rename_update env x y a z hx.1 hy.1]

/-- Dropping the target-binder freshness condition really captures a variable. -/
theorem replacement_capture_counterexample :
    ((Named.all 1 (.eq 0 1)).replace 0 1).eval (fun _ _ : Nat => False) Eq (fun _ => 0) ∧
    ¬ (Named.all 1 (.eq 0 1)).eval (fun _ _ : Nat => False) Eq (fun _ => 0) := by
  constructor
  · simp [Named.replace,renameLabel,Named.eval]
  · intro h
    have bad := h 1
    simp [Named.eval] at bad

#print axioms Named.replace_roundtrip
#print axioms Named.replace_eval
#print axioms Named.freshen_distinct
#print axioms Named.freshen_size
#print axioms replacement_capture_counterexample
end M6.PA.NativeCalculus

