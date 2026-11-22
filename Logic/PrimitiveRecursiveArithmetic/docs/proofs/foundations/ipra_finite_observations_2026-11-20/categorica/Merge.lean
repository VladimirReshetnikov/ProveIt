import Std

/- A semantic Lean 4 proof of the partition invariant used by the arithmetic
algorithm. Specialize V to Fin N. Lists store the most recent edge first. -/
namespace EffectiveFinality

inductive Walk {V : Type} (R : V → V → Prop) : V → V → Prop
  | trivial (x) : Walk R x x
  | edge {x y} : R x y → Walk R x y
  | reverse {x y} : Walk R x y → Walk R y x
  | join {x y z} : Walk R x y → Walk R y z → Walk R x z

def Adj {V : Type} (es : List (V × V)) (x y : V) := (x, y) ∈ es

theorem Walk.mapRel {V : Type} {R S : V → V → Prop}
    (h : ∀ x y, R x y → S x y) {x y} (w : Walk R x y) : Walk S x y := by
  induction w with
  | trivial => exact .trivial _
  | edge e => exact .edge (h _ _ e)
  | reverse _ ih => exact .reverse ih
  | join _ _ ih₁ ih₂ => exact .join ih₁ ih₂

theorem Walk.equalValues {V W : Type} {R : V → V → Prop} (f : V → W)
    (h : ∀ x y, R x y → f x = f y) {x y} (w : Walk R x y) : f x = f y := by
  induction w with
  | trivial => rfl
  | edge e => exact h _ _ e
  | reverse _ ih => exact ih.symm
  | join _ _ ih₁ ih₂ => exact ih₁.trans ih₂

section Labels

variable {V : Type} [DecidableEq V]

def replaceLabel (a b v : V) := if v = b then a else v

def label : List (V × V) → V → V
  | [], x => x
  | (a, b) :: es, x => replaceLabel (label es a) (label es b) (label es x)

theorem label_respects (es : List (V × V)) :
    ∀ x y, Adj es x y → label es x = label es y := by
  induction es with
  | nil => simp [Adj]
  | cons ab es ih =>
    rcases ab with ⟨a,b⟩
    intro x y h
    rcases List.mem_cons.mp h with he | he
    · cases he
      simp [label, replaceLabel]
    · exact congrArg (replaceLabel (label es a) (label es b)) (ih x y he)

theorem walk_label (es : List (V × V)) : ∀ x, Walk (Adj es) x (label es x) := by
  induction es with
  | nil => exact fun x => .trivial x
  | cons ab es ih =>
    rcases ab with ⟨a,b⟩
    have liftOld (x : V) : Walk (Adj ((a,b) :: es)) x (label es x) :=
      (ih x).mapRel (fun _ _ h => List.mem_cons_of_mem _ h)
    intro x
    by_cases h : label es x = label es b
    · have hx := liftOld x
      rw [h] at hx
      have hb : Walk (Adj ((a,b) :: es)) b a :=
        .reverse (.edge (List.mem_cons_self ..))
      simpa [label, replaceLabel, h] using
        (hx.join (liftOld b).reverse |>.join hb |>.join (liftOld a))
    · simpa [label, replaceLabel, h] using liftOld x

theorem same_label_iff (es : List (V × V)) (x y : V) :
    label es x = label es y ↔ Walk (Adj es) x y := by
  constructor
  · intro h
    have hx := walk_label es x
    rw [h] at hx
    exact hx.join (walk_label es y).reverse
  · exact Walk.equalValues (label es) (label_respects es)

theorem label_idempotent (es : List (V × V)) (x : V) :
    label es (label es x) = label es x :=
  ((same_label_iff es x (label es x)).2 (walk_label es x)).symm

end Labels
end EffectiveFinality
