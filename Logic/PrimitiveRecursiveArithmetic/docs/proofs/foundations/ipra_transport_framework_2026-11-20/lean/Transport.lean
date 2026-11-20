import Std

/-! Error propagation through presented paths. A bound is an integer number of
precision units. The relation may depend on the precision, fixed in an instance. -/
namespace PresentedTransport

variable {E X R : Type}

def run (step : E → X → X) : List E → X → X
  | [], x => x
  | e :: w, x => run step w (step e x)

theorem run_append (step : E → X → X) (u v : List E) (x : X) :
    run step (u ++ v) x = run step v (run step u x) := by
  induction u generalizing x with
  | nil => rfl
  | cons e u ih => exact ih (step e x)

def carry (L b : E → Nat) : List E → Nat → Nat
  | [], q => q
  | e :: w, q => carry L b w (L e * q + b e)

structure Laws (step : E → X → X) (L b : E → Nat)
    (near : Nat → X → X → Prop) : Prop where
  refl : ∀ x, near 0 x x
  symm : ∀ {j x y}, near j x y → near j y x
  triangle : ∀ {i j x y z}, near i x y → near j y z → near (i+j) x z
  applyEdge : ∀ e {i x y}, near i x y → near (L e * i + b e) (step e x) (step e y)

variable {L b : E → Nat} {step : E → X → X} {near : Nat → X → X → Prop}

theorem carry_sound (laws : Laws step L b near) (w : List E)
    {q : Nat} {x y : X} (h : near q x y) :
    near (carry L b w q) (run step w x) (run step w y) := by
  induction w generalizing q x y with
  | nil => exact h
  | cons e w ih => exact ih (laws.applyEdge e h)

/-- The index is the computed error budget of the supplied proof. -/
inductive Rewrite (left right : R → List E) (cost : R → Nat) (L b : E → Nat) :
    List E → List E → Nat → Prop where
  | stay (w) : Rewrite left right cost L b w w 0
  | cell (p s : List E) (r : R) :
      Rewrite left right cost L b (p ++ left r ++ s) (p ++ right r ++ s)
        (carry L b s (cost r))
  | reverse {u v q} : Rewrite left right cost L b u v q → Rewrite left right cost L b v u q
  | join {u v w i j} : Rewrite left right cost L b u v i → Rewrite left right cost L b v w j →
      Rewrite left right cost L b u w (i+j)

theorem rewrite_sound {left right : R → List E} {cost : R → Nat}
    (laws : Laws step L b near)
    (cells : ∀ r x, near (cost r) (run step (left r) x) (run step (right r) x))
    {u v q} (cert : Rewrite left right cost L b u v q) (x : X) :
    near q (run step u x) (run step v x) := by
  induction cert with
  | stay w => exact laws.refl _
  | cell p s r =>
    simpa only [run_append] using carry_sound laws s (cells r (run step p x))
  | reverse _ ih => exact laws.symm ih
  | join _ _ ih₁ ih₂ => exact laws.triangle ih₁ ih₂

#print axioms rewrite_sound
end PresentedTransport
