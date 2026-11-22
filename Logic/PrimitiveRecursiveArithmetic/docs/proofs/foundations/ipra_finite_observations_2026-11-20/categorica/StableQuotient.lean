import Std

/- The semantic refinement operator used by the finite antichain signature test.
Masks have exact Boolean values. All proofs below are constructive; decidability
and the N-round clock for finite stabilization are treated in the paper. -/
namespace FiniteClosure.Stability

abbrev Mask (A : Type) := A → Bool
abbrev Relation (A : Type) := A → A → Prop
abbrev Operator (A : Type) := Mask A → Mask A

def Refines {A} (P Q : Relation A) := ∀ a b, P a b → Q a b
def Saturated {A} (P : Relation A) (X : Mask A) := ∀ a b, P a b → X a = X b
def Stable {A} (T : Operator A) (P : Relation A) :=
  ∀ X, Saturated P X → Saturated P (T X)
def refine {A} (T : Operator A) (P : Relation A) : Relation A :=
  fun a b => P a b ∧ ∀ X, Saturated P X → T X a = T X b

theorem stable_iff_no_split {A} (T : Operator A) (P : Relation A) :
    Stable T P ↔ Refines P (refine T P) := by
  constructor
  · exact fun stable a b h => ⟨h, fun X hX => stable X hX a b h⟩
  · exact fun h X hX a b hab => (h a b hab).2 X hX

theorem survives_refine {A} {T : Operator A} {P Q : Relation A}
    (h : Refines Q P) (stable : Stable T Q) : Refines Q (refine T P) := by
  intro a b hab
  refine ⟨h a b hab, ?_⟩
  intro X hX
  have satQ : Saturated Q X := fun i j hij => hX i j (h i j hij)
  exact stable X satQ a b hab

def iter {X : Type} (f : X → X) (x : X) : Nat → X
  | 0 => x
  | n + 1 => f (iter f x n)

theorem stable_survives_all {A} {T : Operator A} {P Q : Relation A}
    (h : Refines Q P) (stable : Stable T Q) :
    ∀ n, Refines Q (iter (refine T) P n) := by
  intro n
  induction n with
  | zero => exact h
  | succ n ih => exact survives_refine ih stable

theorem iter_refines_initial {A} (T : Operator A) (P : Relation A) :
    ∀ n, Refines (iter (refine T) P n) P := by
  intro n
  induction n with
  | zero => exact fun _ _ h => h
  | succ n ih => exact fun a b h => ih a b h.1

/-- For a supplied stationary iteration index the final relation is stable and
is refined by every stable refinement of the initial relation. -/
theorem coarsest_at_fixed {A} {T : Operator A} (P : Relation A) (n : Nat)
    (stop : Refines (iter (refine T) P n) (iter (refine T) P (n+1))) :
    Stable T (iter (refine T) P n) ∧ Refines (iter (refine T) P n) P ∧
    (∀ Q, Refines Q P → Stable T Q → Refines Q (iter (refine T) P n)) :=
  ⟨(stable_iff_no_split _ _).2 stop, iter_refines_initial T P n, fun _ h s => stable_survives_all h s n⟩

section Lifting

variable {A B : Type} (T : Operator A) (q : A → B) (repr : B → A)
def kernel (a b : A) := q a = q b
def liftMask (Y : Mask B) : Mask A := fun a => Y (q a)
def quotientStep (Y : Mask B) : Mask B := fun b => T (liftMask q Y) (repr b)

theorem lift_step (sectionEq : ∀ b, q (repr b) = b) (s : Stable T (kernel q))
    (Y : Mask B) : liftMask q (quotientStep T q repr Y) = T (liftMask q Y) := by
  have hY : Saturated (kernel q) (liftMask q Y) := fun _ _ h => congrArg Y h
  funext a
  exact s _ hY (repr (q a)) a (sectionEq (q a))

theorem lift_all (sectionEq : ∀ b, q (repr b) = b) (s : Stable T (kernel q))
    (Y : Mask B) : ∀ n,
    liftMask q (iter (quotientStep T q repr) Y n) = iter T (liftMask q Y) n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => exact (lift_step T q repr sectionEq s _).trans (congrArg T ih)

end Lifting
end FiniteClosure.Stability
