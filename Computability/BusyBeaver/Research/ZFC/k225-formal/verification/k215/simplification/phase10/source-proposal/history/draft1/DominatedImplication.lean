import Init

/-!
A representation-independent dominated implication theorem.

The 52-step condensed-detachment derivation is adapted from ProveIt commit
4fdc59197a. Four discarded filler terms are chosen reflexively rather than at
numeric zero, and five detachments use an arbitrary private seed. Thus no
bottom element, injectivity, transitivity, or zero-collapse law is needed.
The short semantic tail retains composition and pointwise lifting; the seed
is discharged by a reflexive dominated instance in every public theorem.
This scratch source has not yet been checked by the Lean kernel.
-/
namespace SetTheory.BusyBeaver.ZFC.DominatedImplication

universe v

structure Language (A : Type v) where
  imp : A → A → A
  below : A → A → Prop
  refl : ∀ a, below a a
  grow_left : ∀ {u x : A} (y : A), below u x → below u (imp x y)
  grow_right : ∀ {u y : A} (x : A), below u y → below u (imp x y)

def rho8 {A : Type v} (L : Language A) (a b c u : A) : A :=
  L.imp (L.imp (L.imp c u) a) (L.imp (L.imp a c) (L.imp b c))

structure Restricted {A : Type v} (L : Language A) (T : A → Prop) : Prop where
  mp : ∀ {a b : A}, T (L.imp a b) → T a → T b
  rho8 : ∀ a b c u : A, L.below u a → T (DominatedImplication.rho8 L a b c u)

private structure WithSeed {A : Type v} (L : Language A) (τ : A) (T : A → Prop)
    : Prop extends Restricted L T where
  truth : T τ

section
variable {A : Type v} {L : Language A} {τ : A} {T : A → Prop}
local notation "wim" => L.imp
local infix:50 " ≼ " => L.below

private theorem le_l {u x : A} (y : A) (h : u ≼ x) : u ≼ wim x y :=
  L.grow_left y h
private theorem le_r {u y : A} (x : A) (h : u ≼ y) : u ≼ wim x y :=
  L.grow_right x h

variable (h : WithSeed L τ T)
include h

private theorem d1 (v0 v1 v2 v3 v4 : A) (hb0 : v3 ≼ v0) :
    T (wim (wim (wim (wim v0 v1) (wim v2 v1)) (wim v1 v3)) (wim v4 (wim v1 v3))) :=
  h.mp (h.rho8 (wim (wim v0 v1) (wim v2 v1)) v4 (wim v1 v3) v0 (le_l (wim v2 v1) (le_l v1 (L.refl _)))) (h.rho8 v0 v2 v1 v3 hb0)

private theorem d2 (v0 v1 v2 v3 v4 v5 : A) (hb0 : v2 ≼ v3) :
    T (wim (wim (wim v0 (wim v1 v2)) (wim (wim v3 v1) (wim v4 v1))) (wim v5 (wim (wim v3 v1) (wim v4 v1)))) :=
  h.mp (h.rho8 (wim v0 (wim v1 v2)) v5 (wim (wim v3 v1) (wim v4 v1)) (wim v1 v2) (le_r v0 (L.refl _))) (d1 h v3 v1 v4 v2 v0 hb0)

private theorem d3 (v0 v1 v2 v3 : A) :
    T (wim v0 (wim (wim (wim v1 v2) v1) (wim v3 v1))) :=
  h.mp (d2 h (wim v1 (wim v1 v2)) v1 v2 (wim v1 v2) v3 v0 (le_r v1 (L.refl _))) (h.rho8 (wim v1 v2) v3 v1 (wim v1 v2) (L.refl _))

private theorem d4 (v0 v1 v2 : A) :
    T (wim (wim (wim v0 v1) v0) (wim v2 v0)) :=
  h.mp (d3 h τ v0 v1 v2) h.truth

private theorem d5 (v0 v1 v2 v3 : A) :
    T (wim (wim (wim v0 v1) (wim v1 v2)) (wim v3 (wim v1 v2))) :=
  h.mp (h.rho8 (wim v0 v1) v3 (wim v1 v2) v1 (le_r v0 (L.refl _))) (d4 h v1 v2 v0)

private theorem d6 (v0 v1 v2 v3 v4 : A) :
    T (wim (wim (wim v0 (wim v1 v2)) (wim v3 v1)) (wim v4 (wim v3 v1))) :=
  h.mp (h.rho8 (wim v0 (wim v1 v2)) v4 (wim v3 v1) (wim v1 v2) (le_r v0 (L.refl _))) (d5 h v3 v1 v2 v0)

private theorem d7 (v0 v1 v2 v3 : A) :
    T (wim v0 (wim (wim (wim (wim v1 v2) v3) v2) (wim v1 v2))) :=
  h.mp (d6 h (wim v2 (wim (wim v1 v2) v3)) (wim v1 v2) v3 (wim (wim (wim v1 v2) v3) v2) v0) (h.rho8 (wim (wim v1 v2) v3) v1 v2 (wim (wim v1 v2) v3) (L.refl _))

private theorem d8 (v0 v1 v2 v3 v4 v5 : A) :
    T (wim (wim (wim v0 (wim v1 v2)) (wim v3 (wim v2 v4))) (wim v5 (wim v3 (wim v2 v4)))) :=
  h.mp (h.rho8 (wim v0 (wim v1 v2)) v5 (wim v3 (wim v2 v4)) (wim v1 v2) (le_r v0 (L.refl _))) (d6 h v3 v2 v4 v1 v0)

private theorem d9 (v0 v1 v2 : A) :
    T (wim (wim (wim (wim v0 v1) v2) v1) (wim v0 v1)) :=
  h.mp (d7 h τ v0 v1 v2) h.truth

private theorem d10 (v0 v1 v2 v3 : A) :
    T (wim v0 (wim (wim (wim v1 v2) v3) (wim v2 v3))) :=
  h.mp (d8 h (wim v3 (wim v1 v2)) v1 v2 (wim (wim v1 v2) v3) v3 v0) (h.rho8 (wim v1 v2) v2 v3 (wim v1 v2) (L.refl _))

private theorem d11 (v0 v1 v2 v3 : A) :
    T (wim (wim (wim v0 v1) (wim (wim v0 v1) v2)) (wim v3 (wim (wim v0 v1) v2))) :=
  h.mp (h.rho8 (wim v0 v1) v3 (wim (wim v0 v1) v2) v1 (le_r v0 (L.refl _))) (d9 h v0 v1 v2)

private theorem d12 (v0 v1 : A) :
    T (wim v0 (wim v1 v0)) :=
  h.mp (d9 h v0 (wim v1 v0) v0) (d4 h v0 (wim v1 v0) v1)

private theorem d13 (v0 v1 v2 : A) :
    T (wim (wim (wim v0 v1) v2) (wim v1 v2)) :=
  h.mp (d10 h τ v0 v1 v2) h.truth

private theorem d14 (v0 v1 v2 : A) :
    T (wim v0 (wim (wim (wim v1 v2) v1) v1)) :=
  h.mp (d11 h (wim v1 v2) v1 v1 v0) (d4 h v1 v2 (wim (wim v1 v2) v1))

private theorem d15 (v0 v1 v2 v3 : A) :
    T (wim (wim (wim v0 (wim v1 v2)) v1) (wim v3 v1)) :=
  h.mp (h.rho8 (wim v0 (wim v1 v2)) v3 v1 v2 (le_r v0 (le_r v1 (L.refl _)))) (d12 h (wim v1 v2) v0)

private theorem d16 (v0 v1 v2 : A) :
    T (wim v0 (wim (wim v0 v1) (wim v2 v1))) :=
  h.mp (d13 h (wim v1 v0) v0 (wim (wim v0 v1) (wim v2 v1))) (h.rho8 v0 v2 v1 v0 (L.refl _))

private theorem d17 (v0 v1 v2 : A) :
    T (wim v0 (wim v1 (wim v2 v0))) :=
  h.mp (d13 h v2 v0 (wim v1 (wim v2 v0))) (d12 h (wim v2 v0) v1)

private theorem d18 (v0 v1 : A) :
    T (wim (wim (wim v0 v1) v0) v0) :=
  h.mp (d14 h τ v0 v1) h.truth

private theorem d19 (v0 v1 v2 v3 v4 : A) :
    T (wim (wim (wim (wim (wim v0 v1) v2) (wim v3 v2)) v0) (wim v4 v0)) :=
  h.mp (h.rho8 (wim (wim (wim v0 v1) v2) (wim v3 v2)) v4 v0 v1 (le_l (wim v3 v2) (le_l v2 (le_r v0 (L.refl _))))) (d16 h (wim v0 v1) v2 v3)

private theorem d20 (v0 v1 v2 : A) :
    T (wim (wim v0 (wim v0 v1)) (wim v2 (wim v0 v1))) :=
  h.mp (h.rho8 v0 v2 (wim v0 v1) v0 (L.refl _)) (d18 h v0 v1)

private theorem d21 (v0 v1 v2 : A) :
    T (wim v0 (wim (wim v1 (wim v1 v2)) (wim v1 v2))) :=
  h.mp (d11 h v1 (wim v1 v2) (wim v1 v2) v0) (d20 h v1 v2 (wim v1 (wim v1 v2)))

private theorem d22 (v0 v1 : A) :
    T (wim (wim v0 (wim v0 v1)) (wim v0 v1)) :=
  h.mp (d21 h τ v0 v1) h.truth

private theorem d23 (v0 v1 v2 : A) :
    T (wim (wim (wim v0 (wim v1 v2)) v1) v1) :=
  h.mp (d22 h (wim (wim v0 (wim v1 v2)) v1) v1) (d15 h v0 v1 v2 (wim (wim v0 (wim v1 v2)) v1))

private theorem d24 (v0 v1 v2 v3 : A) :
    T (wim (wim (wim (wim (wim v0 v1) v2) (wim v3 v2)) v0) v0) :=
  h.mp (d22 h (wim (wim (wim (wim v0 v1) v2) (wim v3 v2)) v0) v0) (d19 h v0 v1 v2 v3 (wim (wim (wim (wim v0 v1) v2) (wim v3 v2)) v0))

private theorem d25 (v0 v1 v2 v3 : A) :
    T (wim (wim v0 (wim v1 (wim v0 v2))) (wim v3 (wim v1 (wim v0 v2)))) :=
  h.mp (h.rho8 v0 v3 (wim v1 (wim v0 v2)) v0 (L.refl _)) (d23 h v1 v0 v2)

private theorem d26 (v0 v1 v2 v3 v4 : A) :
    T (wim (wim v0 (wim (wim (wim v0 v1) v2) (wim v3 v2))) (wim v4 (wim (wim (wim v0 v1) v2) (wim v3 v2)))) :=
  h.mp (h.rho8 v0 v4 (wim (wim (wim v0 v1) v2) (wim v3 v2)) v0 (L.refl _)) (d24 h v0 v1 v2 v3)

private theorem d27 (v0 v1 v2 : A) :
    T (wim (wim v0 (wim v1 (wim v0 v2))) (wim v1 (wim v0 v2))) :=
  h.mp (d22 h (wim v0 (wim v1 (wim v0 v2))) (wim v1 (wim v0 v2))) (d25 h v0 v1 v2 (wim v0 (wim v1 (wim v0 v2))))

private theorem d28 (v0 v1 v2 v3 v4 v5 : A) :
    T (wim (wim (wim v0 (wim (wim (wim v1 v2) v3) (wim v4 v3))) v1) (wim v5 v1)) :=
  h.mp (h.rho8 (wim v0 (wim (wim (wim v1 v2) v3) (wim v4 v3))) v5 v1 (wim (wim (wim v1 v2) v3) (wim v4 v3)) (le_r v0 (L.refl _))) (d26 h v1 v2 v3 v4 v0)

private theorem d29 (v0 v1 v2 v3 v4 : A) :
    T (wim (wim (wim v0 (wim (wim (wim v1 v2) v3) (wim v4 v3))) v1) v1) :=
  h.mp (d22 h (wim (wim v0 (wim (wim (wim v1 v2) v3) (wim v4 v3))) v1) v1) (d28 h v0 v1 v2 v3 v4 (wim (wim v0 (wim (wim (wim v1 v2) v3) (wim v4 v3))) v1))

private theorem d30 (v0 v1 v2 : A) (hb0 : v2 ≼ v0) :
    T (wim (wim v0 v1) (wim (wim (wim v1 v2) v0) v1)) :=
  h.mp (d27 h (wim (wim v1 v2) v0) (wim v0 v1) v1) (h.rho8 v0 (wim (wim v1 v2) v0) v1 v2 hb0)

private theorem d31 (v0 v1 v2 v3 : A) (hb0 : v3 ≼ v0) :
    T (wim (wim (wim (wim (wim v0 v1) (wim v2 v1)) v3) v0) (wim (wim v0 v1) (wim v2 v1))) :=
  h.mp (d30 h v0 (wim (wim v0 v1) (wim v2 v1)) v3 hb0) (d16 h v0 v1 v2)

private theorem d32 (v0 v1 v2 v3 : A) :
    T (wim (wim v0 (wim v1 v2)) (wim (wim (wim v0 v3) v2) (wim v1 v2))) :=
  h.mp (d31 h v0 (wim v1 v2) (wim (wim v0 v3) v2) v0 (L.refl _)) (d29 h (wim v0 (wim v1 v2)) v0 v3 v2 v1)

private theorem d33 (v0 v1 v2 v3 : A) :
    T (wim (wim (wim v0 v1) (wim v2 v3)) (wim (wim v0 v3) (wim v2 v3))) :=
  h.mp (d32 h v0 (wim v0 v3) (wim v2 v3) v1) (d16 h v0 v3 v2)

private theorem d34 (v0 v1 v2 v3 : A) (hb0 : v3 ≼ wim v1 (wim v1 v2)) :
    T (wim (wim (wim (wim v0 (wim v1 v2)) v3) (wim v1 (wim v1 v2))) (wim v0 (wim v1 v2))) :=
  h.mp (d30 h (wim v1 (wim v1 v2)) (wim v0 (wim v1 v2)) v3 hb0) (d20 h v1 v2 v0)

private theorem d35 (v0 v1 : A) :
    T (wim v0 (wim (wim v0 v1) v1)) :=
  h.mp (d34 h v0 (wim v0 v1) v1 (wim (wim v0 v1) v1) (le_r (wim v0 v1) (L.refl _))) (d33 h v0 (wim (wim v0 v1) v1) (wim v0 v1) v1)

private theorem d36 (v0 v1 v2 : A) :
    T (wim v0 (wim (wim (wim v1 v0) v2) v2)) :=
  h.mp (d13 h v1 v0 (wim (wim (wim v1 v0) v2) v2)) (d35 h (wim v1 v0) v2)

private theorem d37 (v0 v1 v2 : A) :
    T (wim (wim (wim v0 v1) v2) (wim (wim v0 v2) v2)) :=
  h.mp (d32 h v0 (wim v0 v2) v2 v1) (d35 h v0 v2)

private theorem d38 (v0 v1 v2 v3 : A) :
    T (wim (wim (wim v0 v1) v2) (wim (wim (wim v3 v0) v2) v2)) :=
  h.mp (d32 h v0 (wim (wim v3 v0) v2) v2 v1) (d36 h v0 v3 v2)

private theorem d39 (v0 v1 v2 v3 : A) :
    T (wim (wim v0 v1) (wim (wim (wim v2 (wim v0 v3)) v1) v1)) :=
  h.mp (d33 h v0 v3 (wim (wim v2 (wim v0 v3)) v1) v1) (d36 h (wim v0 v3) v2 v1)

private theorem d40 (v0 v1 v2 : A) :
    T (wim (wim v0 (wim (wim (wim v0 v1) v2) v2)) (wim (wim (wim v0 v1) v2) v2)) :=
  h.mp (d37 h v0 v1 (wim (wim (wim v0 v1) v2) v2)) (d35 h (wim v0 v1) v2)

private theorem d41 (v0 v1 v2 : A) :
    T (wim (wim (wim (wim (wim v0 v1) v2) v0) v2) v2) :=
  h.mp (d40 h (wim (wim v0 v1) v2) v0 v2) (d38 h v0 v1 v2 (wim (wim v0 v1) v2))

private theorem d42 (v0 v1 v2 : A) :
    T (wim (wim (wim (wim v0 v1) (wim v0 v2)) v1) v1) :=
  h.mp (d40 h (wim v0 v1) (wim v0 v2) v1) (d39 h v0 v1 (wim v0 v1) v2)

private theorem d43 (v0 v1 v2 v3 : A) :
    T (wim (wim (wim v0 (wim (wim (wim v1 v2) v3) v1)) v3) v3) :=
  h.mp (d38 h (wim (wim (wim v1 v2) v3) v1) v3 v3 v0) (d41 h v1 v2 v3)

private theorem d44 (v0 v1 v2 v3 : A) :
    T (wim (wim (wim v0 (wim (wim v1 v2) (wim v1 v3))) v2) v2) :=
  h.mp (d38 h (wim (wim v1 v2) (wim v1 v3)) v2 v2 v0) (d42 h v1 v2 v3)

private theorem d45 (v0 v1 v2 : A) :
    T (wim (wim v0 v1) (wim (wim (wim v1 v2) v0) v1)) :=
  h.mp (d31 h v0 v1 (wim (wim v1 v2) v0) v0 (L.refl _)) (d43 h (wim v0 v1) v1 v2 v0)

private theorem d46 (v0 v1 v2 : A) :
    T (wim (wim v0 (wim v1 v2)) (wim (wim v1 v0) (wim v1 v2))) :=
  h.mp (d31 h v0 (wim v1 v2) (wim v1 v0) v0 (L.refl _)) (d44 h (wim v0 (wim v1 v2)) v1 v0 v2)

private theorem d47 (v0 v1 v2 : A) :
    T (wim (wim v0 v1) (wim v0 (wim v2 v1))) :=
  h.mp (d46 h v1 v0 (wim v2 v1)) (d17 h v1 v0 v2)

private theorem d48 (v0 v1 v2 v3 : A) :
    T (wim (wim v0 v1) (wim v2 (wim v0 (wim v3 v1)))) :=
  h.mp (d47 h (wim v0 v1) (wim v0 (wim v3 v1)) v2) (d47 h v0 v1 v3)

private theorem d49 (v0 v1 v2 v3 : A) :
    T (wim (wim v0 (wim v1 v2)) (wim v0 (wim v1 (wim v3 v2)))) :=
  h.mp (d46 h (wim v1 v2) v0 (wim v1 (wim v3 v2))) (d48 h v1 v2 v0 v3)

private theorem d50 (v0 v1 v2 v3 : A) :
    T (wim (wim v0 v1) (wim (wim (wim v1 v2) v0) (wim v3 v1))) :=
  h.mp (d49 h (wim v0 v1) (wim (wim v1 v2) v0) v1 v3) (d45 h v0 v1 v2)

private theorem d51 (v0 v1 v2 : A) :
    T (wim (wim (wim v0 v1) v2) (wim (wim v2 v0) v0)) :=
  h.mp (d27 h (wim v2 v0) (wim (wim v0 v1) v2) v0) (d50 h v2 v0 v1 (wim v2 v0))

private theorem d52 (v0 v1 v2 v3 : A) :
    T (wim (wim (wim v0 v1) v2) (wim (wim v2 v0) (wim v3 v0))) :=
  h.mp (d49 h (wim (wim v0 v1) v2) (wim v2 v0) v0 v3) (d51 h v0 v1 v2)

/-- A proved implication lifts under any antecedent, by two detachments. -/
private theorem under_antecedent (z : A) {x y : A}
    (hxy : T (wim x y)) : T (wim (wim z x) (wim z y)) :=
  h.mp (d46 h x z y) (h.mp (d47 h x y z) hxy)

/-- Insert an independent antecedent into the basic application row. -/
private theorem insert_middle (a b c d : A) :
    T (wim a (wim b (wim (wim a c) (wim d c)))) :=
  h.mp (d47 h a (wim (wim a c) (wim d c)) b) (d16 h a c d)

/-- Contract the double application context without a deduction theorem. -/
private theorem application_contract (a b c : A) :
    T (wim (wim (wim (wim a b) b) (wim a c)) (wim a c)) :=
  h.mp (d22 h (wim (wim (wim a b) b) (wim a c)) (wim a c))
    (h.mp (d52 h (wim a c) a (wim (wim a b) b)
      (wim (wim (wim a b) b) (wim a c)))
      (h.mp (under_antecedent h (wim (wim a c) a) (d35 h a b))
        (d18 h a c)))

/-- Transport application into the antecedent of a proved implication. -/
private theorem application_transport (a b c : A) :
    T (wim (wim (wim (wim a b) b) c) (wim a c)) :=
  h.mp (d27 h a (wim (wim (wim a b) b) c) c)
    (h.mp (application_contract h a b
      (wim (wim (wim (wim a b) b) c) (wim a c)))
      (insert_middle h (wim (wim a b) b) a c a))

/-- Remove a repeated antecedent past two intervening arguments. -/
private theorem repeated_antecedent (a b c d : A) :
    T (wim (wim a (wim b (wim c (wim a d))))
      (wim b (wim c (wim a d)))) :=
  h.mp (d22 h (wim a (wim b (wim c (wim a d))))
    (wim b (wim c (wim a d))))
    (h.mp (h.rho8 a (wim a (wim b (wim c (wim a d))))
      (wim b (wim c (wim a d))) a (L.refl a))
      (h.mp (d38 h (wim c (wim a d)) a a b) (d23 h c a d)))

private theorem composition_seed (a b c : A) :
    T (wim (wim a b) (wim (wim b c) (wim a c))) := by
  have happ : T (wim (wim (wim a b) b)
      (wim (wim a b) (wim (wim b c) (wim a c)))) :=
    h.mp (d46 h b (wim a b) (wim (wim b c) (wim a c)))
      (insert_middle h b (wim a b) c a)
  exact h.mp (repeated_antecedent h a (wim a b) (wim b c) c)
    (h.mp (application_transport h a b
      (wim (wim a b) (wim (wim b c) (wim a c)))) happ)

end

section
variable {A : Type v} {L : Language A} {T : A → Prop}

private theorem withSeed (h : Restricted L T) (a : A) :
    WithSeed L (rho8 L a a a a) T where
  toRestricted := h
  truth := h.rho8 a a a a (L.refl a)

/-- Restricted rows and modus ponens alone derive every unrestricted row. -/
theorem rho8_all (h : Restricted L T) (a b c u : A) : T (rho8 L a b c u) :=
  d52 (withSeed h a) c u a b

theorem composition (h : Restricted L T) (a b c : A) :
    T (L.imp (L.imp a b) (L.imp (L.imp b c) (L.imp a c))) :=
  composition_seed (withSeed h a) a b c

/-- A proved implication lifts under any antecedent. -/
theorem lift_right (h : Restricted L T) {a b : A} (hab : T (L.imp a b)) (x : A) :
    T (L.imp (L.imp x a) (L.imp x b)) :=
  under_antecedent (withSeed h a) x hab

end
#print axioms rho8_all
#print axioms composition
#print axioms lift_right
end SetTheory.BusyBeaver.ZFC.DominatedImplication
