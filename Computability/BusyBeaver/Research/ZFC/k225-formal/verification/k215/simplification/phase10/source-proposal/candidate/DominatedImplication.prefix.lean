import Init

/-!
A representation-independent dominated implication theorem.

The 52-step condensed-detachment derivation is adapted from ProveIt commit
4fdc59197a. Four discarded filler terms are chosen reflexively rather than at
numeric zero, and five detachments use an arbitrary private seed. Thus no
bottom element, injectivity, transitivity, or zero-collapse law is needed.
The short semantic tail retains composition and pointwise lifting; the seed
is discharged by a reflexive dominated instance in every public theorem.
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

