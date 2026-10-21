import Init

/-!
A representation-independent dominated implication theorem.

The proof is an attributed compression of DomRho8 at ProveIt commit
aa66d0a33f1f8237a348899eb8095b045a502832 (Source 149 / CD230 ancestry).
Thirteen condensed-detachment shortcuts remove 33 of 117 numbered helpers.
No formula decoder, injectivity, bottom element, or zero-collapse identity is
assumed. The relation need only be reflexive and closed under insertion into
either implication operand; transitivity is not a separate requirement.
The private seed hypothesis is eliminated in each public theorem using a
dominated axiom instance at its first argument.
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

private theorem b1 (v0 v1 v2 v3 : A) : T (wim (wim (wim v0 v1) (wim v2 v1)) (wim (wim (wim v2 v1) v0) (wim v3 v0))) :=
  (show T (wim (wim (wim v0 v1) (wim v2 v1)) (wim (wim (wim v2 v1) v0) (wim v3 v0))) from by simpa only [rho8] using h.rho8 (wim v2 v1) v3 v0 v1 (le_r v2 (L.refl _)))

private theorem b3 (v0 v1 v2 : A) : T (wim (wim (wim (wim (wim v0 v1) v1) (wim v0 v1)) (wim v1 v1)) (wim v2 (wim v1 v1))) :=
  (h.mp (b1 h (wim v1 v1) (wim v0 v1) (wim (wim v0 v1) v1) v2) (b1 h v1 v1 v0 v0))

private theorem b4 (v0 v1 v2 v3 : A) : T (wim (wim (wim v0 (wim v1 v1)) (wim (wim (wim v2 v1) v1) (wim v2 v1))) (wim v3 (wim (wim (wim v2 v1) v1) (wim v2 v1)))) :=
  (h.mp (b1 h (wim (wim (wim v2 v1) v1) (wim v2 v1)) (wim v1 v1) v0 v3) (b3 h v2 v1 v0))

private theorem b10 (v0 v1 : A) : T (wim v0 (wim (wim (wim v1 v1) v1) (wim v1 v1))) :=
  (h.mp (b4 h (wim v1 v1) v1 v1 v0) (b1 h v1 v1 v1 v1))

private theorem b12 (v0 : A) : T (wim (wim (wim v0 v0) v0) (wim v0 v0)) :=
  (h.mp (b10 h τ v0) h.truth)

private theorem b13 (v0 v1 : A) : T (wim (wim (wim v0 v0) (wim v0 v0)) (wim v1 (wim v0 v0))) :=
  (h.mp (b1 h (wim v0 v0) v0 v0 v1) (b12 h v0))

private theorem b14 (v0 v1 : A) : T (wim v0 (wim (wim v1 v1) (wim v1 v1))) :=
  (h.mp (b13 h (wim v1 v1) v0) (b13 h v1 (wim v1 v1)))

private theorem b15 (v0 : A) : T (wim (wim v0 v0) (wim v0 v0)) :=
  (h.mp (b14 h τ v0) h.truth)

private theorem b16 (v0 v1 : A) : T (wim v0 (wim v1 v1)) :=
  (h.mp (b13 h v1 v0) (b15 h v1))

private theorem b17 (v0 : A) : T (wim v0 v0) :=
  (h.mp (b16 h τ v0) h.truth)

private theorem b18 (v0 v1 v2 : A) : T (wim (wim (wim v0 v1) v0) (wim v2 v0)) :=
  (h.mp (b1 h v0 v1 v0 v2) (b17 h (wim v0 v1)))

private theorem b31 (v0 v1 v2 v3 v4 v5 : A) : T (wim (wim (wim v0 v1) (wim (wim (wim v2 v1) v3) v4)) (wim (wim (wim (wim (wim v2 v1) v3) v4) v0) (wim v5 v0))) :=
  (show T (wim (wim (wim v0 v1) (wim (wim (wim v2 v1) v3) v4)) (wim (wim (wim (wim (wim v2 v1) v3) v4) v0) (wim v5 v0))) from by simpa only [rho8] using h.rho8 (wim (wim (wim v2 v1) v3) v4) v5 v0 v1 (le_l v4 (le_l v3 (le_r v2 (L.refl _)))))

private theorem b19 (v0 v1 v2 v3 : A) : T (wim (wim (wim v0 v1) (wim v1 v2)) (wim v3 (wim v1 v2))) :=
  (h.mp (b1 h (wim v1 v2) v1 v0 v3) (b18 h v1 v2 v0))

private theorem b20 (v0 v1 v2 v3 v4 : A) : T (wim (wim (wim v0 (wim v1 v2)) (wim v3 v1)) (wim v4 (wim v3 v1))) :=
  (h.mp (b1 h (wim v3 v1) (wim v1 v2) v0 v4) (b19 h v3 v1 v2 v0))

private theorem b36 (v0 v1 v2 v3 v4 v5 : A) : T (wim (wim (wim v0 (wim v1 v2)) (wim v3 (wim v2 v4))) (wim v5 (wim v3 (wim v2 v4)))) :=
  (h.mp (b1 h (wim v3 (wim v2 v4)) (wim v1 v2) v0 v5) (b20 h v3 v2 v4 v1 v0))

private theorem b38 (v0 v1 v2 v3 : A) : T (wim v0 (wim (wim (wim v1 v2) v3) (wim v2 v3))) :=
  (h.mp (b36 h (wim v3 v2) v1 v2 (wim (wim v1 v2) v3) v3 v0) (b1 h v3 v2 v1 v2))

private theorem b39 (v0 v1 v2 : A) : T (wim (wim (wim v0 v1) v2) (wim v1 v2)) :=
  (h.mp (b38 h τ v0 v1 v2) h.truth)

private theorem b0 (v0 v1 v2 : A) : T (wim (wim (wim v0 v1) v1) (wim (wim v1 v0) (wim v2 v0))) :=
  (show T (wim (wim (wim v0 v1) v1) (wim (wim v1 v0) (wim v2 v0))) from by simpa only [rho8] using h.rho8 v1 v2 v0 v1 (L.refl _))

private theorem b40 (v0 v1 v2 : A) : T (wim v0 (wim (wim v0 v1) (wim v2 v1))) :=
  (h.mp (b39 h (wim v1 v0) v0 (wim (wim v0 v1) (wim v2 v1))) (b0 h v1 v0 v2))

private theorem b42 (v0 v1 v2 v3 v4 : A) : T (wim (wim (wim (wim (wim v0 v1) v2) (wim v3 v2)) v0) (wim v4 v0)) :=
  (h.mp (b31 h v0 v1 v0 v2 (wim v3 v2) v4) (b40 h (wim v0 v1) v2 v3))

private theorem b21 (v0 v1 v2 v3 : A) : T (wim v0 (wim (wim (wim (wim v1 v2) v3) v2) (wim v1 v2))) :=
  (h.mp (b18 h (wim (wim (wim (wim v1 v2) v3) v2) (wim v1 v2)) (wim v1 v2) v0) (b42 h (wim v1 v2) v3 v2 v1 (wim (wim (wim v1 v2) v3) v2)))

private theorem b22 (v0 v1 v2 : A) : T (wim (wim (wim (wim v0 v1) v2) v1) (wim v0 v1)) :=
  (h.mp (b21 h τ v0 v1 v2) h.truth)

private theorem b23 (v0 v1 v2 v3 : A) : T (wim (wim (wim v0 v1) (wim (wim v0 v1) v2)) (wim v3 (wim (wim v0 v1) v2))) :=
  (h.mp (b1 h (wim (wim v0 v1) v2) v1 v0 v3) (b22 h v0 v1 v2))

private theorem b24 (v0 v1 v2 : A) : T (wim v0 (wim (wim (wim v1 v2) v1) v1)) :=
  (h.mp (b23 h (wim v1 v2) v1 v1 v0) (b18 h v1 v2 (wim (wim v1 v2) v1)))

private theorem b25 (v0 v1 : A) : T (wim (wim (wim v0 v1) v0) v0) :=
  (h.mp (b24 h τ v0 v1) h.truth)

private theorem b60 (v0 v1 : A) : T (wim v0 (wim v1 v0)) :=
  (h.mp (b22 h v0 (wim v1 v0) v0) (b18 h v0 (wim v1 v0) v1))

private theorem b26 (v0 v1 v2 : A) : T (wim (wim v0 (wim v0 v1)) (wim v2 (wim v0 v1))) :=
  (h.mp (b0 h (wim v0 v1) v0 v2) (b25 h v0 v1))

private theorem b27 (v0 v1 v2 : A) : T (wim v0 (wim (wim v1 (wim v1 v2)) (wim v1 v2))) :=
  (h.mp (b26 h (wim v1 (wim v1 v2)) (wim v1 v2) v0) (b26 h v1 v2 (wim v1 (wim v1 v2))))

private theorem b28 (v0 v1 : A) : T (wim (wim v0 (wim v0 v1)) (wim v0 v1)) :=
  (h.mp (b27 h τ v0 v1) h.truth)

private theorem cd0 (v0 v1 v2 v3 : A) (hb0 : v1 ≼ v2) :
    T (wim (wim (wim v0 v1) v2) (wim (wim v2 v0) (wim v3 v0))) :=
  (show T (wim (wim (wim v0 v1) v2) (wim (wim v2 v0) (wim v3 v0))) from by simpa only [rho8] using h.rho8 v2 v3 v0 v1 hb0)

private theorem b29 (v0 v1 v2 v3 : A) : T (wim (wim (wim v0 (wim v1 v2)) v1) (wim v3 v1)) :=
  (h.mp (b1 h v1 (wim v1 v2) v0 v3) (b26 h v1 v2 v0))

private theorem b30 (v0 v1 v2 : A) : T (wim (wim (wim v0 (wim v1 v2)) v1) v1) :=
  (h.mp (b28 h (wim (wim v0 (wim v1 v2)) v1) v1) (b29 h v0 v1 v2 (wim (wim v0 (wim v1 v2)) v1)))

private theorem b33 (v0 v1 v2 v3 : A) : T (wim (wim v0 (wim v1 (wim v0 v2))) (wim v3 (wim v1 (wim v0 v2)))) :=
  (h.mp (b0 h (wim v1 (wim v0 v2)) v0 v3) (b30 h v1 v0 v2))

private theorem b35 (v0 v1 v2 : A) : T (wim (wim v0 (wim v1 (wim v0 v2))) (wim v1 (wim v0 v2))) :=
  (h.mp (b28 h (wim v0 (wim v1 (wim v0 v2))) (wim v1 (wim v0 v2))) (b33 h v0 v1 v2 (wim v0 (wim v1 (wim v0 v2)))))

private theorem b37 (v0 v1 : A) : T (wim (wim v0 v1) (wim (wim (wim v1 v0) v0) v1)) :=
  (h.mp (b35 h (wim (wim v1 v0) v0) (wim v0 v1) v1) (b0 h v1 v0 (wim (wim v1 v0) v0)))

private theorem b46 (v0 v1 v2 : A) : T (wim (wim (wim (wim (wim v0 v1) (wim v2 v1)) v0) v0) (wim (wim v0 v1) (wim v2 v1))) :=
  (h.mp (b37 h v0 (wim (wim v0 v1) (wim v2 v1))) (b40 h v0 v1 v2))

private theorem b44 (v0 v1 v2 v3 : A) : T (wim (wim (wim (wim (wim v0 v1) v2) (wim v3 v2)) v0) v0) :=
  (h.mp (b28 h (wim (wim (wim (wim v0 v1) v2) (wim v3 v2)) v0) v0) (b42 h v0 v1 v2 v3 (wim (wim (wim (wim v0 v1) v2) (wim v3 v2)) v0)))

private theorem b45 (v0 v1 v2 v3 v4 : A) : T (wim (wim v0 (wim (wim (wim v0 v1) v2) (wim v3 v2))) (wim v4 (wim (wim (wim v0 v1) v2) (wim v3 v2)))) :=
  (h.mp (b0 h (wim (wim (wim v0 v1) v2) (wim v3 v2)) v0 v4) (b44 h v0 v1 v2 v3))

private theorem b50 (v0 v1 v2 v3 v4 v5 : A) : T (wim (wim (wim v0 (wim (wim (wim v1 v2) v3) (wim v4 v3))) v1) (wim v5 v1)) :=
  (h.mp (b1 h v1 (wim (wim (wim v1 v2) v3) (wim v4 v3)) v0 v5) (b45 h v1 v2 v3 v4 v0))

private theorem b51 (v0 v1 v2 v3 v4 : A) : T (wim (wim (wim v0 (wim (wim (wim v1 v2) v3) (wim v4 v3))) v1) v1) :=
  (h.mp (b28 h (wim (wim v0 (wim (wim (wim v1 v2) v3) (wim v4 v3))) v1) v1) (b50 h v0 v1 v2 v3 v4 (wim (wim v0 (wim (wim (wim v1 v2) v3) (wim v4 v3))) v1)))

private theorem b52 (v0 v1 v2 v3 : A) : T (wim (wim v0 (wim v1 v2)) (wim (wim (wim v0 v3) v2) (wim v1 v2))) :=
  (h.mp (b46 h v0 (wim v1 v2) (wim (wim v0 v3) v2)) (b51 h (wim v0 (wim v1 v2)) v0 v3 v2 v1))

private theorem cd46 (v0 v1 v2 v3 : A) (hb0 : v3 ≼ v1) :
    T (wim v0 (wim (wim v1 v2) (wim (wim (wim v2 v3) v1) v2))) :=
  (h.mp (b33 h (wim (wim v2 v3) v1) (wim v1 v2) v2 v0) (cd0 h v2 v3 v1 (wim (wim v2 v3) v1) hb0))

private theorem cd47 (v0 v1 v2 : A) (hb0 : v2 ≼ v0) :
    T (wim (wim v0 v1) (wim (wim (wim v1 v2) v0) v1)) :=
  (h.mp (cd46 h τ v0 v1 v2 hb0) h.truth)

private theorem cd60 (v0 v1 v2 v3 : A) (hb0 : v3 ≼ (wim v1 (wim v1 v2))) :
    T (wim (wim (wim (wim v0 (wim v1 v2)) v3) (wim v1 (wim v1 v2))) (wim v0 (wim v1 v2))) :=
  (h.mp (cd47 h (wim v1 (wim v1 v2)) (wim v0 (wim v1 v2)) v3 hb0) (b26 h v1 v2 v0))

private theorem b41 (v0 v1 v2 v3 : A) : T (wim v0 (wim (wim (wim v1 v0) v2) (wim v3 v2))) :=
  (h.mp (b39 h v1 v0 (wim (wim (wim v1 v0) v2) (wim v3 v2))) (b40 h (wim v1 v0) v2 v3))

private theorem b53 (v0 v1 v2 v3 v4 : A) : T (wim (wim (wim v0 v1) (wim v2 v3)) (wim (wim (wim v4 v0) v3) (wim v2 v3))) :=
  (h.mp (b52 h v0 (wim (wim v4 v0) v3) (wim v2 v3) v1) (b41 h v0 v4 v3 v2))

private theorem b54 (v0 v1 v2 v3 : A) : T (wim (wim (wim (wim (wim v0 v1) v0) v2) v0) (wim v3 v0)) :=
  (h.mp (b52 h (wim (wim v0 v1) v0) v3 v0 v2) (b18 h v0 v1 v3))

private theorem b55 (v0 v1 v2 v3 v4 : A) : T (wim (wim (wim v0 (wim (wim (wim v1 v2) v1) v3)) v1) (wim v4 v1)) :=
  (h.mp (b53 h (wim (wim (wim v1 v2) v1) v3) v1 v4 v1 v0) (b54 h v1 v2 v3 v4))

private theorem b56 (v0 v1 v2 v3 : A) : T (wim (wim (wim v0 (wim (wim (wim v1 v2) v1) v3)) v1) v1) :=
  (h.mp (b28 h (wim (wim v0 (wim (wim (wim v1 v2) v1) v3)) v1) v1) (b55 h v0 v1 v2 v3 (wim (wim v0 (wim (wim (wim v1 v2) v1) v3)) v1)))

private theorem b57 (v0 v1 v2 : A) : T (wim (wim v0 v1) (wim (wim (wim v0 v2) v0) v1)) :=
  (h.mp (b46 h v0 v1 (wim (wim v0 v2) v0)) (b56 h (wim v0 v1) v0 v2 v1))

private theorem cd61 (v0 v1 v2 v3 : A)  :
    T (wim (wim (wim v0 v1) v0) (wim (wim v0 v2) (wim v3 v2))) :=
  (h.mp (b57 h v0 (wim (wim v0 v2) (wim v3 v2)) v1) (b40 h v0 v2 v3))

private theorem cd62 (v0 v1 : A)  :
    T (wim v0 (wim (wim v0 v1) v1)) :=
  (h.mp (cd60 h v0 (wim v0 v1) v1 v0 (le_l (wim (wim v0 v1) v1) (le_l v1 (L.refl _)))) (cd61 h v0 (wim (wim v0 v1) v1) v1 (wim v0 v1)))

private theorem cd92 (v0 v1 v2 : A)  :
    T (wim v0 (wim (wim (wim v1 v0) v2) v2)) :=
  (h.mp (b39 h v1 v0 (wim (wim (wim v1 v0) v2) v2)) (cd62 h (wim v1 v0) v2))

private theorem cd75 (v0 v1 v2 v3 : A)  :
    T (wim (wim (wim v0 v1) v2) (wim (wim (wim v3 v0) v2) v2)) :=
  (h.mp (b52 h v0 (wim (wim v3 v0) v2) v2 v1) (cd92 h v0 v3 v2))

private theorem cd33 (v0 v1 v2 v3 : A)  :
    T (wim (wim (wim v0 (wim v1 (wim v2 v3))) v2) v2) :=
  (h.mp (cd75 h (wim v1 (wim v2 v3)) v2 v2 v0) (b30 h v1 v2 v3))

private theorem cd34 (v0 v1 v2 v3 v4 : A)  :
    T (wim (wim v0 (wim v1 (wim v2 (wim v0 v3)))) (wim v4 (wim v1 (wim v2 (wim v0 v3))))) :=
  (h.mp (cd0 h (wim v1 (wim v2 (wim v0 v3))) v0 v0 v4 (L.refl _)) (cd33 h v1 v2 v0 v3))

private theorem cd35 (v0 v1 v2 v3 : A)  :
    T (wim (wim v0 (wim v1 (wim v2 (wim v0 v3)))) (wim v1 (wim v2 (wim v0 v3)))) :=
  (h.mp (b28 h (wim v0 (wim v1 (wim v2 (wim v0 v3)))) (wim v1 (wim v2 (wim v0 v3)))) (cd34 h v0 v1 v2 v3 (wim v0 (wim v1 (wim v2 (wim v0 v3))))))

private theorem cd63 (v0 v1 v2 : A)  :
    T (wim (wim (wim v0 v1) v0) (wim (wim v0 v2) v2)) :=
  (h.mp (b57 h v0 (wim (wim v0 v2) v2) v1) (cd62 h v0 v2))

private theorem cd64 (v0 v1 v2 v3 : A)  :
    T (wim (wim (wim (wim v0 v1) v1) (wim v0 v2)) (wim v3 (wim v0 v2))) :=
  (h.mp (cd0 h (wim v0 v2) v0 (wim (wim v0 v1) v1) v3 (le_l v1 (le_l v1 (L.refl _)))) (cd63 h v0 v2 v1))

private theorem cd65 (v0 v1 v2 : A)  :
    T (wim (wim (wim (wim v0 v1) v1) (wim v0 v2)) (wim v0 v2)) :=
  (h.mp (b28 h (wim (wim (wim v0 v1) v1) (wim v0 v2)) (wim v0 v2)) (cd64 h v0 v1 v2 (wim (wim (wim v0 v1) v1) (wim v0 v2))))

private theorem cd30 (v0 v1 v2 v3 : A)  :
    T (wim (wim (wim v0 v1) (wim v2 v0)) (wim v3 (wim v2 v0))) :=
  (h.mp (b1 h (wim v2 v0) v1 v0 v3) (b39 h v2 v0 v1))

private theorem cd31 (v0 v1 v2 : A)  :
    T (wim v0 (wim v1 (wim v2 v0))) :=
  (h.mp (b22 h v0 (wim v1 (wim v2 v0)) (wim v2 v0)) (cd30 h v0 (wim v1 (wim v2 v0)) v2 v1))

private theorem cd66 (v0 v1 v2 v3 : A) (hb0 : v3 ≼ v2) :
    T (wim (wim (wim (wim v0 (wim v1 v2)) v3) v2) (wim v0 (wim v1 v2))) :=
  (h.mp (cd47 h v2 (wim v0 (wim v1 v2)) v3 hb0) (cd31 h v2 v0 v1))

private theorem cd67 (v0 v1 v2 v3 : A)  :
    T (wim v0 (wim v1 (wim (wim v0 v2) (wim v3 v2)))) :=
  (h.mp (cd66 h v0 v1 (wim (wim v0 v2) (wim v3 v2)) v0 (le_l (wim v3 v2) (le_l v2 (L.refl _)))) (cd61 h v0 (wim v1 (wim (wim v0 v2) (wim v3 v2))) v2 v3))

private theorem cd68 (v0 v1 v2 v3 : A)  :
    T (wim v0 (wim (wim (wim (wim v0 v1) v1) v2) (wim v3 v2))) :=
  (h.mp (cd65 h v0 v1 (wim (wim (wim (wim v0 v1) v1) v2) (wim v3 v2))) (cd67 h (wim (wim v0 v1) v1) v0 v2 v3))

private theorem cd69 (v0 v1 v2 : A)  :
    T (wim (wim (wim (wim v0 v1) v1) v2) (wim v0 v2)) :=
  (h.mp (b35 h v0 (wim (wim (wim v0 v1) v1) v2) v2) (cd68 h v0 v1 v2 v0))

private theorem cd76 (v0 v1 v2 : A) (hb0 : v2 ≼ v0) :
    T (wim (wim (wim (wim (wim v0 v1) v1) v2) v0) (wim (wim v0 v1) v1)) :=
  (h.mp (cd47 h v0 (wim (wim v0 v1) v1) v2 hb0) (cd62 h v0 v1))

private theorem cd77 (v0 v1 v2 : A)  :
    T (wim (wim (wim v0 v1) (wim v2 v0)) (wim v2 v0)) :=
  (h.mp (b28 h (wim (wim v0 v1) (wim v2 v0)) (wim v2 v0)) (cd30 h v0 v1 v2 (wim (wim v0 v1) (wim v2 v0))))

private theorem cd80 (v0 v1 v2 v3 : A)  :
    T (wim v0 (wim (wim (wim v1 (wim (wim v0 v2) v2)) v3) v3)) :=
  (h.mp (cd69 h v0 v2 (wim (wim (wim v1 (wim (wim v0 v2) v2)) v3) v3)) (cd92 h (wim (wim v0 v2) v2) v1 v3))

private theorem cd81 (v0 v1 v2 v3 : A)  :
    T (wim (wim (wim v0 (wim (wim (wim v1 v2) v3) v3)) v1) v1) :=
  (h.mp (cd77 h v1 v2 (wim (wim v0 (wim (wim (wim v1 v2) v3) v3)) v1)) (cd80 h (wim v1 v2) v0 v3 v1))

private theorem cd82 (v0 v1 v2 : A)  :
    T (wim (wim v0 (wim (wim (wim v0 v1) v2) v2)) (wim (wim (wim v0 v1) v2) v2)) :=
  (h.mp (cd76 h v0 (wim (wim (wim v0 v1) v2) v2) v0 (L.refl _)) (cd81 h (wim v0 (wim (wim (wim v0 v1) v2) v2)) v0 v1 v2))

private theorem cd83 (v0 v1 v2 v3 : A)  :
    T (wim (wim (wim v0 (wim v1 v2)) (wim v3 v1)) (wim v3 v1)) :=
  (h.mp (b28 h (wim (wim v0 (wim v1 v2)) (wim v3 v1)) (wim v3 v1)) (b20 h v0 v1 v2 v3 (wim (wim v0 (wim v1 v2)) (wim v3 v1))))

private theorem cd84 (v0 v1 v2 v3 v4 : A)  :
    T (wim (wim (wim v0 (wim (wim (wim v1 (wim v2 v3)) v4) v4)) v2) v2) :=
  (h.mp (cd83 h v1 v2 v3 (wim (wim v0 (wim (wim (wim v1 (wim v2 v3)) v4) v4)) v2)) (cd80 h (wim v1 (wim v2 v3)) v0 v4 v2))

private theorem cd85 (v0 v1 v2 v3 : A)  :
    T (wim (wim v0 v1) (wim (wim (wim v2 (wim v0 v3)) v1) v1)) :=
  (h.mp (b46 h v0 v1 (wim (wim v2 (wim v0 v3)) v1)) (cd84 h (wim v0 v1) v2 v0 v3 v1))

private theorem cd86 (v0 v1 v2 : A)  :
    T (wim (wim (wim (wim v0 v1) (wim v0 v2)) v1) v1) :=
  (h.mp (cd82 h (wim v0 v1) (wim v0 v2) v1) (cd85 h v0 v1 (wim v0 v1) v2))

private theorem cd87 (v0 v1 v2 v3 : A)  :
    T (wim (wim (wim v0 (wim (wim v1 v2) (wim v1 v3))) v2) v2) :=
  (h.mp (cd75 h (wim (wim v1 v2) (wim v1 v3)) v2 v2 v0) (cd86 h v1 v2 v3))

private theorem cd88 (v0 v1 v2 : A)  :
    T (wim (wim v0 (wim v1 v2)) (wim (wim v1 v0) (wim v1 v2))) :=
  (h.mp (b46 h v0 (wim v1 v2) (wim v1 v0)) (cd87 h (wim v0 (wim v1 v2)) v1 v0 v2))

private theorem cd89 (v0 v1 v2 v3 : A)  :
    T (wim (wim v0 v1) (wim v0 (wim (wim v1 v2) (wim v3 v2)))) :=
  (h.mp (cd88 h v1 v0 (wim (wim v1 v2) (wim v3 v2))) (cd67 h v1 v0 v2 v3))

private theorem cd90 (v0 v1 v2 v3 : A)  :
    T (wim v0 (wim (wim v0 v1) (wim (wim v1 v2) (wim v3 v2)))) :=
  (h.mp (cd69 h v0 v1 (wim (wim v0 v1) (wim (wim v1 v2) (wim v3 v2)))) (cd89 h (wim v0 v1) v1 v2 v3))

private theorem cd91 (v0 v1 v2 : A)  :
    T (wim (wim v0 v1) (wim (wim v1 v2) (wim v0 v2))) :=
  (h.mp (cd35 h v0 (wim v0 v1) (wim v1 v2) v2) (cd90 h v0 v1 v2 v0))

private theorem cd104 (v0 v1 v2 v3 : A)  :
    T (wim (wim (wim (wim v0 v1) (wim v2 v1)) v3) (wim (wim v2 v0) v3)) :=
  (h.mp (cd91 h (wim v2 v0) (wim (wim v0 v1) (wim v2 v1)) v3) (cd91 h v2 v0 v1))

private theorem cd103 (v0 v1 v2 : A)  :
    T (wim (wim v0 (wim v1 v2)) (wim v1 (wim v0 v2))) :=
  (h.mp (cd104 h (wim v1 v2) v2 v0 (wim v1 (wim v0 v2))) (cd69 h v1 v2 (wim v0 v2)))

private theorem cd105 (v0 v1 v2 : A)  :
    T (wim (wim v0 v1) (wim (wim v0 (wim v1 v2)) (wim v0 v2))) :=
  (h.mp (cd104 h v1 v2 v0 (wim (wim v0 (wim v1 v2)) (wim v0 v2))) (cd88 h (wim v1 v2) v0 v2))

private theorem cd106 (v0 v1 v2 : A)  :
    T (wim (wim v0 (wim v1 v2)) (wim (wim v0 v1) (wim v0 v2))) :=
  (h.mp (cd103 h (wim v0 v1) (wim v0 (wim v1 v2)) (wim v0 v2)) (cd105 h v0 v1 v2))

private theorem basisK (a b : A) : T (wim a (wim b a)) := b60 h a b
private theorem basisP (a b : A) : T (wim (wim (wim a b) a) a) := b25 h a b

private theorem composition_seed (a b c : A) : T (wim (wim a b) (wim (wim b c) (wim a c))) := cd91 h a b c
private theorem distribution_seed (a b c : A) : T (wim (wim a (wim b c)) (wim (wim a b) (wim a c))) := cd106 h a b c
private theorem compose_derived {a b c : A}
    (hab : T (wim a b)) (hbc : T (wim b c)) : T (wim a c) :=
  h.mp (h.mp (composition_seed h a b c) hab) hbc

private theorem under_antecedent (z : A) {x y : A}
    (hxy : T (wim x y)) : T (wim (wim z x) (wim z y)) :=
  h.mp (h.mp (cd103 h (wim z x) (wim x y) (wim z y))
    (composition_seed h z x y)) hxy

/-- Direct composition and exchange replace the local deduction calculus. -/
private theorem rho8_seed (a b c u : A) : T (rho8 L a b c u) := by
  have h0 := composition_seed h (wim c u) a c
  have h1 := under_antecedent h (wim a c) (basisP h c u)
  have h2 := compose_derived h h0 h1
  have h3 := under_antecedent h (wim a c) (basisK h c b)
  simpa only [rho8] using compose_derived h h2 h3

end

section
variable {A : Type v} {L : Language A} {T : A → Prop}

private theorem withSeed (h : Restricted L T) (a : A) :
    WithSeed L (rho8 L a a a a) T where
  toRestricted := h
  truth := h.rho8 a a a a (L.refl a)

/-- Restricted rows and modus ponens alone derive every unrestricted row. -/
theorem rho8_all (h : Restricted L T) (a b c u : A) : T (rho8 L a b c u) :=
  rho8_seed (withSeed h a) a b c u

theorem composition (h : Restricted L T) (a b c : A) :
    T (L.imp (L.imp a b) (L.imp (L.imp b c) (L.imp a c))) :=
  composition_seed (withSeed h a) a b c

theorem distribution (h : Restricted L T) (a b c : A) :
    T (L.imp (L.imp a (L.imp b c)) (L.imp (L.imp a b) (L.imp a c))) :=
  distribution_seed (withSeed h a) a b c

end
#print axioms rho8_all
#print axioms composition
#print axioms distribution
end SetTheory.BusyBeaver.ZFC.DominatedImplication
