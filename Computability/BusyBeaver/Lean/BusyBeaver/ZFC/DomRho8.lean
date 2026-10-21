import BusyBeaver.ZFC.Code254

/-!
Dominated rho8 derives unrestricted rho8, for arbitrary natural codes.

The proof has three layers. A 58-lemma bootstrap from Source 149 gives identity,
weakening, Peirce and the implication-transport lemma. The original CD230 lemma
hierarchy then derives composition and distribution. We retain 59 of its 107
schemas; 8 carry one explicit numerical dominance hypothesis. Keeping these
hypotheses avoids expanding each schema at every substitution instance.
Finally a small deduction theorem and Peirce's law give the unrestricted row.

The bootstrap shares and prunes Source 149's original nodes0..60; the CD230 templates are its
pinned adaptation of the upstream condensed-detachment derivation. Duplicate template conclusions reuse bootstrap lemmas. Every emitted
step is an ordinary Lean proof. The source producer is untrusted. The only code
normalization is the proved identity `wim 0 0 = 0`; numerical injectivity,
formula decoding and ZFC consistency are not assumptions.
-/

namespace SetTheory.BusyBeaver.ZFC.DomRho8

open Code254

/-- Truth, modus ponens and the dominated rho8 instances. -/
structure DomImp (T : Nat → Prop) : Prop where
  truth : T 0
  mp : ∀ {a b : Nat}, T (wim a b) → T a → T b
  rho8 : ∀ a b c u : Nat, u ≤ a → T (Code254.rho8 a b c u)

theorem le_l {u x : Nat} (y : Nat) (h : u ≤ x) : u ≤ wim x y :=
  Nat.le_trans h (by have := le_P_left x y; simp only [wim]; omega)

theorem le_r {u y : Nat} (x : Nat) (h : u ≤ y) : u ≤ wim x y :=
  Nat.le_trans h (by have := le_P_right x y; simp only [wim]; omega)

/-- A substitution: the valuation sending variable `i` to the `i`-th code. -/
def sub (l : List Nat) (i : Nat) : Nat := l.getD i 0

theorem wim00 : wim 0 0 = 0 := by simp [wim, P, Cantor.toNat, Cantor.tri]
attribute [local irreducible] wim

section
variable {T : Nat → Prop} (h : DomImp T)
include h

private theorem b0 (v0 v1 v2 : Nat) : T (wim (wim (wim v0 v1) v1) (wim (wim v1 v0) (wim v2 v0))) :=
  (show T (wim (wim (wim v0 v1) v1) (wim (wim v1 v0) (wim v2 v0))) from by simpa only [Code254.rho8] using h.rho8 v1 v2 v0 v1 (Nat.le_refl _))

private theorem b1 (v0 v1 v2 v3 : Nat) : T (wim (wim (wim v0 v1) (wim v2 v1)) (wim (wim (wim v2 v1) v0) (wim v3 v0))) :=
  (show T (wim (wim (wim v0 v1) (wim v2 v1)) (wim (wim (wim v2 v1) v0) (wim v3 v0))) from by simpa only [Code254.rho8] using h.rho8 (wim v2 v1) v3 v0 v1 (le_r v2 (Nat.le_refl _)))

private theorem b2 (v0 v1 v2 v3 : Nat) : T (wim (wim (wim v0 v1) (wim v1 v2)) (wim (wim (wim v1 v2) v0) (wim v3 v0))) :=
  (show T (wim (wim (wim v0 v1) (wim v1 v2)) (wim (wim (wim v1 v2) v0) (wim v3 v0))) from by simpa only [Code254.rho8] using h.rho8 (wim v1 v2) v3 v0 v1 (le_l v2 (Nat.le_refl _)))

private theorem b3 (v0 v1 v2 : Nat) : T (wim (wim (wim (wim (wim v0 v1) v1) (wim v0 v1)) (wim v1 v1)) (wim v2 (wim v1 v1))) :=
  (h.mp (b1 h (wim v1 v1) (wim v0 v1) (wim (wim v0 v1) v1) v2) (b1 h v1 v1 v0 v0))

private theorem b4 (v0 v1 v2 v3 : Nat) : T (wim (wim (wim v0 (wim v1 v1)) (wim (wim (wim v2 v1) v1) (wim v2 v1))) (wim v3 (wim (wim (wim v2 v1) v1) (wim v2 v1)))) :=
  (h.mp (b1 h (wim (wim (wim v2 v1) v1) (wim v2 v1)) (wim v1 v1) v0 v3) (b3 h v2 v1 v0))

private theorem b5 (v0 v1 v2 : Nat) : T (wim (wim (wim v0 0) v1) (wim (wim v1 v0) (wim v2 v0))) :=
  (show T (wim (wim (wim v0 0) v1) (wim (wim v1 v0) (wim v2 v0))) from by simpa only [Code254.rho8] using h.rho8 v1 v2 v0 0 (Nat.zero_le _))

private theorem b6 (v0 v1 v2 : Nat) : T (wim (wim (wim (wim 0 v0) (wim v1 v0)) (wim v0 0)) (wim v2 (wim v0 0))) :=
  (h.mp (b5 h (wim v0 0) (wim (wim 0 v0) (wim v1 v0)) v2) (b5 h v0 0 v1))

private theorem b7 (v0 v1 v2 v3 : Nat) : T (wim (wim (wim v0 (wim v1 0)) (wim (wim 0 v1) (wim v2 v1))) (wim v3 (wim (wim 0 v1) (wim v2 v1)))) :=
  (h.mp (b1 h (wim (wim 0 v1) (wim v2 v1)) (wim v1 0) v0 v3) (b6 h v1 v2 v0))

private theorem b8 (v0 : Nat) : T (wim v0 0) :=
  (h.mp (show T (wim 0 (wim v0 0)) from by simpa only [wim00] using (b7 h 0 0 0 v0)) (show T 0 from by simpa only [wim00] using (b6 h 0 0 0)))

private theorem b9 (v0 v1 : Nat) : T (wim (wim 0 v0) (wim v1 v0)) :=
  (h.mp (b5 h v0 0 v1) (b8 h (wim v0 0)))

private theorem b10 (v0 v1 : Nat) : T (wim v0 (wim (wim (wim v1 v1) v1) (wim v1 v1))) :=
  (h.mp (b4 h 0 v1 v1 v0) (b9 h (wim v1 v1) (wim (wim v1 v1) v1)))

private theorem b12 (v0 : Nat) : T (wim (wim (wim v0 v0) v0) (wim v0 v0)) :=
  (h.mp (b10 h 0 v0) h.truth)

private theorem b13 (v0 v1 : Nat) : T (wim (wim (wim v0 v0) (wim v0 v0)) (wim v1 (wim v0 v0))) :=
  (h.mp (b1 h (wim v0 v0) v0 v0 v1) (b12 h v0))

private theorem b14 (v0 v1 : Nat) : T (wim v0 (wim (wim v1 v1) (wim v1 v1))) :=
  (h.mp (b13 h (wim v1 v1) v0) (b13 h v1 (wim v1 v1)))

private theorem b15 (v0 : Nat) : T (wim (wim v0 v0) (wim v0 v0)) :=
  (h.mp (b14 h 0 v0) h.truth)

private theorem b16 (v0 v1 : Nat) : T (wim v0 (wim v1 v1)) :=
  (h.mp (b13 h v1 v0) (b15 h v1))

private theorem b17 (v0 : Nat) : T (wim v0 v0) :=
  (h.mp (b16 h 0 v0) h.truth)

private theorem b18 (v0 v1 v2 : Nat) : T (wim (wim (wim v0 v1) v0) (wim v2 v0)) :=
  (h.mp (b1 h v0 v1 v0 v2) (b17 h (wim v0 v1)))

private theorem b19 (v0 v1 v2 v3 : Nat) : T (wim (wim (wim v0 v1) (wim v1 v2)) (wim v3 (wim v1 v2))) :=
  (h.mp (b1 h (wim v1 v2) v1 v0 v3) (b18 h v1 v2 v0))

private theorem b20 (v0 v1 v2 v3 v4 : Nat) : T (wim (wim (wim v0 (wim v1 v2)) (wim v3 v1)) (wim v4 (wim v3 v1))) :=
  (h.mp (b1 h (wim v3 v1) (wim v1 v2) v0 v4) (b19 h v3 v1 v2 v0))

private theorem b21 (v0 v1 v2 v3 : Nat) : T (wim v0 (wim (wim (wim (wim v1 v2) v3) v2) (wim v1 v2))) :=
  (h.mp (b20 h (wim v2 0) (wim v1 v2) v3 (wim (wim (wim v1 v2) v3) v2) v0) (b5 h v2 (wim (wim v1 v2) v3) v1))

private theorem b22 (v0 v1 v2 : Nat) : T (wim (wim (wim (wim v0 v1) v2) v1) (wim v0 v1)) :=
  (h.mp (b21 h 0 v0 v1 v2) h.truth)

private theorem b23 (v0 v1 v2 v3 : Nat) : T (wim (wim (wim v0 v1) (wim (wim v0 v1) v2)) (wim v3 (wim (wim v0 v1) v2))) :=
  (h.mp (b1 h (wim (wim v0 v1) v2) v1 v0 v3) (b22 h v0 v1 v2))

private theorem b24 (v0 v1 v2 : Nat) : T (wim v0 (wim (wim (wim v1 v2) v1) v1)) :=
  (h.mp (b23 h (wim v1 v2) v1 v1 v0) (b18 h v1 v2 (wim (wim v1 v2) v1)))

private theorem b25 (v0 v1 : Nat) : T (wim (wim (wim v0 v1) v0) v0) :=
  (h.mp (b24 h 0 v0 v1) h.truth)

private theorem b26 (v0 v1 v2 : Nat) : T (wim (wim v0 (wim v0 v1)) (wim v2 (wim v0 v1))) :=
  (h.mp (b0 h (wim v0 v1) v0 v2) (b25 h v0 v1))

private theorem b27 (v0 v1 v2 : Nat) : T (wim v0 (wim (wim v1 (wim v1 v2)) (wim v1 v2))) :=
  (h.mp (b26 h (wim v1 (wim v1 v2)) (wim v1 v2) v0) (b26 h v1 v2 (wim v1 (wim v1 v2))))

private theorem b28 (v0 v1 : Nat) : T (wim (wim v0 (wim v0 v1)) (wim v0 v1)) :=
  (h.mp (b27 h 0 v0 v1) h.truth)

private theorem b29 (v0 v1 v2 v3 : Nat) : T (wim (wim (wim v0 (wim v1 v2)) v1) (wim v3 v1)) :=
  (h.mp (b1 h v1 (wim v1 v2) v0 v3) (b26 h v1 v2 v0))

private theorem b30 (v0 v1 v2 : Nat) : T (wim (wim (wim v0 (wim v1 v2)) v1) v1) :=
  (h.mp (b28 h (wim (wim v0 (wim v1 v2)) v1) v1) (b29 h v0 v1 v2 (wim (wim v0 (wim v1 v2)) v1)))

private theorem b31 (v0 v1 v2 v3 v4 v5 : Nat) : T (wim (wim (wim v0 v1) (wim (wim (wim v2 v1) v3) v4)) (wim (wim (wim (wim (wim v2 v1) v3) v4) v0) (wim v5 v0))) :=
  (show T (wim (wim (wim v0 v1) (wim (wim (wim v2 v1) v3) v4)) (wim (wim (wim (wim (wim v2 v1) v3) v4) v0) (wim v5 v0))) from by simpa only [Code254.rho8] using h.rho8 (wim (wim (wim v2 v1) v3) v4) v5 v0 v1 (le_l v4 (le_l v3 (le_r v2 (Nat.le_refl _)))))

private theorem b33 (v0 v1 v2 v3 : Nat) : T (wim (wim v0 (wim v1 (wim v0 v2))) (wim v3 (wim v1 (wim v0 v2)))) :=
  (h.mp (b0 h (wim v1 (wim v0 v2)) v0 v3) (b30 h v1 v0 v2))

private theorem b35 (v0 v1 v2 : Nat) : T (wim (wim v0 (wim v1 (wim v0 v2))) (wim v1 (wim v0 v2))) :=
  (h.mp (b28 h (wim v0 (wim v1 (wim v0 v2))) (wim v1 (wim v0 v2))) (b33 h v0 v1 v2 (wim v0 (wim v1 (wim v0 v2)))))

private theorem b36 (v0 v1 v2 v3 v4 v5 : Nat) : T (wim (wim (wim v0 (wim v1 v2)) (wim v3 (wim v2 v4))) (wim v5 (wim v3 (wim v2 v4)))) :=
  (h.mp (b1 h (wim v3 (wim v2 v4)) (wim v1 v2) v0 v5) (b20 h v3 v2 v4 v1 v0))

private theorem b37 (v0 v1 : Nat) : T (wim (wim v0 v1) (wim (wim (wim v1 v0) v0) v1)) :=
  (h.mp (b35 h (wim (wim v1 v0) v0) (wim v0 v1) v1) (b0 h v1 v0 (wim (wim v1 v0) v0)))

private theorem b38 (v0 v1 v2 v3 : Nat) : T (wim v0 (wim (wim (wim v1 v2) v3) (wim v2 v3))) :=
  (h.mp (b36 h (wim v3 v1) v1 v2 (wim (wim v1 v2) v3) v3 v0) (b2 h v3 v1 v2 v2))

private theorem b39 (v0 v1 v2 : Nat) : T (wim (wim (wim v0 v1) v2) (wim v1 v2)) :=
  (h.mp (b38 h 0 v0 v1 v2) (show T 0 from by simpa only [wim00] using (b38 h 0 0 0 0)))

private theorem b40 (v0 v1 v2 : Nat) : T (wim v0 (wim (wim v0 v1) (wim v2 v1))) :=
  (h.mp (b39 h (wim v1 v0) v0 (wim (wim v0 v1) (wim v2 v1))) (b0 h v1 v0 v2))

private theorem b41 (v0 v1 v2 v3 : Nat) : T (wim v0 (wim (wim (wim v1 v0) v2) (wim v3 v2))) :=
  (h.mp (b39 h v1 v0 (wim (wim (wim v1 v0) v2) (wim v3 v2))) (b40 h (wim v1 v0) v2 v3))

private theorem b42 (v0 v1 v2 v3 v4 : Nat) : T (wim (wim (wim (wim (wim v0 v1) v2) (wim v3 v2)) v0) (wim v4 v0)) :=
  (h.mp (b31 h v0 v1 v0 v2 (wim v3 v2) v4) (b40 h (wim v0 v1) v2 v3))

private theorem b43 (v0 v1 v2 v3 v4 : Nat) : T (wim (wim (wim (wim (wim v0 v1) v0) (wim v2 v0)) v3) (wim v4 v3)) :=
  (h.mp (b40 h (wim (wim (wim v0 v1) v0) (wim v2 v0)) v3 v4) (b18 h v0 v1 v2))

private theorem b44 (v0 v1 v2 v3 : Nat) : T (wim (wim (wim (wim (wim v0 v1) v2) (wim v3 v2)) v0) v0) :=
  (h.mp (b28 h (wim (wim (wim (wim v0 v1) v2) (wim v3 v2)) v0) v0) (b42 h v0 v1 v2 v3 (wim (wim (wim (wim v0 v1) v2) (wim v3 v2)) v0)))

private theorem b45 (v0 v1 v2 v3 v4 : Nat) : T (wim (wim v0 (wim (wim (wim v0 v1) v2) (wim v3 v2))) (wim v4 (wim (wim (wim v0 v1) v2) (wim v3 v2)))) :=
  (h.mp (b0 h (wim (wim (wim v0 v1) v2) (wim v3 v2)) v0 v4) (b44 h v0 v1 v2 v3))

private theorem b46 (v0 v1 v2 : Nat) : T (wim (wim (wim (wim (wim v0 v1) (wim v2 v1)) v0) v0) (wim (wim v0 v1) (wim v2 v1))) :=
  (h.mp (b37 h v0 (wim (wim v0 v1) (wim v2 v1))) (b40 h v0 v1 v2))

private theorem b47 (v0 v1 v2 v3 v4 v5 : Nat) : T (wim (wim (wim v0 (wim (wim (wim v1 v0) v2) (wim v3 v2))) v4) (wim v5 v4)) :=
  (h.mp (b40 h (wim v0 (wim (wim (wim v1 v0) v2) (wim v3 v2))) v4 v5) (b41 h v0 v1 v2 v3))

private theorem b48 (v0 v1 v2 v3 : Nat) : T (wim (wim (wim (wim (wim v0 v1) v0) (wim v2 v0)) v3) v3) :=
  (h.mp (b28 h (wim (wim (wim (wim v0 v1) v0) (wim v2 v0)) v3) v3) (b43 h v0 v1 v2 v3 (wim (wim (wim (wim v0 v1) v0) (wim v2 v0)) v3)))

private theorem b49 (v0 v1 v2 v3 v4 : Nat) : T (wim (wim (wim v0 (wim (wim (wim v1 v0) v2) (wim v3 v2))) v4) v4) :=
  (h.mp (b28 h (wim (wim v0 (wim (wim (wim v1 v0) v2) (wim v3 v2))) v4) v4) (b47 h v0 v1 v2 v3 v4 (wim (wim v0 (wim (wim (wim v1 v0) v2) (wim v3 v2))) v4)))

private theorem b50 (v0 v1 v2 v3 v4 v5 : Nat) : T (wim (wim (wim v0 (wim (wim (wim v1 v2) v3) (wim v4 v3))) v1) (wim v5 v1)) :=
  (h.mp (b1 h v1 (wim (wim (wim v1 v2) v3) (wim v4 v3)) v0 v5) (b45 h v1 v2 v3 v4 v0))

private theorem b51 (v0 v1 v2 v3 v4 : Nat) : T (wim (wim (wim v0 (wim (wim (wim v1 v2) v3) (wim v4 v3))) v1) v1) :=
  (h.mp (b28 h (wim (wim v0 (wim (wim (wim v1 v2) v3) (wim v4 v3))) v1) v1) (b50 h v0 v1 v2 v3 v4 (wim (wim v0 (wim (wim (wim v1 v2) v3) (wim v4 v3))) v1)))

private theorem b52 (v0 v1 v2 v3 : Nat) : T (wim (wim v0 (wim v1 v2)) (wim (wim (wim v0 v3) v2) (wim v1 v2))) :=
  (h.mp (b46 h v0 (wim v1 v2) (wim (wim v0 v3) v2)) (b51 h (wim v0 (wim v1 v2)) v0 v3 v2 v1))

private theorem b53 (v0 v1 v2 v3 v4 : Nat) : T (wim (wim (wim v0 v1) (wim v2 v3)) (wim (wim (wim v4 v0) v3) (wim v2 v3))) :=
  (h.mp (b49 h v0 v4 v3 v2 (wim (wim (wim v0 v1) (wim v2 v3)) (wim (wim (wim v4 v0) v3) (wim v2 v3)))) (b52 h v0 (wim (wim v4 v0) v3) (wim v2 v3) v1))

private theorem b54 (v0 v1 v2 v3 : Nat) : T (wim (wim (wim (wim (wim v0 v1) v0) v2) v0) (wim v3 v0)) :=
  (h.mp (b48 h v0 v1 v3 (wim (wim (wim (wim (wim v0 v1) v0) v2) v0) (wim v3 v0))) (b52 h (wim (wim v0 v1) v0) v3 v0 v2))

private theorem b55 (v0 v1 v2 v3 v4 : Nat) : T (wim (wim (wim v0 (wim (wim (wim v1 v2) v1) v3)) v1) (wim v4 v1)) :=
  (h.mp (b53 h (wim (wim (wim v1 v2) v1) v3) v1 v4 v1 v0) (b54 h v1 v2 v3 v4))

private theorem b56 (v0 v1 v2 v3 : Nat) : T (wim (wim (wim v0 (wim (wim (wim v1 v2) v1) v3)) v1) v1) :=
  (h.mp (b28 h (wim (wim v0 (wim (wim (wim v1 v2) v1) v3)) v1) v1) (b55 h v0 v1 v2 v3 (wim (wim v0 (wim (wim (wim v1 v2) v1) v3)) v1)))

private theorem b57 (v0 v1 v2 : Nat) : T (wim (wim v0 v1) (wim (wim (wim v0 v2) v0) v1)) :=
  (h.mp (b46 h v0 v1 (wim (wim v0 v2) v0)) (b56 h (wim v0 v1) v0 v2 v1))

private theorem b58 (v0 v1 v2 : Nat) : T (wim (wim (wim (wim (wim v0 v1) v1) (wim v0 v1)) (wim v1 (wim v0 v1))) (wim v2 (wim v1 (wim v0 v1)))) :=
  (h.mp (b1 h (wim v1 (wim v0 v1)) (wim v0 v1) (wim (wim v0 v1) v1) v2) (b0 h v1 (wim v0 v1) v0))

private theorem b59 (v0 v1 v2 : Nat) : T (wim v0 (wim v1 (wim v2 v1))) :=
  (h.mp (b58 h v2 v1 v0) (b18 h (wim v2 v1) v1 v1))

private theorem b60 (v0 v1 : Nat) : T (wim v0 (wim v1 v0)) :=
  (h.mp (b59 h 0 v0 v1) h.truth)

end

section
variable {T : Nat → Prop} (h : DomImp T)
include h
private theorem basisI (a : Nat) : T (wim a a) := b17 h a
private theorem basisK (a b : Nat) : T (wim a (wim b a)) := b60 h a b
private theorem basisP (a b : Nat) : T (wim (wim (wim a b) a) a) := b25 h a b
private theorem basisJ (a b c : Nat) : T (wim (wim a b) (wim (wim (wim a c) a) b)) := b57 h a b c

private theorem cd0 (v0 v1 v2 v3 : Nat) (hb0 : v1 ≤ v2) :
    T (wim (wim (wim v0 v1) v2) (wim (wim v2 v0) (wim v3 v0))) := by
  simpa only [wim00] using (show T (wim (wim (wim v0 v1) v2) (wim (wim v2 v0) (wim v3 v0))) from by simpa only [Code254.rho8] using h.rho8 v2 v3 v0 v1 hb0)

private theorem cd29 (v0 v1 v2 : Nat)  :
    T (wim (wim (wim v0 v1) (wim v1 v2)) (wim v1 v2)) := by
  simpa only [wim00] using (h.mp (b28 h (wim (wim v0 v1) (wim v1 v2)) (wim v1 v2)) (b19 h v0 v1 v2 (wim (wim v0 v1) (wim v1 v2))))

private theorem cd30 (v0 v1 v2 v3 : Nat)  :
    T (wim (wim (wim v0 v1) (wim v2 v0)) (wim v3 (wim v2 v0))) := by
  simpa only [wim00] using (h.mp (cd0 h (wim v2 v0) (wim v0 v1) (wim v0 v1) v3 (Nat.le_refl _)) (cd29 h v2 v0 v1))

private theorem cd31 (v0 v1 v2 : Nat)  :
    T (wim v0 (wim v1 (wim v2 v0))) := by
  simpa only [wim00] using (h.mp (b22 h v0 (wim v1 (wim v2 v0)) (wim v2 v0)) (cd30 h v0 (wim v1 (wim v2 v0)) v2 v1))

private theorem cd32 (v0 v1 v2 v3 v4 : Nat)  :
    T (wim (wim (wim v0 (wim v1 (wim v2 v3))) v2) (wim v4 v2)) := by
  simpa only [wim00] using (h.mp (cd0 h v2 v3 (wim v0 (wim v1 (wim v2 v3))) v4 (le_r v0 (le_r v1 (le_r v2 (Nat.le_refl _))))) (cd31 h (wim v2 v3) v0 v1))

private theorem cd33 (v0 v1 v2 v3 : Nat)  :
    T (wim (wim (wim v0 (wim v1 (wim v2 v3))) v2) v2) := by
  simpa only [wim00] using (h.mp (b28 h (wim (wim v0 (wim v1 (wim v2 v3))) v2) v2) (cd32 h v0 v1 v2 v3 (wim (wim v0 (wim v1 (wim v2 v3))) v2)))

private theorem cd34 (v0 v1 v2 v3 v4 : Nat)  :
    T (wim (wim v0 (wim v1 (wim v2 (wim v0 v3)))) (wim v4 (wim v1 (wim v2 (wim v0 v3))))) := by
  simpa only [wim00] using (h.mp (cd0 h (wim v1 (wim v2 (wim v0 v3))) v0 v0 v4 (Nat.le_refl _)) (cd33 h v1 v2 v0 v3))

private theorem cd35 (v0 v1 v2 v3 : Nat)  :
    T (wim (wim v0 (wim v1 (wim v2 (wim v0 v3)))) (wim v1 (wim v2 (wim v0 v3)))) := by
  simpa only [wim00] using (h.mp (b28 h (wim v0 (wim v1 (wim v2 (wim v0 v3)))) (wim v1 (wim v2 (wim v0 v3)))) (cd34 h v0 v1 v2 v3 (wim v0 (wim v1 (wim v2 (wim v0 v3))))))

private theorem cd46 (v0 v1 v2 v3 : Nat) (hb0 : v3 ≤ v1) :
    T (wim v0 (wim (wim v1 v2) (wim (wim (wim v2 v3) v1) v2))) := by
  simpa only [wim00] using (h.mp (b33 h (wim (wim v2 v3) v1) (wim v1 v2) v2 v0) (cd0 h v2 v3 v1 (wim (wim v2 v3) v1) hb0))

private theorem cd47 (v0 v1 v2 : Nat) (hb0 : v2 ≤ v0) :
    T (wim (wim v0 v1) (wim (wim (wim v1 v2) v0) v1)) := by
  simpa only [wim00] using (h.mp (cd46 h 0 v0 v1 v2 hb0) (show T 0 from by simpa only [wim00] using (cd0 h 0 0 0 0 (Nat.zero_le _))))

private theorem cd52 (v0 v1 v2 v3 : Nat) (hb0 : v3 ≤ v0) :
    T (wim (wim (wim (wim (wim v0 v1) (wim v2 v1)) v3) v0) (wim (wim v0 v1) (wim v2 v1))) := by
  simpa only [wim00] using (h.mp (cd47 h v0 (wim (wim v0 v1) (wim v2 v1)) v3 hb0) (b40 h v0 v1 v2))

private theorem cd54 (v0 v1 v2 v3 v4 : Nat) (hb0 : v2 ≤ (wim (wim v3 (wim v1 v4)) v1)) :
    T (wim (wim (wim (wim v0 v1) v2) (wim (wim v3 (wim v1 v4)) v1)) (wim v0 v1)) := by
  simpa only [wim00] using (h.mp (cd47 h (wim (wim v3 (wim v1 v4)) v1) (wim v0 v1) v2 hb0) (b29 h v3 v1 v4 v0))

private theorem cd60 (v0 v1 v2 v3 : Nat) (hb0 : v3 ≤ (wim v1 (wim v1 v2))) :
    T (wim (wim (wim (wim v0 (wim v1 v2)) v3) (wim v1 (wim v1 v2))) (wim v0 (wim v1 v2))) := by
  simpa only [wim00] using (h.mp (cd47 h (wim v1 (wim v1 v2)) (wim v0 (wim v1 v2)) v3 hb0) (b26 h v1 v2 v0))

private theorem cd61 (v0 v1 v2 v3 : Nat)  :
    T (wim (wim (wim v0 v1) v0) (wim (wim v0 v2) (wim v3 v2))) := by
  simpa only [wim00] using (h.mp (b57 h v0 (wim (wim v0 v2) (wim v3 v2)) v1) (b40 h v0 v2 v3))

private theorem cd62 (v0 v1 : Nat)  :
    T (wim v0 (wim (wim v0 v1) v1)) := by
  simpa only [wim00] using (h.mp (cd60 h v0 (wim v0 v1) v1 v0 (le_l (wim (wim v0 v1) v1) (le_l v1 (Nat.le_refl _)))) (cd61 h v0 (wim (wim v0 v1) v1) v1 (wim v0 v1)))

private theorem cd63 (v0 v1 v2 : Nat)  :
    T (wim (wim (wim v0 v1) v0) (wim (wim v0 v2) v2)) := by
  simpa only [wim00] using (h.mp (b57 h v0 (wim (wim v0 v2) v2) v1) (cd62 h v0 v2))

private theorem cd64 (v0 v1 v2 v3 : Nat)  :
    T (wim (wim (wim (wim v0 v1) v1) (wim v0 v2)) (wim v3 (wim v0 v2))) := by
  simpa only [wim00] using (h.mp (cd0 h (wim v0 v2) v0 (wim (wim v0 v1) v1) v3 (le_l v1 (le_l v1 (Nat.le_refl _)))) (cd63 h v0 v2 v1))

private theorem cd65 (v0 v1 v2 : Nat)  :
    T (wim (wim (wim (wim v0 v1) v1) (wim v0 v2)) (wim v0 v2)) := by
  simpa only [wim00] using (h.mp (b28 h (wim (wim (wim v0 v1) v1) (wim v0 v2)) (wim v0 v2)) (cd64 h v0 v1 v2 (wim (wim (wim v0 v1) v1) (wim v0 v2))))

private theorem cd66 (v0 v1 v2 v3 : Nat) (hb0 : v3 ≤ v2) :
    T (wim (wim (wim (wim v0 (wim v1 v2)) v3) v2) (wim v0 (wim v1 v2))) := by
  simpa only [wim00] using (h.mp (cd47 h v2 (wim v0 (wim v1 v2)) v3 hb0) (cd31 h v2 v0 v1))

private theorem cd67 (v0 v1 v2 v3 : Nat)  :
    T (wim v0 (wim v1 (wim (wim v0 v2) (wim v3 v2)))) := by
  simpa only [wim00] using (h.mp (cd66 h v0 v1 (wim (wim v0 v2) (wim v3 v2)) v0 (le_l (wim v3 v2) (le_l v2 (Nat.le_refl _)))) (cd61 h v0 (wim v1 (wim (wim v0 v2) (wim v3 v2))) v2 v3))

private theorem cd68 (v0 v1 v2 v3 : Nat)  :
    T (wim v0 (wim (wim (wim (wim v0 v1) v1) v2) (wim v3 v2))) := by
  simpa only [wim00] using (h.mp (cd65 h v0 v1 (wim (wim (wim (wim v0 v1) v1) v2) (wim v3 v2))) (cd67 h (wim (wim v0 v1) v1) v0 v2 v3))

private theorem cd69 (v0 v1 v2 : Nat)  :
    T (wim (wim (wim (wim v0 v1) v1) v2) (wim v0 v2)) := by
  simpa only [wim00] using (h.mp (b35 h v0 (wim (wim (wim v0 v1) v1) v2) v2) (cd68 h v0 v1 v2 v0))

private theorem cd70 (v0 v1 v2 v3 v4 : Nat)  :
    T (wim (wim (wim v0 v1) (wim v2 (wim v1 v3))) (wim v4 (wim v2 (wim v1 v3)))) := by
  simpa only [wim00] using (h.mp (cd0 h (wim v2 (wim v1 v3)) v1 (wim v0 v1) v4 (le_r v0 (Nat.le_refl _))) (b29 h v2 v1 v3 v0))

private theorem cd71 (v0 v1 v2 v3 : Nat)  :
    T (wim (wim (wim v0 v1) (wim v2 (wim v1 v3))) (wim v2 (wim v1 v3))) := by
  simpa only [wim00] using (h.mp (b28 h (wim (wim v0 v1) (wim v2 (wim v1 v3))) (wim v2 (wim v1 v3))) (cd70 h v0 v1 v2 v3 (wim (wim v0 v1) (wim v2 (wim v1 v3)))))

private theorem cd72 (v0 v1 v2 v3 v4 : Nat)  :
    T (wim v0 (wim v1 (wim (wim (wim v2 v0) v3) (wim v4 v3)))) := by
  simpa only [wim00] using (h.mp (b39 h v2 v0 (wim v1 (wim (wim (wim v2 v0) v3) (wim v4 v3)))) (cd67 h (wim v2 v0) v1 v3 v4))

private theorem cd73 (v0 v1 v2 v3 v4 : Nat)  :
    T (wim v0 (wim (wim (wim v1 (wim (wim v0 v2) v2)) v3) (wim v4 v3))) := by
  simpa only [wim00] using (h.mp (cd65 h v0 v2 (wim (wim (wim v1 (wim (wim v0 v2) v2)) v3) (wim v4 v3))) (cd72 h (wim (wim v0 v2) v2) v0 v1 v3 v4))

private theorem cd74 (v0 v1 v2 v3 v4 : Nat)  :
    T (wim (wim (wim v0 (wim (wim (wim v1 v2) v3) v3)) v4) (wim v2 v4)) := by
  simpa only [wim00] using (h.mp (cd71 h v1 v2 (wim (wim v0 (wim (wim (wim v1 v2) v3) v3)) v4) v4) (cd73 h (wim v1 v2) v0 v3 v4 v2))

private theorem cd75 (v0 v1 v2 v3 : Nat)  :
    T (wim (wim (wim v0 v1) v2) (wim (wim (wim v3 v0) v2) v2)) := by
  simpa only [wim00] using (h.mp (cd52 h (wim v0 v1) v2 (wim (wim v3 v0) v2) v1 (le_r v0 (Nat.le_refl _))) (cd74 h (wim (wim v0 v1) v2) v3 v0 v2 v1))

private theorem cd76 (v0 v1 v2 : Nat) (hb0 : v2 ≤ v0) :
    T (wim (wim (wim (wim (wim v0 v1) v1) v2) v0) (wim (wim v0 v1) v1)) := by
  simpa only [wim00] using (h.mp (cd47 h v0 (wim (wim v0 v1) v1) v2 hb0) (cd62 h v0 v1))

private theorem cd77 (v0 v1 v2 : Nat)  :
    T (wim (wim (wim v0 v1) (wim v2 v0)) (wim v2 v0)) := by
  simpa only [wim00] using (h.mp (b28 h (wim (wim v0 v1) (wim v2 v0)) (wim v2 v0)) (cd30 h v0 v1 v2 (wim (wim v0 v1) (wim v2 v0))))

private theorem cd78 (v0 v1 v2 : Nat)  :
    T (wim v0 (wim v1 (wim (wim v0 v2) v2))) := by
  simpa only [wim00] using (h.mp (cd66 h v0 v1 (wim (wim v0 v2) v2) v0 (le_l v2 (le_l v2 (Nat.le_refl _)))) (cd63 h v0 (wim v1 (wim (wim v0 v2) v2)) v2))

private theorem cd79 (v0 v1 v2 v3 : Nat)  :
    T (wim v0 (wim v1 (wim (wim (wim v2 v0) v3) v3))) := by
  simpa only [wim00] using (h.mp (b39 h v2 v0 (wim v1 (wim (wim (wim v2 v0) v3) v3))) (cd78 h (wim v2 v0) v1 v3))

private theorem cd80 (v0 v1 v2 v3 : Nat)  :
    T (wim v0 (wim (wim (wim v1 (wim (wim v0 v2) v2)) v3) v3)) := by
  simpa only [wim00] using (h.mp (cd65 h v0 v2 (wim (wim (wim v1 (wim (wim v0 v2) v2)) v3) v3)) (cd79 h (wim (wim v0 v2) v2) v0 v1 v3))

private theorem cd81 (v0 v1 v2 v3 : Nat)  :
    T (wim (wim (wim v0 (wim (wim (wim v1 v2) v3) v3)) v1) v1) := by
  simpa only [wim00] using (h.mp (cd77 h v1 v2 (wim (wim v0 (wim (wim (wim v1 v2) v3) v3)) v1)) (cd80 h (wim v1 v2) v0 v3 v1))

private theorem cd82 (v0 v1 v2 : Nat)  :
    T (wim (wim v0 (wim (wim (wim v0 v1) v2) v2)) (wim (wim (wim v0 v1) v2) v2)) := by
  simpa only [wim00] using (h.mp (cd76 h v0 (wim (wim (wim v0 v1) v2) v2) v0 (Nat.le_refl _)) (cd81 h (wim v0 (wim (wim (wim v0 v1) v2) v2)) v0 v1 v2))

private theorem cd83 (v0 v1 v2 v3 : Nat)  :
    T (wim (wim (wim v0 (wim v1 v2)) (wim v3 v1)) (wim v3 v1)) := by
  simpa only [wim00] using (h.mp (b28 h (wim (wim v0 (wim v1 v2)) (wim v3 v1)) (wim v3 v1)) (b20 h v0 v1 v2 v3 (wim (wim v0 (wim v1 v2)) (wim v3 v1))))

private theorem cd84 (v0 v1 v2 v3 v4 : Nat)  :
    T (wim (wim (wim v0 (wim (wim (wim v1 (wim v2 v3)) v4) v4)) v2) v2) := by
  simpa only [wim00] using (h.mp (cd83 h v1 v2 v3 (wim (wim v0 (wim (wim (wim v1 (wim v2 v3)) v4) v4)) v2)) (cd80 h (wim v1 (wim v2 v3)) v0 v4 v2))

private theorem cd85 (v0 v1 v2 v3 : Nat)  :
    T (wim (wim v0 v1) (wim (wim (wim v2 (wim v0 v3)) v1) v1)) := by
  simpa only [wim00] using (h.mp (cd52 h v0 v1 (wim (wim v2 (wim v0 v3)) v1) v0 (Nat.le_refl _)) (cd84 h (wim v0 v1) v2 v0 v3 v1))

private theorem cd86 (v0 v1 v2 : Nat)  :
    T (wim (wim (wim (wim v0 v1) (wim v0 v2)) v1) v1) := by
  simpa only [wim00] using (h.mp (cd82 h (wim v0 v1) (wim v0 v2) v1) (cd85 h v0 v1 (wim v0 v1) v2))

private theorem cd87 (v0 v1 v2 v3 : Nat)  :
    T (wim (wim (wim v0 (wim (wim v1 v2) (wim v1 v3))) v2) v2) := by
  simpa only [wim00] using (h.mp (cd75 h (wim (wim v1 v2) (wim v1 v3)) v2 v2 v0) (cd86 h v1 v2 v3))

private theorem cd88 (v0 v1 v2 : Nat)  :
    T (wim (wim v0 (wim v1 v2)) (wim (wim v1 v0) (wim v1 v2))) := by
  simpa only [wim00] using (h.mp (cd52 h v0 (wim v1 v2) (wim v1 v0) v0 (Nat.le_refl _)) (cd87 h (wim v0 (wim v1 v2)) v1 v0 v2))

private theorem cd89 (v0 v1 v2 v3 : Nat)  :
    T (wim (wim v0 v1) (wim v0 (wim (wim v1 v2) (wim v3 v2)))) := by
  simpa only [wim00] using (h.mp (cd88 h v1 v0 (wim (wim v1 v2) (wim v3 v2))) (cd67 h v1 v0 v2 v3))

private theorem cd90 (v0 v1 v2 v3 : Nat)  :
    T (wim v0 (wim (wim v0 v1) (wim (wim v1 v2) (wim v3 v2)))) := by
  simpa only [wim00] using (h.mp (cd69 h v0 v1 (wim (wim v0 v1) (wim (wim v1 v2) (wim v3 v2)))) (cd89 h (wim v0 v1) v1 v2 v3))

private theorem cd91 (v0 v1 v2 : Nat)  :
    T (wim (wim v0 v1) (wim (wim v1 v2) (wim v0 v2))) := by
  simpa only [wim00] using (h.mp (cd35 h v0 (wim v0 v1) (wim v1 v2) v2) (cd90 h v0 v1 v2 v0))

private theorem cd92 (v0 v1 v2 : Nat)  :
    T (wim v0 (wim (wim (wim v1 v0) v2) v2)) := by
  simpa only [wim00] using (h.mp (b39 h v1 v0 (wim (wim (wim v1 v0) v2) v2)) (cd62 h (wim v1 v0) v2))

private theorem cd93 (v0 v1 v2 v3 v4 : Nat)  :
    T (wim (wim (wim (wim (wim v0 (wim v1 v2)) v3) v3) v1) (wim v4 v1)) := by
  simpa only [wim00] using (h.mp (cd0 h v1 v2 (wim (wim (wim v0 (wim v1 v2)) v3) v3) v4 (le_l v3 (le_l v3 (le_r v0 (le_r v1 (Nat.le_refl _)))))) (cd92 h (wim v1 v2) v0 v3))

private theorem cd94 (v0 v1 v2 v3 : Nat)  :
    T (wim (wim (wim (wim (wim v0 (wim v1 v2)) v3) v3) v1) v1) := by
  simpa only [wim00] using (h.mp (b28 h (wim (wim (wim (wim v0 (wim v1 v2)) v3) v3) v1) v1) (cd93 h v0 v1 v2 v3 (wim (wim (wim (wim v0 (wim v1 v2)) v3) v3) v1)))

private theorem cd95 (v0 v1 v2 v3 v4 : Nat)  :
    T (wim (wim (wim v0 (wim (wim (wim v1 (wim v2 v3)) v2) v4)) v2) v2) := by
  simpa only [wim00] using (h.mp (cd54 h (wim (wim v0 (wim (wim (wim v1 (wim v2 v3)) v2) v4)) v2) v2 (wim (wim v1 (wim v2 v3)) v2) v1 v3 (Nat.le_refl _)) (cd94 h v0 (wim (wim v1 (wim v2 v3)) v2) v4 v2))

private theorem cd96 (v0 v1 v2 v3 : Nat)  :
    T (wim (wim v0 v1) (wim (wim (wim v2 (wim v0 v3)) v0) v1)) := by
  simpa only [wim00] using (h.mp (cd52 h v0 v1 (wim (wim v2 (wim v0 v3)) v0) v0 (Nat.le_refl _)) (cd95 h (wim v0 v1) v2 v0 v3 v1))

private theorem cd97 (v0 v1 v2 v3 v4 : Nat)  :
    T (wim (wim (wim v0 (wim v1 v2)) v1) (wim (wim v1 v3) (wim v4 v3))) := by
  simpa only [wim00] using (h.mp (cd96 h v1 (wim (wim v1 v3) (wim v4 v3)) v0 v2) (b40 h v1 v3 v4))

private theorem cd98 (v0 v1 v2 v3 : Nat)  :
    T (wim (wim (wim (wim v0 v1) (wim v2 v1)) v3) (wim v0 v3)) := by
  simpa only [wim00] using (h.mp (cd52 h (wim (wim v0 v1) (wim v2 v1)) v3 v0 v0 (le_l (wim v2 v1) (le_l v1 (Nat.le_refl _)))) (cd97 h (wim (wim (wim v0 v1) (wim v2 v1)) v3) v0 v3 v1 v2))

private theorem cd99 (v0 v1 v2 : Nat)  :
    T (wim (wim v0 v1) (wim v0 (wim v2 v1))) := by
  simpa only [wim00] using (h.mp (cd98 h (wim v0 v1) v1 v2 (wim v0 (wim v2 v1))) (cd69 h v0 v1 (wim v2 v1)))

private theorem cd100 (v0 v1 v2 v3 : Nat)  :
    T (wim (wim v0 v1) (wim v2 (wim v0 (wim v3 v1)))) := by
  simpa only [wim00] using (h.mp (cd99 h (wim v0 v1) (wim v0 (wim v3 v1)) v2) (cd99 h v0 v1 v3))

private theorem cd101 (v0 v1 v2 v3 : Nat)  :
    T (wim (wim v0 (wim v1 v2)) (wim v0 (wim v1 (wim v3 v2)))) := by
  simpa only [wim00] using (h.mp (cd88 h (wim v1 v2) v0 (wim v1 (wim v3 v2))) (cd100 h v1 v2 v0 v3))

private theorem cd102 (v0 v1 v2 v3 : Nat)  :
    T (wim v0 (wim (wim v0 (wim v1 v2)) (wim v1 (wim v3 v2)))) := by
  simpa only [wim00] using (h.mp (cd69 h v0 (wim v1 v2) (wim (wim v0 (wim v1 v2)) (wim v1 (wim v3 v2)))) (cd101 h (wim v0 (wim v1 v2)) v1 v2 v3))

private theorem cd103 (v0 v1 v2 : Nat)  :
    T (wim (wim v0 (wim v1 v2)) (wim v1 (wim v0 v2))) := by
  simpa only [wim00] using (h.mp (cd35 h v0 (wim v0 (wim v1 v2)) v1 v2) (cd102 h v0 v1 v2 v0))

private theorem cd104 (v0 v1 v2 v3 : Nat)  :
    T (wim (wim (wim (wim v0 v1) (wim v2 v1)) v3) (wim (wim v2 v0) v3)) := by
  simpa only [wim00] using (h.mp (cd91 h (wim v2 v0) (wim (wim v0 v1) (wim v2 v1)) v3) (cd91 h v2 v0 v1))

private theorem cd105 (v0 v1 v2 : Nat)  :
    T (wim (wim v0 v1) (wim (wim v0 (wim v1 v2)) (wim v0 v2))) := by
  simpa only [wim00] using (h.mp (cd104 h v1 v2 v0 (wim (wim v0 (wim v1 v2)) (wim v0 v2))) (cd88 h (wim v1 v2) v0 v2))

private theorem cd106 (v0 v1 v2 : Nat)  :
    T (wim (wim v0 (wim v1 v2)) (wim (wim v0 v1) (wim v0 v2))) := by
  simpa only [wim00] using (h.mp (cd103 h (wim v0 v1) (wim v0 (wim v1 v2)) (wim v0 v2)) (cd105 h v0 v1 v2))

theorem composition (a b c : Nat) : T (wim (wim a b) (wim (wim b c) (wim a c))) := cd91 h a b c
theorem distribution (a b c : Nat) : T (wim (wim a (wim b c)) (wim (wim a b) (wim a c))) := cd106 h a b c
/-! Deduction is used only after deriving K and S from the dominated rows. -/
private inductive Proof (T : Nat → Prop) : List Nat → Nat → Prop
  | ax {G a} : T a → Proof T G a
  | hyp {G a} : a ∈ G → Proof T G a
  | mp {G a b} : Proof T G (wim a b) → Proof T G a → Proof T G b

private theorem proof_sound {G : List Nat} {a : Nat} (d : Proof T G a)
    (hG : ∀ x, x ∈ G → T x) : T a := by
  induction d with
  | ax ht => exact ht
  | hyp hm => exact hG _ hm
  | mp _ _ ih1 ih2 => exact h.mp ih1 ih2

private theorem discharge_aux {a : Nat} {G' : List Nat} {b : Nat}
    (d : Proof T G' b) : ∀ G : List Nat, G' = a :: G → Proof T G (wim a b) := by
  induction d with
  | ax hb => intro G _; exact .mp (.ax (basisK h _ a)) (.ax hb)
  | hyp hm =>
      intro G hG
      subst hG
      cases List.mem_cons.mp hm with
      | inl he => subst he; exact .ax (basisI h _)
      | inr hin => exact .mp (.ax (basisK h _ a)) (.hyp hin)
  | mp _ _ ih1 ih2 =>
      intro G hG
      exact .mp (.mp (.ax (distribution h _ _ _)) (ih1 G hG)) (ih2 G hG)

private theorem discharge {G : List Nat} {a b : Nat}
    (d : Proof T (a :: G) b) : Proof T G (wim a b) :=
  discharge_aux h d G rfl

/-- Every unrestricted instance follows by deduction and Peirce's law. -/
theorem rho8_all (a b c u : Nat) : T (Code254.rho8 a b c u) := by
  let f := wim (wim c u) a
  let g := wim a c
  have hc : Proof T [wim c u, b, g, f] c :=
    .mp (.hyp (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
      (.mp (.hyp (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))
        (.hyp (List.mem_cons_self ..)))
  have closedC : Proof T [b, g, f] c :=
    .mp (.ax (basisP h c u)) (discharge h hc)
  have result : Proof T [] (Code254.rho8 a b c u) :=
    discharge h (discharge h (discharge h closedC))
  exact proof_sound h result (by intro x hx; cases hx)

end
#print axioms rho8_all
#print axioms composition
#print axioms distribution
end SetTheory.BusyBeaver.ZFC.DomRho8
