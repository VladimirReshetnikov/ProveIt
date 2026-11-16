import IPRADerivations.Core.Quotient

/-!
# Integers in iPRA as differences, and a ring tool for them

iPRA has only natural numbers. An integer is represented by a pair of terms
`(p, q)`, read as `p - q`, and the integer equation `(p, q) = (p', q')` is the
quantifier-free iPRA formula `p + q' ≐ p' + q` (`ZT.eq`). Sums, products and
negatives of pairs are computed by the usual formulas, so every integer
polynomial identity has an explicit iPRA statement over natural-number
variables.

To derive such statements, `Groth R` is the ring of differences of a cancellative
commutative semiring `R` (its Grothendieck ring), with the injective semiring map
`Groth.ι : R →+* Groth R`. Applied to `R = Q Γ` it gives a commutative ring in
which `ZT.toZ` evaluates integer terms; `ZT.derive` turns an equality there into
a `Prf PRAAx` derivation. Identities are then proved by `ring`, and identities
under hypotheses by `linear_combination`.
-/

namespace LeanProofs.IPRA

open LeanProofs.ConciseIPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)

/-! ## The ring of differences of a cancellative commutative semiring -/

namespace Groth

variable (R : Type*) [CommSemiring R] [IsCancelAdd R]

/-- `(a, b) ~ (c, d)` when `a + d = c + b`. -/
def setoid : Setoid (R × R) where
  r p q := p.1 + q.2 = q.1 + p.2
  iseqv := {
    refl := fun _ => rfl
    symm := fun h => h.symm
    trans := by
      rintro ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩ h₁ h₂
      dsimp only at h₁ h₂ ⊢
      apply _root_.add_right_cancel (b := c + d)
      calc a + f + (c + d) = (a + d) + (c + f) := by ring
        _ = (c + b) + (e + d) := by rw [h₁, h₂]
        _ = e + b + (c + d) := by ring }

end Groth

/-- The ring of formal differences of `R`. -/
def Groth (R : Type*) [CommSemiring R] [IsCancelAdd R] : Type _ := Quotient (Groth.setoid R)

namespace Groth

variable {R : Type*} [CommSemiring R] [IsCancelAdd R]

/-- The class of `a - b`. -/
def mk (a b : R) : Groth R := Quotient.mk (setoid R) (a, b)

theorem mk_eq_mk {a b c d : R} : mk a b = mk c d ↔ a + d = c + b :=
  ⟨Quotient.exact, fun h => Quotient.sound h⟩

@[elab_as_elim] theorem ind {motive : Groth R → Prop} (h : ∀ a b, motive (mk a b))
    (x : Groth R) : motive x :=
  Quotient.ind (fun p => h p.1 p.2) x

instance : Zero (Groth R) := ⟨mk 0 0⟩
instance : One (Groth R) := ⟨mk 1 0⟩

instance : Add (Groth R) :=
  ⟨Quotient.map₂ (fun p q => (p.1 + q.1, p.2 + q.2)) fun ⟨a, b⟩ ⟨a', b'⟩ h ⟨c, d⟩ ⟨c', d'⟩ h' => by
    change a + b' = a' + b at h
    change c + d' = c' + d at h'
    change a + c + (b' + d') = a' + c' + (b + d)
    calc a + c + (b' + d') = (a + b') + (c + d') := by ring
      _ = (a' + b) + (c' + d) := by rw [h, h']
      _ = a' + c' + (b + d) := by ring⟩

instance : Neg (Groth R) :=
  ⟨Quotient.map (fun p => (p.2, p.1)) fun ⟨a, b⟩ ⟨a', b'⟩ h => by
    change a + b' = a' + b at h
    change b + a' = b' + a
    calc b + a' = a' + b := _root_.add_comm _ _
      _ = a + b' := h.symm
      _ = b' + a := _root_.add_comm _ _⟩

omit [IsCancelAdd R] in
private theorem mul_left {a b a' b' : R} (c d : R) (h : a + b' = a' + b) :
    (a * c + b * d) + (a' * d + b' * c) = (a' * c + b' * d) + (a * d + b * c) :=
  calc (a * c + b * d) + (a' * d + b' * c) = (a + b') * c + (a' + b) * d := by ring
    _ = (a' + b) * c + (a + b') * d := by rw [h]
    _ = (a' * c + b' * d) + (a * d + b * c) := by ring

omit [IsCancelAdd R] in
private theorem mul_right (a b : R) {c d c' d' : R} (h : c + d' = c' + d) :
    (a * c + b * d) + (a * d' + b * c') = (a * c' + b * d') + (a * d + b * c) :=
  calc (a * c + b * d) + (a * d' + b * c') = a * (c + d') + b * (c' + d) := by ring
    _ = a * (c' + d) + b * (c + d') := by rw [h]
    _ = (a * c' + b * d') + (a * d + b * c) := by ring

instance : Mul (Groth R) :=
  ⟨Quotient.map₂ (fun p q => (p.1 * q.1 + p.2 * q.2, p.1 * q.2 + p.2 * q.1))
    fun ⟨a, b⟩ ⟨a', b'⟩ h ⟨c, d⟩ ⟨c', d'⟩ h' => by
      change a + b' = a' + b at h
      change c + d' = c' + d at h'
      change (a * c + b * d) + (a' * d' + b' * c') = (a' * c' + b' * d') + (a * d + b * c)
      apply _root_.add_right_cancel (b := a' * d + b' * c)
      have h₁ := mul_left c d h
      have h₂ := mul_right a' b' h'
      calc (a * c + b * d) + (a' * d' + b' * c') + (a' * d + b' * c)
          = ((a * c + b * d) + (a' * d + b' * c)) + (a' * d' + b' * c') := by ring
        _ = ((a' * c + b' * d) + (a * d + b * c)) + (a' * d' + b' * c') := by rw [h₁]
        _ = ((a' * c + b' * d) + (a' * d' + b' * c')) + (a * d + b * c) := by ring
        _ = ((a' * c' + b' * d') + (a' * d + b' * c)) + (a * d + b * c) := by rw [h₂]
        _ = (a' * c' + b' * d') + (a * d + b * c) + (a' * d + b' * c) := by ring⟩

@[simp] theorem mk_add (a b c d : R) : mk a b + mk c d = mk (a + c) (b + d) := rfl
@[simp] theorem mk_mul (a b c d : R) : mk a b * mk c d = mk (a * c + b * d) (a * d + b * c) := rfl
@[simp] theorem neg_mk (a b : R) : -mk a b = mk b a := rfl
theorem zero_def : (0 : Groth R) = mk 0 0 := rfl
theorem one_def : (1 : Groth R) = mk 1 0 := rfl

instance : CommRing (Groth R) where
  add_assoc x y z := by
    induction x using Groth.ind; induction y using Groth.ind; induction z using Groth.ind
    simp only [mk_add]; exact mk_eq_mk.2 (by ring)
  zero_add x := by
    induction x using Groth.ind; rw [zero_def, mk_add]; exact mk_eq_mk.2 (by ring)
  add_zero x := by
    induction x using Groth.ind; rw [zero_def, mk_add]; exact mk_eq_mk.2 (by ring)
  add_comm x y := by
    induction x using Groth.ind; induction y using Groth.ind
    simp only [mk_add]; exact mk_eq_mk.2 (by ring)
  neg_add_cancel x := by
    induction x using Groth.ind; rw [zero_def, neg_mk, mk_add]; exact mk_eq_mk.2 (by ring)
  mul_assoc x y z := by
    induction x using Groth.ind; induction y using Groth.ind; induction z using Groth.ind
    simp only [mk_mul]; exact mk_eq_mk.2 (by ring)
  one_mul x := by
    induction x using Groth.ind; rw [one_def, mk_mul]; exact mk_eq_mk.2 (by ring)
  mul_one x := by
    induction x using Groth.ind; rw [one_def, mk_mul]; exact mk_eq_mk.2 (by ring)
  zero_mul x := by
    induction x using Groth.ind; rw [zero_def, mk_mul]; exact mk_eq_mk.2 (by ring)
  mul_zero x := by
    induction x using Groth.ind; rw [zero_def, mk_mul]; exact mk_eq_mk.2 (by ring)
  left_distrib x y z := by
    induction x using Groth.ind; induction y using Groth.ind; induction z using Groth.ind
    simp only [mk_add, mk_mul]; exact mk_eq_mk.2 (by ring)
  right_distrib x y z := by
    induction x using Groth.ind; induction y using Groth.ind; induction z using Groth.ind
    simp only [mk_add, mk_mul]; exact mk_eq_mk.2 (by ring)
  mul_comm x y := by
    induction x using Groth.ind; induction y using Groth.ind
    simp only [mk_mul]; exact mk_eq_mk.2 (by ring)
  nsmul := nsmulRec
  zsmul := zsmulRec
  npow := npowRec

/-- The embedding of `R` into its ring of differences. -/
def ι : R →+* Groth R where
  toFun a := mk a 0
  map_zero' := rfl
  map_one' := rfl
  map_add' a b := mk_eq_mk.2 (by simp)
  map_mul' a b := mk_eq_mk.2 (by simp)

theorem ι_apply (a : R) : ι a = mk a 0 := rfl

theorem ι_injective : Function.Injective (ι : R → Groth R) := fun a b h => by
  simpa using mk_eq_mk.1 h

theorem mk_eq_sub (a b : R) : mk a b = ι a - ι b := by
  rw [sub_eq_add_neg, ι_apply, ι_apply, neg_mk, mk_add]
  exact mk_eq_mk.2 (by ring)

end Groth

/-! ## Integer terms of iPRA -/

/-- An integer term over `n` natural-number variables: the pair `(pos, neg)`
stands for `pos - neg`. -/
structure ZT (n : ℕ) where
  pos : PTm n
  neg : PTm n

namespace ZT

variable {n : ℕ}

instance : Add (ZT n) := ⟨fun u v => ⟨u.pos + v.pos, u.neg + v.neg⟩⟩
instance : Mul (ZT n) :=
  ⟨fun u v => ⟨u.pos * v.pos + u.neg * v.neg, u.pos * v.neg + u.neg * v.pos⟩⟩
instance : Neg (ZT n) := ⟨fun u => ⟨u.neg, u.pos⟩⟩
instance : Sub (ZT n) := ⟨fun u v => u + -v⟩

/-- A natural-number term read as an integer. -/
def ofNat (t : PTm n) : ZT n := ⟨t, zero⟩

/-- The natural-number constant `k`, read as an integer. -/
def natLit (k : ℕ) : ZT n := ofNat (PTm.num k)

/-- The integer square. -/
def sq (u : ZT n) : ZT n := u * u

/-- The iPRA formula expressing equality of two integer terms. -/
def eq (u v : ZT n) : Fm PTm n := u.pos + v.neg ≐ v.pos + u.neg

/-- Evaluation of an integer term in the ring of differences of `Q Γ`. -/
def toZ (Γ : List (Fm PTm n)) (u : ZT n) : Groth (Q Γ) :=
  Groth.ι (Q.mk Γ u.pos) - Groth.ι (Q.mk Γ u.neg)

variable {Γ : List (Fm PTm n)}

@[simp] theorem toZ_add (u v : ZT n) : toZ Γ (u + v) = toZ Γ u + toZ Γ v := by
  show Groth.ι (Q.mk Γ (u.pos + v.pos)) - Groth.ι (Q.mk Γ (u.neg + v.neg)) = _
  simp only [toZ, Q.mk_add, map_add]; ring

@[simp] theorem toZ_mul (u v : ZT n) : toZ Γ (u * v) = toZ Γ u * toZ Γ v := by
  show Groth.ι (Q.mk Γ (u.pos * v.pos + u.neg * v.neg)) -
      Groth.ι (Q.mk Γ (u.pos * v.neg + u.neg * v.pos)) = _
  simp only [toZ, Q.mk_add, Q.mk_mul, map_add, map_mul]; ring

@[simp] theorem toZ_neg (u : ZT n) : toZ Γ (-u) = -toZ Γ u := by
  show Groth.ι (Q.mk Γ u.neg) - Groth.ι (Q.mk Γ u.pos) = _
  simp only [toZ]; ring

@[simp] theorem toZ_sub (u v : ZT n) : toZ Γ (u - v) = toZ Γ u - toZ Γ v := by
  show toZ Γ (u + -v) = _
  rw [toZ_add, toZ_neg]; ring

@[simp] theorem toZ_sq (u : ZT n) : toZ Γ (sq u) = toZ Γ u ^ 2 := by
  rw [sq, toZ_mul]; ring

@[simp] theorem toZ_ofNat (t : PTm n) : toZ Γ (ofNat t) = Groth.ι (Q.mk Γ t) := by
  simp [toZ, ofNat]

@[simp] theorem toZ_natLit (k : ℕ) : toZ Γ (natLit k : ZT n) = (k : Groth (Q Γ)) := by
  simp [natLit]

/-- An equality of evaluations gives a derivation of the integer equation. -/
theorem derive {u v : ZT n} (h : toZ Γ u = toZ Γ v) : Γ ⊢[PRAAx] eq u v := by
  apply Q.exact
  apply Groth.ι_injective
  simp only [toZ] at h
  simp only [Q.mk_add, map_add]
  linear_combination h

/-- A derived integer equation gives an equality of evaluations. -/
theorem toZ_eq {u v : ZT n} (h : Γ ⊢[PRAAx] eq u v) : toZ Γ u = toZ Γ v := by
  have h' := congrArg Groth.ι (Q.sound h)
  simp only [Q.mk_add, map_add] at h'
  simp only [toZ]
  linear_combination h'

end ZT

end LeanProofs.IPRA
