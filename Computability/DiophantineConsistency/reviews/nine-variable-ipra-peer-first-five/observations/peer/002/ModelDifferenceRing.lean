import Mathlib.Algebra.Order.Ring.Cone
import DiophantineConsistency.AdaptiveEquationSyntax2011
import DiophantineConsistency.WeightedExpressionDegree
/-! # The ring of differences of an ordered natural-like semiring

For a commutative, linearly and strictly ordered, canonically ordered semiring
`V` (every model of `𝗣𝗔⁻` is one), `DiffRing V` is the quotient of `V × V` by
`(a,b) ~ (c,d) ↔ a + d = c + b`. It is a linearly and strictly ordered
commutative ring whose nonnegative cone is exactly the image of the injective
semiring embedding `ι : V →+* DiffRing V`.

`internalZero_iff` turns a model-level zero of split-natural syntax into the
vanishing of ordinary ring evaluation, so integer-coefficient identities and
ordered-ring arguments apply inside an arbitrary model. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.ModelDifferenceRing

section Ring
variable (V : Type*) [CommSemiring V] [LinearOrder V] [IsStrictOrderedRing V]
  [CanonicallyOrderedAdd V]

def setoid : Setoid (V × V) where
  r p q := p.1 + q.2 = q.1 + p.2
  iseqv := {
    refl := fun _ => rfl
    symm := fun h => h.symm
    trans := fun {p q r} h k => by
      apply add_right_cancel (b := q.1 + q.2)
      calc p.1 + r.2 + (q.1 + q.2) = (p.1 + q.2) + (q.1 + r.2) := by ac_rfl
        _ = (q.1 + p.2) + (r.1 + q.2) := by rw [h, k]
        _ = r.1 + p.2 + (q.1 + q.2) := by ac_rfl }

def DiffRing : Type _ := Quotient (setoid V)

variable {V}

def mk (a b : V) : DiffRing V := Quotient.mk (setoid V) (a, b)

theorem mk_eq {a b c d : V} : mk a b = mk c d ↔ a + d = c + b := Quotient.eq

theorem exists_mk (x : DiffRing V) : ∃ a b : V, x = mk a b :=
  Quotient.inductionOn x fun p => ⟨p.1, p.2, rfl⟩

def mulPair (p q : V × V) : V × V := (p.1 * q.1 + p.2 * q.2, p.1 * q.2 + p.2 * q.1)

theorem mulPair_left {p p' : V × V} (hp : p.1 + p'.2 = p'.1 + p.2) (q : V × V) :
    (mulPair p q).1 + (mulPair p' q).2 = (mulPair p' q).1 + (mulPair p q).2 := by
  have h2 : p.2 + p'.1 = p'.2 + p.1 := by
    rw [add_comm p.2, add_comm p'.2]; exact hp.symm
  calc (mulPair p q).1 + (mulPair p' q).2 = (p.1 + p'.2) * q.1 + (p.2 + p'.1) * q.2 := by
        simp only [mulPair]; ring
    _ = (p'.1 + p.2) * q.1 + (p'.2 + p.1) * q.2 := by rw [hp, h2]
    _ = (mulPair p' q).1 + (mulPair p q).2 := by simp only [mulPair]; ring

theorem mulPair_right {q q' : V × V} (hq : q.1 + q'.2 = q'.1 + q.2) (p : V × V) :
    (mulPair p q).1 + (mulPair p q').2 = (mulPair p q').1 + (mulPair p q).2 := by
  have h2 : q.2 + q'.1 = q'.2 + q.1 := by
    rw [add_comm q.2, add_comm q'.2]; exact hq.symm
  calc (mulPair p q).1 + (mulPair p q').2 = p.1 * (q.1 + q'.2) + p.2 * (q.2 + q'.1) := by
        simp only [mulPair]; ring
    _ = p.1 * (q'.1 + q.2) + p.2 * (q'.2 + q.1) := by rw [hq, h2]
    _ = (mulPair p q').1 + (mulPair p q).2 := by simp only [mulPair]; ring

instance : Zero (DiffRing V) := ⟨mk 0 0⟩
instance : One (DiffRing V) := ⟨mk 1 0⟩
instance : Neg (DiffRing V) := ⟨Quotient.map (fun p => (p.2, p.1)) fun p q h => by
  change p.2 + q.1 = q.2 + p.1
  change p.1 + q.2 = q.1 + p.2 at h
  rw [add_comm p.2, add_comm q.2]; exact h.symm⟩
instance : Add (DiffRing V) := ⟨Quotient.map₂ (fun p q => (p.1 + q.1, p.2 + q.2))
  fun p p' hp q q' hq => by
    change p.1 + p'.2 = p'.1 + p.2 at hp
    change q.1 + q'.2 = q'.1 + q.2 at hq
    change p.1 + q.1 + (p'.2 + q'.2) = p'.1 + q'.1 + (p.2 + q.2)
    calc p.1 + q.1 + (p'.2 + q'.2) = (p.1 + p'.2) + (q.1 + q'.2) := by ac_rfl
      _ = (p'.1 + p.2) + (q'.1 + q.2) := by rw [hp, hq]
      _ = p'.1 + q'.1 + (p.2 + q.2) := by ac_rfl⟩
instance : Mul (DiffRing V) := ⟨Quotient.map₂ mulPair fun p p' hp q q' hq =>
  (setoid V).iseqv.trans (show (setoid V).r _ _ from mulPair_left hp q)
    (show (setoid V).r _ _ from mulPair_right hq p')⟩

theorem zero_def : (0 : DiffRing V) = mk 0 0 := rfl
theorem one_def : (1 : DiffRing V) = mk 1 0 := rfl
theorem mk_neg (a b : V) : -mk a b = mk b a := rfl
theorem mk_add (a b c d : V) : mk a b + mk c d = mk (a + c) (b + d) := rfl
theorem mk_mul (a b c d : V) : mk a b * mk c d = mk (a * c + b * d) (a * d + b * c) := rfl

instance : CommRing (DiffRing V) where
  add_assoc x y z := by
    obtain ⟨a, b, rfl⟩ := exists_mk x; obtain ⟨c, d, rfl⟩ := exists_mk y
    obtain ⟨e, f, rfl⟩ := exists_mk z
    rw [mk_add, mk_add, mk_add, mk_add, mk_eq]; ring
  zero_add x := by
    obtain ⟨a, b, rfl⟩ := exists_mk x; rw [zero_def, mk_add, mk_eq]; ring
  add_zero x := by
    obtain ⟨a, b, rfl⟩ := exists_mk x; rw [zero_def, mk_add, mk_eq]; ring
  add_comm x y := by
    obtain ⟨a, b, rfl⟩ := exists_mk x; obtain ⟨c, d, rfl⟩ := exists_mk y
    rw [mk_add, mk_add, mk_eq]; ring
  mul_assoc x y z := by
    obtain ⟨a, b, rfl⟩ := exists_mk x; obtain ⟨c, d, rfl⟩ := exists_mk y
    obtain ⟨e, f, rfl⟩ := exists_mk z
    rw [mk_mul, mk_mul, mk_mul, mk_mul, mk_eq]; ring
  one_mul x := by
    obtain ⟨a, b, rfl⟩ := exists_mk x; rw [one_def, mk_mul, mk_eq]; ring
  mul_one x := by
    obtain ⟨a, b, rfl⟩ := exists_mk x; rw [one_def, mk_mul, mk_eq]; ring
  left_distrib x y z := by
    obtain ⟨a, b, rfl⟩ := exists_mk x; obtain ⟨c, d, rfl⟩ := exists_mk y
    obtain ⟨e, f, rfl⟩ := exists_mk z
    rw [mk_add, mk_mul, mk_mul, mk_mul, mk_add, mk_eq]; ring
  right_distrib x y z := by
    obtain ⟨a, b, rfl⟩ := exists_mk x; obtain ⟨c, d, rfl⟩ := exists_mk y
    obtain ⟨e, f, rfl⟩ := exists_mk z
    rw [mk_add, mk_mul, mk_mul, mk_mul, mk_add, mk_eq]; ring
  zero_mul x := by
    obtain ⟨a, b, rfl⟩ := exists_mk x; rw [zero_def, mk_mul, mk_eq]; ring
  mul_zero x := by
    obtain ⟨a, b, rfl⟩ := exists_mk x; rw [zero_def, mk_mul, mk_eq]; ring
  mul_comm x y := by
    obtain ⟨a, b, rfl⟩ := exists_mk x; obtain ⟨c, d, rfl⟩ := exists_mk y
    rw [mk_mul, mk_mul, mk_eq]; ring
  neg_add_cancel x := by
    obtain ⟨a, b, rfl⟩ := exists_mk x; rw [mk_neg, mk_add, zero_def, mk_eq]; ring
  nsmul := nsmulRec
  zsmul := zsmulRec

/-- The semiring embedding of `V` as the nonnegative elements. -/
def ι : V →+* DiffRing V where
  toFun a := mk a 0
  map_one' := rfl
  map_mul' a b := by rw [mk_mul, mk_eq]; ring
  map_zero' := rfl
  map_add' a b := by rw [mk_add, mk_eq]; ring

theorem ι_apply (a : V) : ι a = mk a 0 := rfl

theorem mk_eq_sub (a b : V) : mk a b = ι a - ι b := by
  rw [sub_eq_add_neg, ι_apply, ι_apply, mk_neg, mk_add, mk_eq]; ring

theorem ι_injective : Function.Injective (ι : V →+* DiffRing V) := by
  intro a b h
  have := mk_eq.mp h
  simpa using this

/-- Every element is `ι c` or `-ι c`. -/
theorem nonneg_or_nonpos (x : DiffRing V) : (∃ c, x = ι c) ∨ ∃ c, x = -ι c := by
  obtain ⟨a, b, rfl⟩ := exists_mk x
  rcases le_total b a with h | h
  · obtain ⟨c, rfl⟩ := exists_add_of_le h
    exact Or.inl ⟨c, by rw [ι_apply, mk_eq]; ring⟩
  · obtain ⟨c, rfl⟩ := exists_add_of_le h
    exact Or.inr ⟨c, by rw [ι_apply, mk_neg, mk_eq]; ring⟩

theorem ι_eq_neg_ι {a b : V} (h : ι a = -ι b) : a = 0 := by
  have h1 : ι (a + b) = ι 0 := by rw [map_add, h, neg_add_cancel, map_zero]
  exact (add_eq_zero.mp (ι_injective h1)).1

/-- The nonnegative cone. -/
def cone : RingCone (DiffRing V) where
  carrier := {x | ∃ a, x = ι a}
  add_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a + b, (map_add ι a b).symm⟩
  zero_mem' := ⟨0, (map_zero ι).symm⟩
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a * b, (map_mul ι a b).symm⟩
  one_mem' := ⟨1, (map_one ι).symm⟩
  eq_zero_of_mem_of_neg_mem' := by
    rintro _ ⟨a, rfl⟩ ⟨b, hb⟩
    have : a = 0 := ι_eq_neg_ι (neg_eq_iff_eq_neg.mp hb)
    rw [this, map_zero]

theorem mem_cone {x : DiffRing V} : x ∈ cone ↔ ∃ a, x = ι a := Iff.rfl

instance : HasMemOrNegMem (cone (V := V)) where
  mem_or_neg_mem x := by
    rcases nonneg_or_nonpos x with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · exact Or.inl ⟨c, rfl⟩
    · exact Or.inr ⟨c, by rw [neg_neg]⟩

open Classical in
instance : LinearOrder (DiffRing V) := LinearOrder.mkOfAddGroupCone cone

instance : IsOrderedRing (DiffRing V) := IsOrderedRing.mkOfCone cone

/-- Foundation's scoped `LE` for every `ORingStructure` would otherwise also apply
to `DiffRing V` in files that open `LO.FirstOrder.Arithmetic`; these instances
keep `≤` and `<` on the cone order there. -/
instance (priority := high) instLEDiffRing : LE (DiffRing V) := Preorder.toLE
instance (priority := high) instLTDiffRing : LT (DiffRing V) := Preorder.toLT

instance : Nontrivial (DiffRing V) :=
  ⟨⟨0, 1, fun h => by
    have := ι_injective (show ι (0 : V) = ι 1 by rw [map_zero, map_one]; exact h)
    exact zero_ne_one this⟩⟩

theorem ι_mul_ι_eq_zero {a b : V} (h : ι a * ι b = 0) : ι a = 0 ∨ ι b = 0 := by
  rw [← map_mul, ← map_zero ι] at h
  have hab := ι_injective h
  by_contra hne
  push_neg at hne
  have ha : a ≠ 0 := fun ha => hne.1 (by rw [ha, map_zero])
  have hb : b ≠ 0 := fun hb => hne.2 (by rw [hb, map_zero])
  exact (mul_pos (pos_iff_ne_zero.mpr ha) (pos_iff_ne_zero.mpr hb)).ne' hab

instance : NoZeroDivisors (DiffRing V) where
  eq_zero_or_eq_zero_of_mul_eq_zero {x y} h := by
    rcases nonneg_or_nonpos x with ⟨a, rfl⟩ | ⟨a, rfl⟩ <;>
    rcases nonneg_or_nonpos y with ⟨b, rfl⟩ | ⟨b, rfl⟩
    · exact ι_mul_ι_eq_zero h
    · rcases ι_mul_ι_eq_zero (by simpa using h) with h | h <;> simp [h]
    · rcases ι_mul_ι_eq_zero (by simpa using h) with h | h <;> simp [h]
    · rcases ι_mul_ι_eq_zero (by simpa using h) with h | h <;> simp [h]

instance : IsStrictOrderedRing (DiffRing V) := IsOrderedRing.toIsStrictOrderedRing _

theorem nonneg_iff {x : DiffRing V} : 0 ≤ x ↔ ∃ a, x = ι a := by
  change x - 0 ∈ cone ↔ _
  rw [sub_zero]; rfl

theorem ι_nonneg (a : V) : 0 ≤ ι a := nonneg_iff.mpr ⟨a, rfl⟩

theorem ι_le_ι {a b : V} : ι a ≤ ι b ↔ a ≤ b := by
  change ι b - ι a ∈ cone ↔ _
  constructor
  · rintro ⟨c, hc⟩
    have : ι b = ι (c + a) := by rw [map_add, ← hc, sub_add_cancel]
    rw [ι_injective this]; exact le_add_self
  · intro h
    obtain ⟨c, rfl⟩ := exists_add_of_le h
    exact ⟨c, by rw [map_add, add_sub_cancel_left]⟩

theorem ι_lt_ι {a b : V} : ι a < ι b ↔ a < b := by
  rw [lt_iff_le_not_ge, lt_iff_le_not_ge, ι_le_ι, ι_le_ι]

/-- Discreteness of `V` passes to its ring of differences. -/
theorem one_le_of_pos (hd : ∀ a : V, 0 < a → 1 ≤ a) {x : DiffRing V} (hx : 0 < x) : 1 ≤ x := by
  rcases nonneg_or_nonpos x with ⟨a, rfl⟩ | ⟨a, rfl⟩
  · rw [← map_one ι, ι_le_ι]
    rw [← map_zero ι, ι_lt_ι] at hx
    exact hd a hx
  · exfalso
    have := ι_nonneg a
    linarith

end Ring

/-! ### Evaluation of split-natural syntax -/

theorem evalSemiring_map {σ R S : Type*} [Semiring R] [Semiring S] (f : R →+* S)
    (e : NatExpr σ) (v : σ → R) :
    f (e.evalSemiring v) = e.evalSemiring (fun i => f (v i)) := by
  induction e <;> simp_all [NatExpr.evalSemiring]

theorem split_evalRing {σ R : Type*} [CommRing R] (e : Expr σ) (w : σ → R) :
    e.splitNatural.1.evalSemiring w - e.splitNatural.2.evalSemiring w = e.evalRing w := by
  induction e with
  | constant a =>
    have h := congrArg (Int.cast (R := R)) (Int.toNat_sub_toNat_neg a)
    push_cast at h
    simpa [Expr.splitNatural, NatExpr.evalSemiring, Expr.evalRing] using h
  | var i => simp [Expr.splitNatural, NatExpr.evalSemiring, Expr.evalRing]
  | add p q hp hq | sub p q hp hq | mul p q hp hq =>
    simp only [Expr.splitNatural, Expr.evalRing] at hp hq ⊢
    simp only [NatExpr.evalSemiring] at hp hq ⊢
    rw [← hp, ← hq]; ring

section Model
variable {V : Type*} [CommSemiring V] [LinearOrder V] [IsStrictOrderedRing V]
  [CanonicallyOrderedAdd V]

/-- A model-level zero is a zero of the ordinary ring evaluation. -/
theorem internalZero_iff {σ : Type*} (e : Expr σ) (v : σ → V) :
    AdaptiveEquationSyntax2011.InternalZero e v ↔ e.evalRing (fun i => ι (v i)) = 0 := by
  unfold AdaptiveEquationSyntax2011.InternalZero
  rw [← split_evalRing, sub_eq_zero, ← evalSemiring_map, ← evalSemiring_map]
  exact ι_injective.eq_iff.symm

end Model

end DiophantineConsistency.ModelDifferenceRing
