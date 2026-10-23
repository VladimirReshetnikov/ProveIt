import DiophantineConsistency.ObjectDistributivity
import Mathlib.Algebra.Ring.Defs

/-! # The internal omega as a genuine commutative semiring

Only the carrier's algebraic laws are packaged here. Its elements may be
nonstandard; no external induction principle or identification with Nat is
asserted. Operations have exactly the existing definable arithmetic graphs.
-/

namespace DiophantineConsistency.ObjectOmegaSemiring
open SetTheory SetTheory.Form
open LeanProofs.BoundedZFCConsistency ObjectArithmetic ObjectMultiplication
open ObjectAdditionLaws ObjectMultiplicationLaws ObjectDistributivity

set_option maxRecDepth 16000
universe u
variable {V : Type u} {mem : V → V → Prop}

theorem mulRel_one_left (H : ZFAxioms mem) {y : V} (hy : mem y (omegaV H)) :
    MulRel H (natV H 1) y y := by
  let ee : Nat → V := fun _ => vempty H
  have h : ∀ n, mem n (omegaV H) →
      Sat mem (scons n (scons (natV H 1) ee)) (mulForm 0 1 0) := by
    apply omega_ind H (mulForm 0 1 0) (scons (natV H 1) ee)
    · exact (mulForm_spec H _ 0 1 0).mpr (mulRel_zero H (natV_mem_omega H 1))
    · intro n hn ih
      have hm := mulRel_succ H ((mulForm_spec H _ 0 1 0).mp ih)
      change MulRel H (natV H 1) (vsucc H n) (addValue H n (natV H 1)) at hm
      have he : addValue H n (natV H 1)=vsucc H n := by
        change addValue H n (vsucc H (vempty H))=vsucc H n
        rw [addValue_succ_right H hn (vempty_in_omega H),addValue_zero_right H hn]
      rw [he] at hm
      exact (mulForm_spec H _ 0 1 0).mpr hm
  exact (mulForm_spec H _ 0 1 0).mp (h y hy)

abbrev Natural (H : ZFAxioms mem) := {x : V // mem x (omegaV H)}

namespace Natural
variable (H : ZFAxioms mem)

noncomputable def zero : Natural H := ⟨vempty H,vempty_in_omega H⟩
noncomputable def one : Natural H := ⟨natV H 1,natV_mem_omega H 1⟩

noncomputable def plus (x y : Natural H) : Natural H :=
  ⟨addValue H x.val y.val,addRel_result_nat H (addValue_rel H x.property y.property)⟩

noncomputable def times (x y : Natural H) : Natural H :=
  ⟨(mulRel_total H x.property y.property).choose,
    mulRel_result_nat H (mulRel_total H x.property y.property).choose_spec⟩

theorem plus_spec (x y : Natural H) : AddRel H x.val y.val (plus H x y).val :=
  addValue_rel H x.property y.property

theorem times_spec (x y : Natural H) : MulRel H x.val y.val (times H x y).val :=
  (mulRel_total H x.property y.property).choose_spec

noncomputable instance : CommSemiring (Natural H) where
  zero := zero H
  one := one H
  add := plus H
  mul := times H
  nsmul := @nsmulRec (Natural H) ⟨zero H⟩ ⟨plus H⟩
  natCast n := ⟨natV H n,natV_mem_omega H n⟩
  natCast_zero := rfl
  natCast_succ n := by
    apply Subtype.ext
    exact (addValue_numerals H n 1).symm
  add_assoc x y z := Subtype.ext (addValue_assoc H x.property y.property z.property)
  add_comm x y := Subtype.ext (addValue_comm H x.property y.property)
  zero_add x := Subtype.ext (addValue_zero_left H x.property)
  add_zero x := Subtype.ext (addValue_zero_right H x.property)
  mul_assoc x y z := by
    apply Subtype.ext
    exact mulRel_unique H
      (mulRel_assoc H (times_spec H x y) (times_spec H y z) (times_spec H (times H x y) z))
      (times_spec H x (times H y z))
  mul_comm x y := Subtype.ext
    (mulRel_unique H (mulRel_comm H (times_spec H x y)) (times_spec H y x))
  zero_mul x := Subtype.ext (mulRel_unique H (times_spec H (zero H) x)
    (mulRel_zero_left H x.property))
  mul_zero x := Subtype.ext (mulRel_unique H (times_spec H x (zero H)) (mulRel_zero H x.property))
  one_mul x := Subtype.ext (mulRel_unique H (times_spec H (one H) x) (mulRel_one_left H x.property))
  mul_one x := Subtype.ext (mulRel_unique H (times_spec H x (one H))
    (mulRel_comm H (mulRel_one_left H x.property)))
  left_distrib x y z := by
    apply Subtype.ext
    exact mulRel_unique H (times_spec H x (plus H y z))
      (mulRel_distrib_left H (plus_spec H y z) (times_spec H x y) (times_spec H x z)
        (plus_spec H (times H x y) (times H x z)))
  right_distrib x y z := by
    apply Subtype.ext
    exact mulRel_unique H (times_spec H (plus H x y) z)
      (mulRel_distrib_right H (plus_spec H x y) (times_spec H x z) (times_spec H y z)
        (plus_spec H (times H x z) (times H y z)))

theorem add_graph (x y : Natural H) : AddRel H x.val y.val (x+y).val := plus_spec H x y
theorem mul_graph (x y : Natural H) : MulRel H x.val y.val (x*y).val := times_spec H x y

theorem addRel_iff (x y z : Natural H) : AddRel H x.val y.val z.val ↔ x+y=z := by
  constructor
  · intro h
    exact Subtype.ext (addRel_unique H (add_graph H x y) h)
  · rintro rfl
    exact add_graph H x y

theorem mulRel_iff (x y z : Natural H) : MulRel H x.val y.val z.val ↔ x*y=z := by
  constructor
  · intro h
    exact Subtype.ext (mulRel_unique H (mul_graph H x y) h)
  · rintro rfl
    exact mul_graph H x y

theorem natCast_val (n : ℕ) : ((n : Natural H) : V)=natV H n := rfl

instance : Nontrivial (Natural H) :=
  ⟨⟨0,1,fun h => natV_succ_ne_vempty H 0 (congrArg Subtype.val h).symm⟩⟩

end Natural
end DiophantineConsistency.ObjectOmegaSemiring
