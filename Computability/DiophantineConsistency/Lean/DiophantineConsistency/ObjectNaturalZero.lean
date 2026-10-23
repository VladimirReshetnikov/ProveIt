import DiophantineConsistency.ObjectOmegaSemiring

/-! # No zero divisors over the entire internal omega -/
namespace DiophantineConsistency.ObjectNaturalZero
open SetTheory SetTheory.Form
open LeanProofs.BoundedZFCConsistency ObjectArithmetic ObjectMultiplication
open ObjectAdditionCancellation ObjectMultiplicationLaws ObjectOmegaSemiring

universe u
variable {V : Type u} {mem : V → V → Prop}

private def zeroProductStage : Form :=
  fAll (fImp (mulForm 2 0 1) (fOr (fEq 0 2) (fEq 1 2)))

private theorem zeroProductStage_spec (H : ZFAxioms mem) (n : V) (ee : Nat → V) :
    Sat mem (scons n (scons (vempty H) ee)) zeroProductStage ↔
      ∀ x, MulRel H x n (vempty H) → x=vempty H ∨ n=vempty H := by
  constructor
  · intro h x hx
    exact h x ((mulForm_spec H _ 2 0 1).mpr hx)
  · intro h x hx
    exact h x ((mulForm_spec H _ 2 0 1).mp hx)

theorem mulRel_zero_iff (H : ZFAxioms mem) {x y : V}
    (hx : mem x (omegaV H)) (hy : mem y (omegaV H)) :
    MulRel H x y (vempty H) ↔ x=vempty H ∨ y=vempty H := by
  constructor
  · intro hxy
    let ee : Nat → V := fun _ => vempty H
    have h : ∀ n, mem n (omegaV H) →
        Sat mem (scons n (scons (vempty H) ee)) zeroProductStage := by
      apply omega_ind H zeroProductStage (scons (vempty H) ee)
      · apply (zeroProductStage_spec H _ ee).mpr
        intro _ _
        exact Or.inr rfl
      · intro n hn _
        apply (zeroProductStage_spec H _ ee).mpr
        intro a ha
        obtain ⟨b,hb⟩ := mulRel_total H ha.1 hn
        have he : vempty H=addValue H b a := mulRel_unique H ha (mulRel_succ H hb)
        have hadd : AddRel H b a (vempty H) :=
          he.symm ▸ addValue_rel H (mulRel_result_nat H hb) ha.1
        exact Or.inl ((addRel_zero_iff H b a).mp hadd).2
    exact (zeroProductStage_spec H y ee).mp (h y hy) x hxy
  · rintro (rfl | rfl)
    · exact mulRel_zero_left H hy
    · exact mulRel_zero H hx

namespace Natural
variable (H : ZFAxioms mem)

instance : NoZeroDivisors (ObjectOmegaSemiring.Natural H) where
  eq_zero_or_eq_zero_of_mul_eq_zero {a b} h := by
    have hmul := (ObjectOmegaSemiring.Natural.mulRel_iff H a b 0).mpr h
    rcases (mulRel_zero_iff H a.property b.property).mp hmul with ha | hb
    · exact Or.inl (Subtype.ext ha)
    · exact Or.inr (Subtype.ext hb)

end Natural
end DiophantineConsistency.ObjectNaturalZero
