import DiophantineConsistency.ObjectOmegaSemiring

/-! # No zero divisors over the entire internal omega -/
namespace DiophantineConsistency.ObjectNaturalZero
open SetTheory SetTheory.Form
open LeanProofs.BoundedZFCConsistency ObjectArithmetic ObjectMultiplication
open ObjectAdditionCancellation ObjectMultiplicationLaws ObjectOmegaSemiring

universe u
variable {V : Type u} {mem : V → V → Prop}

theorem mulRel_zero_iff (H : ZFAxioms mem) {x y : V}
    (hx : mem x (omegaV H)) (hy : mem y (omegaV H)) :
    MulRel H x y (vempty H) ↔ x=vempty H ∨ y=vempty H := by
  constructor
  · intro hxy
    rcases nat_zero_or_succ H y hy with rfl | ⟨n,hn,rfl⟩
    · exact Or.inr rfl
    · obtain ⟨b,hb⟩ := mulRel_total H hx hn
      have he : vempty H=addValue H b x := mulRel_unique H hxy (mulRel_succ H hb)
      have hadd : AddRel H b x (vempty H) :=
        he.symm ▸ addValue_rel H (mulRel_result_nat H hb) hx
      exact Or.inl ((addRel_zero_iff H b x).mp hadd).2
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
