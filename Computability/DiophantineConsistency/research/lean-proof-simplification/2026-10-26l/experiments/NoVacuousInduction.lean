import DiophantineConsistency.ObjectMultiplicationLaws
import BoundedZFCConsistency.InternalSat

/-!
# Replace two inductions with their actual zero/successor case split

The two upstream successor cases ignore their induction hypotheses.  The
existing `nat_zero_or_succ` theorem already supplies precisely those cases for
every internal natural, including nonstandard ones.  No external Nat induction
and no unrestricted induction principle on the model are used here.
-/

namespace DiophantineConsistency.NoVacuousInduction

open SetTheory SetTheory.Form
open LeanProofs.BoundedZFCConsistency ObjectArithmetic ObjectMultiplication
open ObjectAdditionLaws ObjectMultiplicationLaws

universe u
variable {V : Type u} {mem : V → V → Prop}

theorem addRel_zero_iff (H : ZFAxioms mem) (x y : V) :
    AddRel H x y (vempty H) ↔ x = vempty H ∧ y = vempty H := by
  constructor
  · intro hxy
    rcases nat_zero_or_succ H y hxy.2.1 with rfl | ⟨n, hn, rfl⟩
    · exact ⟨(addRel_unique H hxy (addRel_zero H hxy.1)).symm, rfl⟩
    · obtain ⟨b, hb⟩ := addRel_total H hxy.1 hn
      have he : vempty H = vsucc H b := addRel_unique H hxy (addRel_succ H hb)
      exact False.elim (vempty_spec H b (he.symm ▸ vsucc_self H b))
  · rintro ⟨rfl, rfl⟩
    exact addRel_zero H (vempty_in_omega H)

theorem mulRel_zero_iff (H : ZFAxioms mem) {x y : V}
    (hx : mem x (omegaV H)) (hy : mem y (omegaV H)) :
    MulRel H x y (vempty H) ↔ x = vempty H ∨ y = vempty H := by
  constructor
  · intro hxy
    rcases nat_zero_or_succ H y hy with rfl | ⟨n, hn, rfl⟩
    · exact Or.inr rfl
    · obtain ⟨b, hb⟩ := mulRel_total H hx hn
      have he : vempty H = addValue H b x := mulRel_unique H hxy (mulRel_succ H hb)
      have hadd : AddRel H b x (vempty H) :=
        he.symm ▸ addValue_rel H (mulRel_result_nat H hb) hx
      exact Or.inl ((NoVacuousInduction.addRel_zero_iff H b x).mp hadd).2
  · rintro (rfl | rfl)
    · exact mulRel_zero_left H hy
    · exact mulRel_zero H hx

#print axioms addRel_zero_iff
#print axioms mulRel_zero_iff

end DiophantineConsistency.NoVacuousInduction
