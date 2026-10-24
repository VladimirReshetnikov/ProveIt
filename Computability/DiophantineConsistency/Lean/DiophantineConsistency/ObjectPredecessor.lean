import DiophantineConsistency.ObjectUnpair

/-! # Predecessor and its quadratic certificate on all internal naturals -/
noncomputable section
namespace DiophantineConsistency.ObjectPredecessor
open SetTheory ObjectOmegaSemiring
universe u
variable {V : Type u} {mem : V → V → Prop}
variable (H : ZFAxioms mem)
abbrev N := Natural H

private theorem exists_predecessor (x : N H) (hx : x≠0) : ∃ y : N H,x=y+1 :=
  (ObjectNaturalDiscrete.zero_or_add_one H x).resolve_left hx

def pred (x : N H) : N H :=
  if hx : x=0 then 0 else Classical.choose (exists_predecessor H x hx)

theorem pred_zero : pred H 0=0 := by simp [pred]

theorem pred_spec (x : N H) (hx : x≠0) : x=pred H x+1 := by
  simpa only [pred,dif_neg hx] using Classical.choose_spec (exists_predecessor H x hx)

theorem pred_add_one (x : N H) : pred H (x+1)=x := by
  exact add_right_cancel (pred_spec H (x+1) (ObjectNaturalDiscrete.add_one_ne_zero H x)).symm

theorem pred_cast (n : ℕ) : pred H (n : N H)=(n.pred : N H) := by
  cases n with
  | zero => exact pred_zero H
  | succ n => simpa only [Nat.cast_add,Nat.cast_one,Nat.pred_succ] using pred_add_one H (n : N H)

/-- The two residuals written as equality of their natural parts. -/
def Certificate (out n : N H) : Prop :=
  n*(out+1)=n*n ∧ out*(out+1)=out*n

theorem certificate_iff (out n : N H) : Certificate H out n ↔ out=pred H n := by
  constructor
  · rintro ⟨hn,ho⟩
    by_cases hz : n=0
    · subst n
      have hmul : out*(out+1)=0 := by simpa only [mul_zero] using ho
      have hout : out=0 := (mul_eq_zero.mp hmul).resolve_right
        (ObjectNaturalDiscrete.add_one_ne_zero H out)
      simpa only [pred_zero H] using hout
    · have he : out+1=n := mul_left_cancel₀ hz hn
      rw [← he,pred_add_one]
  · intro h
    subst out
    rcases ObjectNaturalDiscrete.zero_or_add_one H n with hz | ⟨s,hs⟩
    · subst n
      simp only [Certificate,pred_zero,zero_mul,and_self]
    · rw [hs,pred_add_one]
      exact ⟨rfl,rfl⟩

end DiophantineConsistency.ObjectPredecessor
