import DiophantineConsistency.ObjectNaturalDiscrete
import DiophantineConsistency.QuadraticNatPairing

/-! # The max-square pairing certificate on every internal natural

This interprets the sharp local certificate without identifying internal
omega with external Nat. Inverse-pair existence and internal code transport
are separate obligations.
-/
noncomputable section
namespace DiophantineConsistency.ObjectNatPairing
open SetTheory
open LeanProofs.BoundedZFCConsistency ObjectOmegaSemiring
universe u
variable {V : Type u} {mem : V → V → Prop}
variable (H : ZFAxioms mem)
abbrev N := Natural H

/-- The branch convention is the direct checker's exact max-square pairing. -/
def pair (a b : N H) : N H := if a<b then b*b+a else a*a+a+b

/-- The four integer residuals, read as equalities of natural parts. -/
def Certificate (z a b t s m : N H) : Prop :=
  t*t=t ∧ m+t*b=b+t*a ∧ b+t*s+t*(s+1)=a+(s+1) ∧ z=m*m+a+t*b

theorem certificate_sound {z a b t s m : N H} (h : Certificate H z a b t s m) :
    z=pair H a b := by
  obtain ⟨ht,hm,hs,hz⟩ := h
  rcases (ObjectNaturalDiscrete.mul_self_eq_self_iff H t).mp ht with ht0 | ht1
  · subst t
    have hm' : m=b := by simpa only [zero_mul,add_zero] using hm
    subst m
    have hbs : b=a+s+1 := by simpa only [zero_mul,add_zero,add_assoc] using hs
    have hab := (ObjectNaturalDiscrete.lt_iff_exists_add_one H a b).mpr ⟨s,hbs⟩
    simpa only [pair,if_pos hab,zero_mul,add_zero] using hz
  · subst t
    have hm' : m=a := by
      apply add_right_cancel (b := b)
      simpa only [one_mul,add_comm b a] using hm
    subst m
    have hba : b+s=a := add_right_cancel (by simpa only [one_mul] using hs)
    have hle : b≤a := (ObjectNaturalOrder.Natural.le_iff_exists_add H b a).mpr ⟨s,hba⟩
    simpa only [pair,if_neg (not_lt_of_ge hle),one_mul] using hz

theorem certificate_complete {z a b : N H} (h : z=pair H a b) :
    ∃ t s m, Certificate H z a b t s m := by
  by_cases hab : a<b
  · obtain ⟨s,hs⟩ := (ObjectNaturalDiscrete.lt_iff_exists_add_one H a b).mp hab
    refine ⟨0,s,b,by simp,by simp,?_,?_⟩
    · simpa only [zero_mul,add_zero,add_assoc] using hs
    · simpa only [pair,if_pos hab,zero_mul,add_zero] using h
  · obtain ⟨s,hs⟩ := (ObjectNaturalOrder.Natural.le_iff_exists_add H b a).mp (le_of_not_gt hab)
    refine ⟨1,s,a,by simp,by simp [add_comm],?_,?_⟩
    · simp only [one_mul,hs]
    · simpa only [pair,if_neg hab,one_mul] using h

theorem exists_certificate_iff (z a b : N H) :
    (∃ t s m, Certificate H z a b t s m) ↔ z=pair H a b :=
  ⟨by rintro ⟨t,s,m,h⟩; exact certificate_sound H h,certificate_complete H⟩

theorem pair_cast (a b : ℕ) : pair H (a : N H) (b : N H)=(Nat.pair a b : N H) := by
  by_cases h : a<b <;> simp [pair,Nat.pair,ObjectNaturalDiscrete.cast_lt_cast,h]

end DiophantineConsistency.ObjectNatPairing
