import GowersSzemeredi.Proofs16PairEnergyCS

/-! Cauchy--Schwarz for matching keys from two different finite families. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def keyMatchingCount {X Y Z : Type*} [DecidableEq Z] (S : Finset X) (T : Finset Y)
    (f : X → Z) (g : Y → Z) : Nat :=
  ((S ×ˢ T).filter fun p => f p.1 = g p.2).card

theorem keyMatchingCount_eq_sum {X Y Z : Type*} [Fintype Z] [DecidableEq Z]
    (S : Finset X) (T : Finset Y) (f : X → Z) (g : Y → Z) :
    keyMatchingCount S T f g =
      ∑ z, (S.filter fun x => f x = z).card * (T.filter fun y => g y = z).card := by
  unfold keyMatchingCount
  rw [Finset.card_filter,Finset.sum_product]
  have hinner : ∀ x ∈ S, (∑ y ∈ T, if f x = g y then 1 else 0) =
      (T.filter fun y => g y = f x).card := by
    intro x _
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro y _
    by_cases h : f x = g y
    · rw [if_pos h,if_pos h.symm]
    · rw [if_neg h,if_neg (Ne.symm h)]
  rw [Finset.sum_congr rfl hinner,← Finset.sum_fiberwise S f]
  apply Finset.sum_congr rfl
  intro z _
  rw [Finset.sum_congr rfl fun x hx => by rw [(Finset.mem_filter.mp hx).2]]
  rw [Finset.sum_const,smul_eq_mul]

theorem keyMatchingCount_sq_le {X Y Z : Type*} [Fintype Z] [DecidableEq Z]
    (S : Finset X) (T : Finset Y) (f : X → Z) (g : Y → Z) :
    (keyMatchingCount S T f g)^2 ≤ keyMatchingCount S S f f * keyMatchingCount T T g g := by
  rw [keyMatchingCount_eq_sum,keyMatchingCount_eq_sum,keyMatchingCount_eq_sum]
  simpa only [sq] using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun z => (S.filter fun x => f x = z).card) (fun z => (T.filter fun y => g y = z).card)

end LeanProofs.GowersSzemeredi
