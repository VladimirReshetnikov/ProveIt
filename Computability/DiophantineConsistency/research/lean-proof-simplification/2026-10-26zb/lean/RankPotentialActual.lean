import DiophantineConsistency.NativeRankVariation

/-! Optional exact rank comparisons using the actual imported windowRank.
This adds an API without modifying existing source definitions or proofs.
The actual safe coefficient mutation remains a separate obligation. -/

namespace LeanSimplification20261026.ActualRankPotential

open DiophantineConsistency
open DiophantineConsistency.NativeRankVariation

def potential (q C F : ℤ) : ℤ := C+q*F

theorem windowRank_affine (q C F MC MF J : ℤ) :
    windowRank q C F MC MF J =
      (q^2-potential q C F)*(q^2-1)+(MC+q*MF)*J := by
  unfold windowRank potential
  ring

/-- Rank comparison reverses comparison of a single scalar potential.
The same q and mask ports occur on both sides. -/
theorem windowRank_lt_iff (q C F C' F' MC MF J : ℤ) (hq : 1 < q) :
    windowRank q C' F' MC MF J < windowRank q C F MC MF J ↔
      potential q C F < potential q C' F' := by
  have hs : 0 < q^2-1 := by nlinarith
  rw [windowRank_affine, windowRank_affine, add_lt_add_iff_right,
    mul_lt_mul_iff_of_pos_right hs, sub_lt_sub_iff_left]

theorem windowRank_eq_iff (q C F C' F' MC MF J : ℤ) (hq : 1 < q) :
    windowRank q C' F' MC MF J = windowRank q C F MC MF J ↔
      potential q C' F' = potential q C F := by
  have hs : q^2-1 ≠ 0 := by nlinarith
  rw [windowRank_affine, windowRank_affine, add_left_inj,
    mul_left_inj' hs, sub_right_inj]

theorem windowRank_le_iff (q C F C' F' MC MF J : ℤ) (hq : 1 < q) :
    windowRank q C' F' MC MF J ≤ windowRank q C F MC MF J ↔
      potential q C F ≤ potential q C' F' := by
  have hs : 0 < q^2-1 := by nlinarith
  rw [windowRank_affine, windowRank_affine, add_le_add_iff_right,
    mul_le_mul_iff_of_pos_right hs, sub_le_sub_iff_left]

/-- A correlated increment is just one sufficient way to raise potential. -/
theorem potential_increment (q C F A δ : ℤ) :
    potential q (C+δ) (F+A*δ) = potential q C F+δ*(1+q*A) := by
  unfold potential
  ring

/-- The map forgets a direction: equal potential need not mean equal cells. -/
theorem potential_fiber (q C F k : ℤ) :
    potential q (C+q*k) (F-k) = potential q C F := by
  unfold potential
  ring

theorem rank_fiber (q C F MC MF J k : ℤ) :
    windowRank q (C+q*k) (F-k) MC MF J = windowRank q C F MC MF J := by
  rw [windowRank_affine, windowRank_affine, potential_fiber]

/-- The q=1 degeneracy is preserved: all (C,F) have the same rank. -/
theorem rank_at_one (C F C' F' MC MF J : ℤ) :
    windowRank 1 C F MC MF J = windowRank 1 C' F' MC MF J := by
  simp [windowRank]

/-- Actual Carrier65 fronts need only share q and J; their C and F changes
may be unrelated. The parameter vector keeps both mask ports fixed. -/
theorem core_rank_lt_iff (p : Fin 4 → ℤ) (v v' : Fin 14 → ℤ)
    (hq : (Carrier65.core p v').q =
      (Carrier65.core p v).q)
    (hJ : v' 0 = v 0) (hql : 1 < (Carrier65.core p v).q) :
    (Carrier65.core p v').rank <
        (Carrier65.core p v).rank ↔
      potential (Carrier65.core p v).q
          (Carrier65.core p v).C (v 1) <
        potential (Carrier65.core p v).q
          (Carrier65.core p v').C (v' 1) := by
  rw [core_rank p v', core_rank p v, hq, hJ]
  exact windowRank_lt_iff _ _ _ _ _ _ _ _ hql

theorem core_rank_eq_iff (p : Fin 4 → ℤ) (v v' : Fin 14 → ℤ)
    (hq : (Carrier65.core p v').q =
      (Carrier65.core p v).q)
    (hJ : v' 0 = v 0) (hql : 1 < (Carrier65.core p v).q) :
    (Carrier65.core p v').rank =
        (Carrier65.core p v).rank ↔
      potential (Carrier65.core p v).q
          (Carrier65.core p v').C (v' 1) =
        potential (Carrier65.core p v).q
          (Carrier65.core p v).C (v 1) := by
  rw [core_rank p v', core_rank p v, hq, hJ]
  exact windowRank_eq_iff _ _ _ _ _ _ _ _ hql

#print axioms windowRank_lt_iff
#print axioms windowRank_eq_iff
#print axioms windowRank_le_iff
#print axioms potential_increment
#print axioms rank_fiber
#print axioms rank_at_one
#print axioms core_rank_lt_iff
#print axioms core_rank_eq_iff

end LeanSimplification20261026.ActualRankPotential
