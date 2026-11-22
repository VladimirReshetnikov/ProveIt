import PowerDivisorInversion
import Mathlib.NumberTheory.ArithmeticFunction.Liouville

/-! The ordinary Liouville and Möbius summatory criteria are equivalent for
the actual arithmetic functions of Mathlib. -/
namespace LiouvilleCriterion
open Finset ArithmeticFunction PowerDivisorInversion
open scoped BigOperators

def summatory (f : ArithmeticFunction ℤ) (N : ℕ) : ℤ := ∑ n ∈ Icc 1 N, f n

private theorem square_factor_unique {b d a m : ℕ} (hb : 0 < b) (hd : 0 < d)
    (ha : Squarefree a) (hm : Squarefree m) (he : b^2*a = d^2*m) : b = d := by
  apply Nat.eq_of_factorization_eq hb.ne' hd.ne'
  intro p
  have he' := congrArg (fun z : ℕ => z.factorization p) he
  simp only [Nat.factorization_mul (pow_ne_zero _ hb.ne') ha.ne_zero,
    Nat.factorization_mul (pow_ne_zero _ hd.ne') hm.ne_zero, Nat.factorization_pow,
    Finsupp.add_apply, Finsupp.smul_apply, nsmul_eq_mul] at he'
  have := ha.natFactorization_le_one p
  have := hm.natFactorization_le_one p
  omega

private theorem squarefree_sign {a b : ℕ} (ha : Squarefree a) (hb : 0 < b) :
    liouville (b^2*a) = moebius a := by
  rw [liouville_apply_mul, pow_two, liouville_apply_mul, liouville_apply hb.ne',
    liouville_apply ha.ne_zero, moebius_apply_of_squarefree ha]
  rcases neg_one_pow_eq_or ℤ (cardFactors b) with h | h <;> rw [h] <;> ring

/-- Group the signed points of the square hyperbola by d² m. In each fiber
exactly one quotient m is squarefree, by uniqueness of the parity factors. -/
theorem summatory_identity (N : ℕ) :
    act 2 (↑zeta) (summatory moebius) N = summatory liouville N := by
  let S := Icc 1 N
  let g := fun p : ℕ × ℕ => p.1^2*p.2
  let T := (S ×ˢ S).filter (fun p => g p ∈ S)
  have hsub (d : ℕ) (hd : d ∈ S) :
      S.filter (fun e => g (d,e) ∈ S) = Icc 1 (N/d^2) := by
    have hd1 := (mem_Icc.mp hd).1
    have hp : 0 < d^2 := pow_pos hd1 _
    ext e; simp only [mem_filter,mem_Icc,S,g]
    constructor
    · rintro ⟨⟨he,_⟩,_,heN⟩
      exact ⟨he,(Nat.le_div_iff_mul_le hp).mpr (Nat.mul_comm _ _ ▸ heN)⟩
    · rintro ⟨he,hle⟩
      exact ⟨⟨he,hle.trans (Nat.div_le_self ..)⟩,Nat.mul_pos hp he,
        Nat.mul_comm _ _ ▸ (Nat.le_div_iff_mul_le hp).mp hle⟩
  calc
    _ = ∑ d ∈ S, ∑ e ∈ S, if g (d,e) ∈ S then moebius e else 0 := by
      apply sum_congr rfl; intro d hd
      rw [← sum_filter,hsub d hd,ArithmeticFunction.natCoe_apply,
          zeta_apply_ne (by have := (mem_Icc.mp hd).1; omega : d ≠ 0)]
      simp [summatory]
    _ = ∑ p ∈ T, moebius p.2 := by
      dsimp [T]; rw [sum_filter, sum_product]
    _ = ∑ n ∈ S, ∑ p ∈ T.filter (fun p => g p = n), moebius p.2 :=
      (sum_fiberwise_of_maps_to (fun p hp => (mem_filter.mp hp).2) (fun p : ℕ × ℕ => moebius p.2)).symm
    _ = _ := by
      apply sum_congr rfl; intro n hn
      have ⟨hn1,hnN⟩ := mem_Icc.mp hn
      obtain ⟨a,b,ha,hb,hba,hsq⟩ := Nat.sq_mul_squarefree_of_pos hn1
      have hbaN : b^2*a ≤ N := hba.trans_le hnN
      have hbN := (Nat.le_self_pow (by decide : 2 ≠ 0) b).trans
        ((Nat.le_mul_of_pos_right _ ha).trans hbaN)
      have haN := (Nat.le_mul_of_pos_left _ (pow_pos hb _)).trans hbaN
      have hmem : (b,a) ∈ T.filter (fun p => g p = n) :=
        mem_filter.mpr ⟨mem_filter.mpr ⟨mem_product.mpr ⟨mem_Icc.mpr ⟨hb,hbN⟩,
          mem_Icc.mpr ⟨ha,haN⟩⟩,show b^2*a ∈ S from hba.symm ▸ hn⟩,hba⟩
      rw [sum_eq_single (b,a)]
      · exact hba ▸ (squarefree_sign hsq hb).symm
      · intro p hp hne
        apply moebius_eq_zero_of_not_squarefree; intro hs
        have he := (mem_filter.mp hp).2
        have hdp := (mem_Icc.mp (mem_product.mp (mem_filter.mp (mem_filter.mp hp).1).1).1).1
        have eqd := square_factor_unique hb hdp hsq hs (hba.trans he.symm)
        have eqm : a = p.2 := Nat.eq_of_mul_eq_mul_left (pow_pos hb _) (by
          dsimp [g] at he; rw [← eqd] at he; exact hba.trans he.symm)
        exact hne (Prod.ext eqd.symm eqm.symm)
      · exact fun h => (h hmem).elim

/-- No hypothesis on the actual sizes of the sums is assumed. -/
theorem mertens_iff_liouville :
    Growth (summatory moebius) ↔ Growth (summatory liouville) := by
  rw [← show act 2 (↑zeta) (summatory moebius) = summatory liouville from
    funext summatory_identity]
  exact growth_iff 2 (by decide) _ (by simp [summatory])

end LiouvilleCriterion
