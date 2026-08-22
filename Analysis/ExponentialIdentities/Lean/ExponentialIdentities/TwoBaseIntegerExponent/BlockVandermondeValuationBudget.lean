import ExponentialIdentities.TwoBaseIntegerExponent.BlockFiberFactorization
import Mathlib.NumberTheory.Padics.PadicVal.Basic

namespace LeanProofs.TwoBaseIntegerExponent

open Finset

/-- The unsigned Vandermonde product of a finite family of integer nodes. -/
def natVandermondeProduct {n : ℕ} (x : Fin n → ℤ) : ℕ :=
  ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, Int.natAbs (x j - x i)

/-- The number of ordered-by-index pairs of nodes that collide modulo `p ^ level`.
The use of the absolute integer difference makes this independent of which node is numerically larger. -/
def vandermondeCollisionCount {n : ℕ}
    (p level : ℕ) (x : Fin n → ℤ) : ℕ :=
  ∑ i : Fin n,
    ((Finset.Ioi i).filter fun j ↦ p ^ level ∣ Int.natAbs (x j - x i)).card

theorem padicValNat_eq_sum_pow_dvd {p n L : ℕ} [Fact p.Prime]
    (hn : n ≠ 0) (hL : padicValNat p n ≤ L) :
    padicValNat p n =
      ∑ ell ∈ Finset.range L, if p ^ (ell + 1) ∣ n then 1 else 0 := by
  classical
  let v := padicValNat p n
  have hdvd : ∀ ell : ℕ, (p ^ (ell + 1) ∣ n) ↔ ell + 1 ≤ v := by
    intro ell
    simpa [v] using (padicValNat_dvd_iff_le (p := p) (n := ell + 1) hn)
  have hfilter :
      (Finset.range L).filter (fun ell ↦ ell + 1 ≤ v) = Finset.range v := by
    ext ell
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  calc
    padicValNat p n = v := rfl
    _ = (Finset.range v).card := (Finset.card_range v).symm
    _ = ((Finset.range L).filter (fun ell ↦ ell + 1 ≤ v)).card := by rw [hfilter]
    _ = ∑ ell ∈ Finset.range L, if ell + 1 ≤ v then 1 else 0 := by
      simp
    _ = ∑ ell ∈ Finset.range L, if p ^ (ell + 1) ∣ n then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro ell _
      simp only [hdvd]

theorem padicValNat_finset_prod {p : ℕ} [Fact p.Prime]
    {ι : Type*} {s : Finset ι} {f : ι → ℕ}
    (hf : ∀ i ∈ s, f i ≠ 0) :
    padicValNat p (∏ i ∈ s, f i) = ∑ i ∈ s, padicValNat p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hfa : f a ≠ 0 := hf a (Finset.mem_insert_self a s)
      have hfs : ∀ i ∈ s, f i ≠ 0 := fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)
      rw [Finset.prod_insert ha, Finset.sum_insert ha,
        padicValNat.mul hfa (Finset.prod_ne_zero_iff.mpr hfs), ih hfs]

theorem natVandermondeProduct_ne_zero {n : ℕ}
    {x : Fin n → ℤ} (hx : Function.Injective x) : natVandermondeProduct x ≠ 0 := by
  classical
  simp only [natVandermondeProduct, Finset.prod_ne_zero_iff, Finset.mem_univ,
    true_implies, Finset.mem_Ioi]
  intro i j hij
  exact Int.natAbs_ne_zero.mpr (sub_ne_zero.mpr (hx.ne (ne_of_gt hij)))

theorem padicValNat_natVandermondeProduct {n p : ℕ} [Fact p.Prime]
    {x : Fin n → ℤ} (hx : Function.Injective x) :
    padicValNat p (natVandermondeProduct x) =
      ∑ i : Fin n, ∑ j ∈ Finset.Ioi i,
        padicValNat p (Int.natAbs (x j - x i)) := by
  classical
  unfold natVandermondeProduct
  rw [padicValNat_finset_prod]
  · apply Finset.sum_congr rfl
    intro i _
    rw [padicValNat_finset_prod]
    intro j hj
    exact Int.natAbs_ne_zero.mpr
      (sub_ne_zero.mpr (hx.ne (ne_of_gt (by simpa using hj))))
  · intro i _
    simp only [Finset.prod_ne_zero_iff]
    intro j hj
    exact Int.natAbs_ne_zero.mpr
      (sub_ne_zero.mpr (hx.ne (ne_of_gt (by simpa using hj))))

/-- **Exact collision-energy formula.**  If `L` bounds all pairwise valuations,
the valuation of the Vandermonde product is the total number of pair collisions
over the congruence depths `p, ..., p ^ L`. -/
theorem padicValNat_natVandermondeProduct_eq_sum_collisionCount
    {n p L : ℕ} [Fact p.Prime] {x : Fin n → ℤ} (hx : Function.Injective x)
    (hL : ∀ i : Fin n, ∀ j ∈ Finset.Ioi i,
      padicValNat p (Int.natAbs (x j - x i)) ≤ L) :
    padicValNat p (natVandermondeProduct x) =
      ∑ ell ∈ Finset.range L, vandermondeCollisionCount p (ell + 1) x := by
  classical
  rw [padicValNat_natVandermondeProduct hx]
  simp only [vandermondeCollisionCount]
  have hpair : ∀ i : Fin n, ∀ j ∈ Finset.Ioi i,
      padicValNat p (Int.natAbs (x j - x i)) =
        ∑ ell ∈ Finset.range L,
          if p ^ (ell + 1) ∣ Int.natAbs (x j - x i) then 1 else 0 := by
    intro i j hij
    apply padicValNat_eq_sum_pow_dvd
    · exact Int.natAbs_ne_zero.mpr
        (sub_ne_zero.mpr (hx.ne (ne_of_gt (by simpa using hij))))
    · exact hL i j hij
  calc
    (∑ i : Fin n, ∑ j ∈ Finset.Ioi i,
        padicValNat p (Int.natAbs (x j - x i))) =
      ∑ i : Fin n, ∑ j ∈ Finset.Ioi i,
        ∑ ell ∈ Finset.range L,
          if p ^ (ell + 1) ∣ Int.natAbs (x j - x i) then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j hj
          exact hpair i j hj
    _ =
      ∑ i : Fin n, ∑ ell ∈ Finset.range L, ∑ j ∈ Finset.Ioi i,
          if p ^ (ell + 1) ∣ Int.natAbs (x j - x i) then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
    _ = ∑ ell ∈ Finset.range L, ∑ i : Fin n, ∑ j ∈ Finset.Ioi i,
          if p ^ (ell + 1) ∣ Int.natAbs (x j - x i) then 1 else 0 := by
        rw [Finset.sum_comm]
    _ = ∑ ell ∈ Finset.range L, ∑ i : Fin n,
          ((Finset.Ioi i).filter fun j ↦
            p ^ (ell + 1) ∣ Int.natAbs (x j - x i)).card := by
        apply Finset.sum_congr rfl
        intro ell _
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.card_filter]

/-- An elementary replacement for a deep linear-forms estimate when only a
linear-in-the-exponents upper bound is needed.  A prime power dividing a
difference of powers cannot exceed the archimedean size of that difference. -/
theorem padicValNat_natAbs_pow_sub_pow_le
    {p a b d h : ℕ} (hp : p.Prime) :
    padicValNat p (Int.natAbs ((a ^ d : ℤ) - (b ^ h : ℤ))) ≤
      1 + d * Nat.clog p a + h * Nat.clog p b := by
  let ca := Nat.clog p a
  let cb := Nat.clog p b
  let E := d * ca + h * cb
  have ha0 : a ≤ p ^ ca := by
    exact Nat.le_pow_clog hp.one_lt a
  have hb0 : b ≤ p ^ cb := by
    exact Nat.le_pow_clog hp.one_lt b
  have ha : a ^ d ≤ p ^ (d * ca) := by
    calc
      a ^ d ≤ (p ^ ca) ^ d := Nat.pow_le_pow_left ha0 d
      _ = p ^ (d * ca) := by rw [← Nat.pow_mul, Nat.mul_comm]
  have hb : b ^ h ≤ p ^ (h * cb) := by
    calc
      b ^ h ≤ (p ^ cb) ^ h := Nat.pow_le_pow_left hb0 h
      _ = p ^ (h * cb) := by rw [← Nat.pow_mul, Nat.mul_comm]
  have hpa : p ^ (d * ca) ≤ p ^ E := by
    exact Nat.pow_le_pow_right (Nat.zero_lt_of_lt hp.one_lt)
      (Nat.le_add_right (d * ca) (h * cb))
  have hpb : p ^ (h * cb) ≤ p ^ E := by
    exact Nat.pow_le_pow_right (Nat.zero_lt_of_lt hp.one_lt)
      (Nat.le_add_left (h * cb) (d * ca))
  have hsize : Int.natAbs ((a ^ d : ℤ) - (b ^ h : ℤ)) ≤ p ^ (E + 1) := by
    calc
      Int.natAbs ((a ^ d : ℤ) - (b ^ h : ℤ)) ≤ a ^ d + b ^ h := by
        simpa only [Int.natAbs_pow, Int.natAbs_natCast, Int.natCast_pow] using
          Int.natAbs_sub_le (a ^ d : ℤ) (b ^ h : ℤ)
      _ ≤ p ^ E + p ^ E := Nat.add_le_add (ha.trans hpa) (hb.trans hpb)
      _ = 2 * p ^ E := by omega
      _ ≤ p * p ^ E := Nat.mul_le_mul_right (p ^ E) hp.two_le
      _ = p ^ (E + 1) := by rw [pow_succ, Nat.mul_comm]
  calc
    padicValNat p (Int.natAbs ((a ^ d : ℤ) - (b ^ h : ℤ))) ≤
        Nat.log p (Int.natAbs ((a ^ d : ℤ) - (b ^ h : ℤ))) :=
      padicValNat_le_nat_log _
    _ ≤ Nat.log p (p ^ (E + 1)) := Nat.log_mono_right hsize
    _ = E + 1 := Nat.log_pow hp.one_lt _
    _ = 1 + d * Nat.clog p a + h * Nat.clog p b := by
      simp only [E, ca, cb]
      omega

/-- The unsigned product of variable-size Vandermonde blocks. -/
def blockVandermondeNatProduct
    {o : Type*} [Fintype o] [DecidableEq o]
    (s : o → ℕ) (x : ∀ k : o, Fin (s k) → ℤ) : ℕ :=
  ∏ k : o, natVandermondeProduct (x k)

theorem blockVandermondeNatProduct_ne_zero
    {o : Type*} [Fintype o] [DecidableEq o]
    {s : o → ℕ} {x : ∀ k : o, Fin (s k) → ℤ}
    (hx : ∀ k, Function.Injective (x k)) :
    blockVandermondeNatProduct s x ≠ 0 := by
  classical
  simp only [blockVandermondeNatProduct, Finset.prod_ne_zero_iff,
    Finset.mem_univ, true_implies]
  exact fun k ↦ natVandermondeProduct_ne_zero (hx k)

/-- Valuation of a product of Vandermonde blocks is the sum of all pairwise
valuations in all blocks. -/
theorem padicValNat_blockVandermondeNatProduct
    {o : Type*} [Fintype o] [DecidableEq o]
    {p : ℕ} [Fact p.Prime] {s : o → ℕ}
    {x : ∀ k : o, Fin (s k) → ℤ}
    (hx : ∀ k, Function.Injective (x k)) :
    padicValNat p (blockVandermondeNatProduct s x) =
      ∑ k : o, ∑ i : Fin (s k), ∑ j ∈ Finset.Ioi i,
        padicValNat p (Int.natAbs (x k j - x k i)) := by
  classical
  unfold blockVandermondeNatProduct
  rw [padicValNat_finset_prod]
  · apply Finset.sum_congr rfl
    intro k _
    exact padicValNat_natVandermondeProduct (hx k)
  · intro k _
    exact natVandermondeProduct_ne_zero (hx k)

/-- **Finite cubic block budget.**  If every pair in a block of size `s k`
has valuation at most `C * s k + D`, then that block contributes at most
`s k ^ 2 * (C * s k + D)`.  This deliberately loose closed form is robust
under variable block sizes and is enough for the `O(L^4)` first-layer bound
when there are `O(L)` blocks of size `O(L)`. -/
theorem padicValNat_blockVandermondeNatProduct_le_cubeBudget
    {o : Type*} [Fintype o] [DecidableEq o]
    {p : ℕ} [Fact p.Prime] {s : o → ℕ}
    {x : ∀ k : o, Fin (s k) → ℤ}
    (hx : ∀ k, Function.Injective (x k)) (C D : ℕ)
    (hpair : ∀ k (i : Fin (s k)) (j : Fin (s k)), j ∈ Finset.Ioi i →
      padicValNat p (Int.natAbs (x k j - x k i)) ≤ C * s k + D) :
    padicValNat p (blockVandermondeNatProduct s x) ≤
      ∑ k : o, (s k) ^ 2 * (C * s k + D) := by
  classical
  rw [padicValNat_blockVandermondeNatProduct hx]
  apply Finset.sum_le_sum
  intro k _
  calc
    (∑ i : Fin (s k), ∑ j ∈ Finset.Ioi i,
        padicValNat p (Int.natAbs (x k j - x k i))) ≤
        ∑ i : Fin (s k), s k * (C * s k + D) := by
      apply Finset.sum_le_sum
      intro i _
      calc
        (∑ j ∈ Finset.Ioi i,
            padicValNat p (Int.natAbs (x k j - x k i))) ≤
            ∑ _j ∈ Finset.Ioi i, (C * s k + D) := by
              apply Finset.sum_le_sum
              intro j hj
              exact hpair k i j hj
        _ = (Finset.Ioi i).card * (C * s k + D) := by simp
        _ ≤ s k * (C * s k + D) := by
          apply Nat.mul_le_mul_right
          simpa using (Finset.card_le_univ (s := Finset.Ioi i))
    _ = (s k) ^ 2 * (C * s k + D) := by
      simp [pow_two, mul_assoc]

/-- Uniform-size consequence of the cubic block budget. -/
theorem padicValNat_blockVandermondeNatProduct_le_uniformCubeBudget
    {o : Type*} [Fintype o] [DecidableEq o]
    {p : ℕ} [Fact p.Prime] {s : o → ℕ}
    {x : ∀ k : o, Fin (s k) → ℤ}
    (hx : ∀ k, Function.Injective (x k)) (C D S : ℕ)
    (hsize : ∀ k, s k ≤ S)
    (hpair : ∀ k (i : Fin (s k)) (j : Fin (s k)), j ∈ Finset.Ioi i →
      padicValNat p (Int.natAbs (x k j - x k i)) ≤ C * s k + D) :
    padicValNat p (blockVandermondeNatProduct s x) ≤
      Fintype.card o * (S ^ 2 * (C * S + D)) := by
  calc
    padicValNat p (blockVandermondeNatProduct s x) ≤
        ∑ k : o, (s k) ^ 2 * (C * s k + D) :=
      padicValNat_blockVandermondeNatProduct_le_cubeBudget hx C D hpair
    _ ≤ ∑ _k : o, S ^ 2 * (C * S + D) := by
      apply Finset.sum_le_sum
      intro k _
      apply Nat.mul_le_mul
      · exact Nat.pow_le_pow_left (hsize k) 2
      · exact Nat.add_le_add_right (Nat.mul_le_mul_left C (hsize k)) D
    _ = Fintype.card o * (S ^ 2 * (C * S + D)) := by simp

/-- Report-shaped elementary budget for a block family whose pair differences
reduce to differences `a^d - b^h`, with `h ≤ B*d`.  No linear-forms theorem is
used: the archimedean size bound above makes every pair valuation linear in
its index gap, and the variable-block estimate turns that into a cubic budget. -/
theorem padicValNat_blockVandermondeNatProduct_le_powDifferenceCubeBudget
    {o : Type*} [Fintype o] [DecidableEq o]
    {p a b B S : ℕ} (hp : p.Prime) {s : o → ℕ}
    {x : ∀ k : o, Fin (s k) → ℤ}
    (hx : ∀ k, Function.Injective (x k))
    (hsize : ∀ k, s k ≤ S)
    (heightGap : ∀ k, Fin (s k) → Fin (s k) → ℕ)
    (hheight : ∀ k (i j : Fin (s k)), j ∈ Finset.Ioi i →
      heightGap k i j ≤ B * (j.val - i.val))
    (hpow : ∀ k (i j : Fin (s k)), j ∈ Finset.Ioi i →
      padicValNat p (Int.natAbs (x k j - x k i)) ≤
        padicValNat p (Int.natAbs
          ((a ^ (j.val - i.val) : ℤ) - (b ^ heightGap k i j : ℤ)))) :
    padicValNat p (blockVandermondeNatProduct s x) ≤
      Fintype.card o *
        (S ^ 2 * ((Nat.clog p a + B * Nat.clog p b) * S + 1)) := by
  letI : Fact p.Prime := ⟨hp⟩
  let C := Nat.clog p a + B * Nat.clog p b
  apply padicValNat_blockVandermondeNatProduct_le_uniformCubeBudget
    hx C 1 S hsize
  intro k i j hij
  let d := j.val - i.val
  let h := heightGap k i j
  have hd : d ≤ s k := by
    exact (Nat.sub_le _ _).trans (Nat.le_of_lt j.isLt)
  have hh : h ≤ B * d := hheight k i j hij
  have hda : d * Nat.clog p a ≤ s k * Nat.clog p a :=
    Nat.mul_le_mul_right _ hd
  have hhb : h * Nat.clog p b ≤ (B * Nat.clog p b) * s k := by
    calc
      h * Nat.clog p b ≤ (B * d) * Nat.clog p b :=
        Nat.mul_le_mul_right _ hh
      _ = (B * Nat.clog p b) * d := by ac_rfl
      _ ≤ (B * Nat.clog p b) * s k := Nat.mul_le_mul_left _ hd
  have hsum :
      1 + d * Nat.clog p a + h * Nat.clog p b ≤ C * s k + 1 := by
    calc
      1 + d * Nat.clog p a + h * Nat.clog p b =
          (d * Nat.clog p a + h * Nat.clog p b) + 1 := by omega
      _ ≤ (s k * Nat.clog p a + (B * Nat.clog p b) * s k) + 1 :=
        Nat.add_le_add_right (Nat.add_le_add hda hhb) 1
      _ = C * s k + 1 := by
        dsimp only [C]
        ring
  calc
    padicValNat p (Int.natAbs (x k j - x k i)) ≤
        padicValNat p (Int.natAbs
          ((a ^ d : ℤ) - (b ^ h : ℤ))) := hpow k i j hij
    _ ≤ 1 + d * Nat.clog p a + h * Nat.clog p b :=
      padicValNat_natAbs_pow_sub_pow_le hp
    _ ≤ C * s k + 1 := hsum

end LeanProofs.TwoBaseIntegerExponent
