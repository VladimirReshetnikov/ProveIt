import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! The new mechanism is the aggregate bound and one-shot endpoint transport.
The geometric estimate itself is existing library infrastructure. -/
namespace AggregateSafeSupport
open scoped BigOperators

theorem geom_sum_lt_pow {ρ : ℕ} (hρ : 2 ≤ ρ) (L : ℕ) :
    (∑ i ∈ Finset.range L, ρ^i) < ρ^L := by
  have hg := geom_sum_mul_of_one_le (by omega : 1 ≤ ρ) L
  have hl := Nat.le_mul_of_pos_right (∑ i ∈ Finset.range L, ρ^i)
    (by omega : 0 < ρ-1)
  have hp := Nat.pow_pos (by omega : 0 < ρ) (n := L)
  omega

theorem sparse_powers_lt {α : Type*} [DecidableEq α]
    {ρ L : ℕ} (hρ : 2 ≤ ρ) (S : Finset α) (e : α → ℕ)
    (hi : Function.Injective e) (he : ∀ j ∈ S, e j < L) :
    (∑ j ∈ S, ρ^(e j)) < ρ^L := by
  have hs : S.image e ⊆ Finset.range L := by
    intro n hn
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hn
    exact Finset.mem_range.mpr (he j hj)
  calc
    (∑ j ∈ S, ρ^(e j)) = ∑ n ∈ S.image e, ρ^n :=
      (Finset.sum_image hi.injOn).symm
    _ ≤ ∑ n ∈ Finset.range L, ρ^n := Finset.sum_le_sum_of_subset hs
    _ < ρ^L := geom_sum_lt_pow hρ L

/-- The actual two safe-position inequalities control the entire support,
independently of its cardinality. N=1 is allowed (then S must be empty). -/
theorem aggregate_increment_bound {N ρ K s : ℕ} [NeZero N]
    (hρ : 2 ≤ ρ) (hK : K < ρ^2022)
    (S : Finset (ZMod N))
    (hsafe : ∀ j ∈ S, j.val+1 < N ∧ j.val+s < N) :
    (K+ρ^(2011*s))*(ρ^977*(∑ j ∈ S, (ρ^2011)^j.val)) <
      ρ^(N*2011-2) := by
  have hN := NeZero.pos N
  have hr : 1 ≤ ρ := by omega
  have hk : K*(ρ^977*(∑ j ∈ S, (ρ^2011)^j.val)) < ρ^(N*2011-3) := by
    have hsum := sparse_powers_lt (L := N*2011-3) hρ S (fun j => 2999+2011*j.val)
      (by
        intro a b h
        dsimp only at h
        apply ZMod.val_injective N
        omega)
      (by
        intro j hj
        obtain ⟨hnext,_⟩ := hsafe j hj
        omega)
    apply lt_of_le_of_lt _ hsum
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    calc
      K*(ρ^977*(ρ^2011)^j.val) ≤ ρ^2022*(ρ^977*(ρ^2011)^j.val) :=
        Nat.mul_le_mul_right _ (Nat.le_of_lt hK)
      _ = ρ^(2999+2011*j.val) := by
        rw [← pow_mul, ← pow_add, ← pow_add]
        congr 1
        omega
  have ht : ρ^(2011*s)*(ρ^977*(∑ j ∈ S, (ρ^2011)^j.val)) <
      ρ^(N*2011-3) := by
    have hsum := sparse_powers_lt (L := N*2011-3) hρ S (fun j => 977+2011*(j.val+s))
      (by
        intro a b h
        dsimp only at h
        apply ZMod.val_injective N
        omega)
      (by
        intro j hj
        obtain ⟨_,htime⟩ := hsafe j hj
        omega)
    convert hsum using 1
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [← pow_mul, ← pow_add, ← pow_add]
    congr 1
    omega
  have he : N*2011-2 = (N*2011-3)+1 := by omega
  have hpow : ρ^(N*2011-2) = ρ^(N*2011-3)*ρ := by rw [he, pow_succ]
  rw [Nat.add_mul, hpow]
  have hm := Nat.mul_le_mul_left (ρ^(N*2011-3)) hρ
  omega

/-- The previous two-window capacity proposal is used as a baseline lemma,
not counted as a new proposal here. -/
theorem no_wrap {ρ m F Δ : ℕ} (hρ : 2 ≤ ρ) (hm : 2 ≤ m)
    (hF : F < ρ^(m-1)) (hΔ : Δ < ρ^(m-2)) : F+Δ < ρ^m-1 := by
  have hΔ' := hΔ.trans_le (Nat.pow_le_pow_right (by omega : 1 ≤ ρ)
    (by omega : m-2 ≤ m-1))
  have hm' : m = (m-1)+1 := by omega
  have hcap : 2*ρ^(m-1) ≤ ρ^m := by
    conv_rhs => rw [hm', pow_succ]
    simpa only [Nat.mul_comm] using Nat.mul_le_mul_left (ρ^(m-1)) hρ
  omega

/-- Both actual transports and the aggregate bound give the final equality
without constructing any intermediate carry witnesses. -/
theorem normalized_endpoint {N ρ K s C C' F F' : ℕ} [NeZero N]
    (hρ : 2 ≤ ρ) (hK : K < ρ^2022)
    (S : Finset (ZMod N))
    (hsafe : ∀ j ∈ S, j.val+1 < N ∧ j.val+s < N)
    (hC : C' = C+ρ^977*(∑ j ∈ S, (ρ^2011)^j.val))
    (hF : (K+ρ^(2011*s))*C ≡ F [MOD ρ^(N*2011)-1])
    (hF' : (K+ρ^(2011*s))*C' ≡ F' [MOD ρ^(N*2011)-1])
    (hsmall : F < ρ^(N*2011-1)) (hlt : F' < ρ^(N*2011)-1) :
    F' = F+(K+ρ^(2011*s))*(ρ^977*(∑ j ∈ S, (ρ^2011)^j.val)) := by
  have hd := aggregate_increment_bound hρ hK S hsafe
  have hn := no_wrap hρ (by have := NeZero.pos N; omega) hsmall hd
  have he : (K+ρ^(2011*s))*C' ≡
      F+(K+ρ^(2011*s))*(ρ^977*(∑ j ∈ S, (ρ^2011)^j.val)) [MOD ρ^(N*2011)-1] := by
    rw [hC, Nat.mul_add]
    exact hF.add_right _
  exact (hF'.symm.trans he).eq_of_lt_of_lt hlt hn

#print axioms aggregate_increment_bound
#print axioms normalized_endpoint
end AggregateSafeSupport
