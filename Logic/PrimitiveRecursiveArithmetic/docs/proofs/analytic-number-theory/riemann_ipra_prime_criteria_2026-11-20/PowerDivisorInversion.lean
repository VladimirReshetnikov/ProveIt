import PowerDivisorBounds
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-! Composition, cancellation and an unconditional growth equivalence for
convolution along h-th powers. A is the summatory function, A(0)=0. -/
namespace PowerDivisorInversion
open Finset ArithmeticFunction
open scoped BigOperators

def act (h : ℕ) (w : ArithmeticFunction ℤ) (A : ℕ → ℤ) (N : ℕ) : ℤ :=
  ∑ d ∈ Icc 1 N, w d * A (N/d^h)

private theorem enlarge (h : ℕ) (hh : 0 < h) (w : ArithmeticFunction ℤ)
    (A : ℕ → ℤ) (hA : A 0 = 0) {M N : ℕ} (hm : M ≤ N) :
    act h w A M = ∑ d ∈ Icc 1 N, w d * A (M/d^h) := by
  apply sum_subset (fun x hx => mem_Icc.mpr ⟨(mem_Icc.mp hx).1, (mem_Icc.mp hx).2.trans hm⟩)
  intro x hx hxm
  have hx1 := (mem_Icc.mp hx).1
  have hx2 : M < x := by by_contra! h; exact hxm (mem_Icc.mpr ⟨hx1,h⟩)
  rw [Nat.div_eq_of_lt (hx2.trans_le (Nat.le_pow hh)), hA, mul_zero]

/-- A divisor pair whose product lies in 1..N already lies in the N by N square. -/
private theorem fiber (N n : ℕ) (hn : n ∈ Icc 1 N) :
    ((Icc 1 N ×ˢ Icc 1 N).filter (fun p : ℕ × ℕ => p.1*p.2 = n)) =
       n.divisorsAntidiagonal := by
  ext p
  simp only [mem_filter, mem_product, mem_Icc, Nat.mem_divisorsAntidiagonal]
  have ⟨hn1,hn2⟩ := mem_Icc.mp hn
  constructor
  · intro ⟨_,heq⟩; exact ⟨heq, by omega⟩
  · intro ⟨heq,_⟩
    have ha : 0 < p.1 := Nat.pos_of_mul_pos_right (heq ▸ hn1)
    have hb : 0 < p.2 := Nat.pos_of_mul_pos_left (heq ▸ hn1)
    have hprod : p.1*p.2 ≤ N := heq ▸ hn2
    exact ⟨⟨⟨ha,(Nat.le_mul_of_pos_right _ hb).trans hprod⟩,
      ⟨hb,(Nat.le_mul_of_pos_left _ ha).trans hprod⟩⟩,heq⟩

theorem act_mul (h : ℕ) (hh : 0 < h) (u v : ArithmeticFunction ℤ)
    (A : ℕ → ℤ) (hA : A 0 = 0) (N : ℕ) :
    act h u (act h v A) N = act h (u*v) A N := by
  let S := Icc 1 N
  let g := fun p : ℕ × ℕ => p.1 * p.2
  let f := fun p : ℕ × ℕ => (u p.1*v p.2) * A (N/(g p)^h)
  calc
    _ = ∑ d ∈ S, ∑ e ∈ S, f (d,e) := by
      unfold act
      apply sum_congr rfl; intro d _
      rw [show (∑ e ∈ Icc 1 (N/d^h), v e*A (N/d^h/e^h)) =
         ∑ e ∈ S, v e*A (N/d^h/e^h) from enlarge h hh v A hA (Nat.div_le_self ..), mul_sum]
      apply sum_congr rfl; intro e _
      dsimp [f,g]; rw [Nat.div_div_eq_div_mul, mul_pow, mul_assoc]
    _ = ∑ p ∈ S ×ˢ S, f p := (sum_product S S f).symm
    _ = ∑ p ∈ (S ×ˢ S).filter (fun p => g p ∈ S), f p := by
      symm; apply sum_subset (filter_subset ..); intro p hp hnot
      have hp1 := (mem_Icc.mp (mem_product.mp hp).1).1
      have hp2 := (mem_Icc.mp (mem_product.mp hp).2).1
      have hg : 0 < g p := Nat.mul_pos hp1 hp2
      have hbig : N < g p := by
        by_contra! h
        exact hnot (mem_filter.mpr ⟨hp,mem_Icc.mpr ⟨hg,h⟩⟩)
      dsimp [f]
      rw [Nat.div_eq_of_lt (hbig.trans_le (Nat.le_pow hh)), hA, mul_zero]
    _ = ∑ n ∈ S, ∑ p ∈ (S ×ˢ S).filter (fun p => g p = n), f p :=
      (sum_fiberwise_eq_sum_filter (S ×ˢ S) S g f).symm
    _ = _ := by
      apply sum_congr rfl; intro n hn
      rw [show (S ×ˢ S).filter (fun p => g p = n) = n.divisorsAntidiagonal from fiber N n hn,
          ArithmeticFunction.mul_apply, sum_mul]
      apply sum_congr rfl; intro p hp
      dsimp [f,g]
      rw [(Nat.mem_divisorsAntidiagonal.mp hp).1]

theorem act_one (h : ℕ) (A : ℕ → ℤ) (hA : A 0 = 0) (N : ℕ) :
    act h 1 A N = A N := by
  by_cases hn : N = 0
  · subst N; simp [act,hA]
  have hmem : 1 ∈ Icc 1 N := mem_Icc.mpr ⟨by decide,by omega⟩
  unfold act
  rw [sum_eq_single 1]
  · simp
  · intro b _ hb; simp [hb]
  · exact fun h => (h hmem).elim

def growthAt (F : ℕ → ℤ) (r c : ℕ) : Prop :=
  ∀ N, (F N).natAbs^(2*r) ≤ c*N^(r+1)

def Growth (F : ℕ → ℤ) : Prop := ∀ r > 0, ∃ c, growthAt F r c

theorem growth_act (h r c : ℕ) (hh : 2 ≤ h) (hr : 0 < r) (w : ArithmeticFunction ℤ)
    (hw : ∀ d > 0, (w d).natAbs ≤ 1) (A : ℕ → ℤ) (ha : growthAt A (2*r) c) :
    growthAt (act h w A) r ((c+1)*(8*r)^(2*r)) := by
  intro N
  let t := fun i => w (i+1)*A (N/(i+1)^h)
  have heq : act h w A N = ∑ i ∈ range N, t i := by
    have hset : Icc 1 N = Ico 1 (N+1) := by ext; simp
    simp only [act,hset,sum_Ico_eq_sum_range, Nat.add_sub_cancel]
    apply sum_congr rfl; intro i _; dsimp [t]; rw [Nat.add_comm 1 i]
  rw [heq]
  apply PowerDivisorBounds.power_divisor_transfer r c N hr t (fun i => N/(i+1)^h)
  · intro i _
    exact (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) hh)).trans (Nat.mul_div_le ..)
  · intro i _
    have hu : (t i).natAbs ≤ (A (N/(i+1)^h)).natAbs := by
      dsimp [t]; rw [Int.natAbs_mul]
      simpa only [Nat.one_mul] using Nat.mul_le_mul_right (A (N/(i+1)^h)).natAbs (hw (i+1) (by omega))
    exact (Nat.pow_le_pow_left hu _).trans
      (by simpa only [show 2*(2*r)=4*r by omega] using ha (N/(i+1)^h))

private theorem zetaSmall (d : ℕ) (hd : 0 < d) :
    ((↑zeta : ArithmeticFunction ℤ) d).natAbs ≤ 1 := by
  simp [ArithmeticFunction.natCoe_apply,zeta_apply_ne (by omega : d ≠ 0)]

private theorem muSmall (d : ℕ) (_ : 0 < d) : (moebius d).natAbs ≤ 1 := by
  have ht := @abs_moebius_le_one d
  rw [← Int.natCast_natAbs] at ht; exact_mod_cast ht

/-- The reverse implication uses actual Möbius inversion at each finite cutoff. -/
theorem growth_iff (h : ℕ) (hh : 2 ≤ h) (A : ℕ → ℤ) (ha : A 0 = 0) :
    Growth A ↔ Growth (act h (↑zeta) A) := by
  constructor
  · intro H r hr
    obtain ⟨c,hc⟩ := H (2*r) (by omega)
    exact ⟨_, growth_act h r c hh hr _ zetaSmall A hc⟩
  · intro H r hr
    obtain ⟨c,hc⟩ := H (2*r) (by omega)
    have ht := growth_act h r c hh hr _ muSmall _ hc
    have heq : act h moebius (act h (↑zeta) A) = A := by
      funext N; rw [act_mul h (by omega) _ _ _ ha, moebius_mul_coe_zeta, act_one h A ha]
    exact ⟨_, heq ▸ ht⟩

theorem uniform_growth_iff (A : ℕ → ℤ) (ha : A 0 = 0) :
    Growth A ↔ ∀ r > 0, ∃ C, ∀ h ≥ 2, growthAt (act h (↑zeta) A) r C := by
  constructor
  · intro H r hr
    obtain ⟨c,hc⟩ := H (2*r) (by omega)
    exact ⟨_, fun h hh => growth_act h r c hh hr _ zetaSmall A hc⟩
  · intro H; apply (growth_iff 2 (by decide) A ha).mpr
    intro r hr; obtain ⟨C,hC⟩ := H r hr; exact ⟨C,hC 2 (by decide)⟩

end PowerDivisorInversion
