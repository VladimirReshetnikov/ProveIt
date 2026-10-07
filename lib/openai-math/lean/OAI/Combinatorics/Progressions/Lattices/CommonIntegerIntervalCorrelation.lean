import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Ring
import OAI.Combinatorics.Progressions.Estimates.FixedPartnerPower

namespace OAI

section

namespace Erdos3

open scoped BigOperators

def integerGridStart (a L : ℕ) : ℕ := L * (a / L + 1)

def integerGridEnd (b L : ℕ) : ℕ := L * (b / L)

theorem integerGridStart_bounds (a : ℕ) {L : ℕ} (hL : 0 < L) :
    a ≤ integerGridStart a L ∧ integerGridStart a L ≤ a + L := by
  constructor
  · exact (Nat.lt_mul_div_succ a hL).le
  · dsimp [integerGridStart]
    rw [Nat.mul_add, Nat.mul_one]
    exact Nat.add_le_add_right (by simpa only [Nat.mul_comm] using Nat.div_mul_le_self a L) L

theorem integerGridEnd_bounds (b : ℕ) {L : ℕ} (hL : 0 < L) :
    integerGridEnd b L ≤ b ∧ b < integerGridEnd b L + L := by
  exact ⟨by simpa only [integerGridEnd, Nat.mul_comm] using Nat.div_mul_le_self b L,
    Nat.lt_mul_div_self_add hL⟩

theorem integer_grid_interval_geometry (a len : ℕ) {L : ℕ} (hL : 0 < L)
    (hsmall : 4 * L ≤ len) :
    a ≤ integerGridStart a L ∧ integerGridEnd (a + len) L ≤ a + len ∧
      integerGridStart a L < integerGridEnd (a + len) L ∧
      integerGridEnd (a + len) L - integerGridStart a L ≤ len ∧
      len ≤ 2 * (integerGridEnd (a + len) L - integerGridStart a L) ∧
      len ≤ (integerGridEnd (a + len) L - integerGridStart a L) + 2 * L := by
  have hs := integerGridStart_bounds a hL
  have he := integerGridEnd_bounds (a + len) hL
  omega

theorem norm_sum_subset_card_loss {α : Type*} [DecidableEq α]
    {S T : Finset α} (hTS : T ⊆ S) (f : α → ℂ) (hf : ∀ x ∈ S, ‖f x‖ ≤ 1) :
    ‖∑ x ∈ S, f x‖ ≤ ‖∑ x ∈ T, f x‖ + (S.card : ℝ) - (T.card : ℝ) := by
  have hsum := Finset.sum_sdiff (f := f) hTS
  have hb : ‖∑ x ∈ S \ T, f x‖ ≤ ((S \ T).card : ℝ) := by
    apply (norm_sum_le _ _).trans
    simpa using Finset.sum_le_sum (fun x hx => hf x (Finset.mem_sdiff.mp hx).1)
  have hc : ((S \ T).card : ℝ) + (T.card : ℝ) = (S.card : ℝ) := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hTS
  have hn := norm_add_le (∑ x ∈ S \ T, f x) (∑ x ∈ T, f x)
  rw [hsum] at hn
  linarith only [hb, hc, hn]

theorem integer_grid_interval_correlation (a len : ℕ) {L : ℕ} (hL : 0 < L)
    {ρ : ℝ} (hρ : 0 < ρ) (hρone : ρ ≤ 1) (hsmall : 4 * (L : ℝ) ≤ ρ * len)
    (f : ℤ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (hcorr : ρ ≤ ‖𝔼 n ∈ Finset.Ico (a : ℤ) (a + len), f n‖) :
    ρ / 2 ≤ ‖𝔼 n ∈ Finset.Ico (integerGridStart a L : ℤ)
      (integerGridEnd (a + len) L : ℤ), f n‖ := by
  have hsmallNat : 4 * L ≤ len := by
    have h := hsmall.trans (mul_le_of_le_one_left (Nat.cast_nonneg len) hρone)
    exact_mod_cast h
  obtain ⟨hstart, hend, hpos, hlenle, _, hloss⟩ := integer_grid_interval_geometry a len hL hsmallNat
  let S := Finset.Ico (a : ℤ) (a + len)
  let T := Finset.Ico (integerGridStart a L : ℤ) (integerGridEnd (a + len) L : ℤ)
  let d := integerGridEnd (a + len) L - integerGridStart a L
  have hTS : T ⊆ S := by
    intro n hn
    simp only [S, T, Finset.mem_Ico] at hn ⊢
    constructor <;> omega
  have hScard : S.card = len := by simp [S, Int.card_Ico]
  have hTcard : T.card = d := by
    simp only [T, Int.card_Ico]
    rw [← Int.natCast_sub hpos.le, Int.toNat_natCast]
  have hbound := norm_sum_subset_card_loss hTS f (fun n _ => hf n)
  rw [← Finset.card_mul_expect S f, ← Finset.card_mul_expect T f] at hbound
  simp only [norm_mul, Complex.norm_natCast, hScard, hTcard] at hbound
  have hd : (0 : ℝ) < d := by exact_mod_cast Nat.sub_pos_of_lt hpos
  have hdlen : (d : ℝ) ≤ len := by exact_mod_cast hlenle
  have hlossR : (len : ℝ) ≤ d + 2 * L := by exact_mod_cast hloss
  have hcor := mul_le_mul_of_nonneg_left hcorr (Nat.cast_nonneg len : (0 : ℝ) ≤ len)
  change ρ / 2 ≤ ‖𝔼 n ∈ T, f n‖
  nlinarith only [hbound, hcor, hsmall, hd, hdlen, hlossR, hρ]

end Erdos3

end

section

namespace Erdos3

theorem exists_exp_integer_grid_scale {p : ℝ} (hp : 0 ≤ p) {N : ℕ}
    (hN : Real.exp (2 * p + 8) ≤ (N : ℝ)) :
    ∃ L : ℕ, 0 < L ∧ 4 * (L : ℝ) ≤ Real.exp (-(2 * p)) * N ∧
      ((N / L + 2 : ℕ) : ℝ) ≤ Real.exp (2 * p + 5) := by
  let x := Real.exp (-(2 * p)) * N / 8
  let L := ⌊x⌋₊
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have h16 : (16 : ℝ) ≤ Real.exp 8 :=
    (by norm_num : (16 : ℝ) ≤ 2 ^ 8).trans (two_pow_le_exp_of_le 8 le_rfl)
  have hscaled : Real.exp 8 ≤ Real.exp (-(2 * p)) * N := by
    calc
      _ = Real.exp (-(2 * p)) * Real.exp (2 * p + 8) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hN (Real.exp_nonneg _)
  have hx2 : 2 ≤ x := by dsimp [x]; linarith only [h16, hscaled]
  have hfloor : (L : ℝ) ≤ x := Nat.floor_le hx0
  have hlt : x < (L : ℝ) + 1 := Nat.lt_floor_add_one x
  have hL : 0 < L := by
    have : (0 : ℝ) < L := by linarith only [hx2, hlt]
    exact_mod_cast this
  have hhalf : x ≤ 2 * (L : ℝ) := by linarith only [hx2, hlt]
  have hupper : 4 * (L : ℝ) ≤ Real.exp (-(2 * p)) * N := by
    dsimp [x] at hfloor hx0
    linarith only [hfloor, hx0]
  have hlower : Real.exp (-(2 * p)) * N ≤ 16 * (L : ℝ) := by
    dsimp [x] at hhalf
    linarith only [hhalf]
  have hNL : (N : ℝ) ≤ 16 * Real.exp (2 * p) * L := by
    calc
      _ = Real.exp (2 * p) * (Real.exp (-(2 * p)) * N) := by
        rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
      _ ≤ Real.exp (2 * p) * (16 * L) :=
        mul_le_mul_of_nonneg_left hlower (Real.exp_nonneg _)
      _ = _ := by ring
  have hdiv : ((N / L : ℕ) : ℝ) ≤ 16 * Real.exp (2 * p) :=
    Nat.cast_div_le.trans ((div_le_iff₀ (by exact_mod_cast hL : (0 : ℝ) < L)).mpr hNL)
  have h18 : (18 : ℝ) ≤ Real.exp 5 :=
    (by norm_num : (18 : ℝ) ≤ 2 ^ 5).trans (two_pow_le_exp_of_le 5 le_rfl)
  refine ⟨L, hL, hupper, ?_⟩
  calc
    _ = ((N / L : ℕ) : ℝ) + 2 := by norm_cast
    _ ≤ 18 * Real.exp (2 * p) := by
      have h1 := Real.one_le_exp (show 0 ≤ 2 * p by positivity)
      linarith only [hdiv, h1]
    _ ≤ Real.exp 5 * Real.exp (2 * p) := mul_le_mul_of_nonneg_right h18 (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_common_integer_interval {G : Type*} {p : ℝ} (hp : 0 ≤ p) {N : ℕ}
    (hN : Real.exp (2 * p + 8) ≤ (N : ℝ))
    (H : Finset G) (hH : H.Nonempty) (start len : G → ℕ)
    (hend : ∀ t ∈ H, start t + len t ≤ N)
    (hshort : ∀ t ∈ H, 2 * ((len t : ℤ) - 1) < N)
    (hlength : ∀ t ∈ H, Real.exp (-p) * N ≤ (len t : ℝ))
    (f : G → ℤ → ℂ) (hf : ∀ t ∈ H, ∀ n, ‖f t n‖ ≤ 1)
    (hcorr : ∀ t ∈ H, Real.exp (-p) ≤
      ‖𝔼 n ∈ Finset.Ico (start t : ℤ) (start t + len t), f t n‖) :
    ∃ S : Finset G, S ⊆ H ∧ S.Nonempty ∧
      Real.exp (-(4 * p + 10)) * (H.card : ℝ) ≤ (S.card : ℝ) ∧
      ∃ a d : ℕ, 0 < d ∧ a + d ≤ N ∧ 2 * ((d : ℤ) - 1) < N ∧
        Real.exp (-(p + 1)) * N ≤ (d : ℝ) ∧
        ∀ t ∈ S, Real.exp (-(p + 1)) ≤
          ‖𝔼 n ∈ Finset.Ico (a : ℤ) (a + d), f t n‖ := by
  classical
  obtain ⟨L, hL, hscale, hgrid⟩ := exists_exp_integer_grid_scale hp hN
  have hrho : Real.exp (-p) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith only [hp])
  have hsmall (t : G) (ht : t ∈ H) : 4 * (L : ℝ) ≤ Real.exp (-p) * len t := by
    apply hscale.trans
    calc
      _ = Real.exp (-p) * (Real.exp (-p) * N) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hlength t ht) (Real.exp_nonneg _)
  have hsmallNat (t : G) (ht : t ∈ H) : 4 * L ≤ len t := by
    exact_mod_cast (hsmall t ht).trans (mul_le_of_le_one_left (Nat.cast_nonneg _) hrho)
  let P := Fin (N / L + 2) × Fin (N / L + 2)
  let rel (t : G) (_ : Unit) (c : P) : Prop :=
    start t / L + 1 = c.1.val ∧ (start t + len t) / L = c.2.val
  have hchoice : ∀ t ∈ H, ∀ u, ∃ c, rel t u c := by
    intro t ht _
    have hs : start t ≤ N := by have hh := hend t ht; omega
    have hsd : start t / L ≤ N / L := Nat.div_le_div_right hs
    have hed : (start t + len t) / L ≤ N / L := Nat.div_le_div_right (hend t ht)
    exact ⟨(⟨start t / L + 1, by omega⟩, ⟨(start t + len t) / L, by omega⟩), rfl, rfl⟩
  have hcount : (Fintype.card P : ℝ) ≤ Real.exp (4 * p + 10) := by
    simp only [P, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
    calc
      _ ≤ Real.exp (2 * p + 5) * Real.exp (2 * p + 5) :=
        mul_le_mul hgrid hgrid (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  obtain ⟨c, S, hSH, hS, hSdense, hfixed⟩ := exists_large_fixed_choices H hH rel hchoice hcount
  let a := L * (c ()).1.val
  let b := L * (c ()).2.val
  let d := b - a
  have hround (t : G) (ht : t ∈ S) :
      integerGridStart (start t) L = a ∧ integerGridEnd (start t + len t) L = b := by
    obtain ⟨hs, he⟩ := hfixed t ht ()
    constructor
    · dsimp only [integerGridStart, a]
      rw [hs]
    · dsimp only [integerGridEnd, b]
      rw [he]
  obtain ⟨t0, ht0⟩ := hS
  have ht0H := hSH ht0
  have hgeom := integer_grid_interval_geometry (start t0) (len t0) hL (hsmallNat t0 ht0H)
  rw [(hround t0 ht0).1, (hround t0 ht0).2] at hgeom
  obtain ⟨_, hb, hab, hdlen, hhalf, _⟩ := hgeom
  have had : a + d = b := Nat.add_sub_of_le hab.le
  have hd : 0 < d := Nat.sub_pos_of_lt hab
  have hbN : b ≤ N := hb.trans (hend t0 ht0H)
  have hdshort : 2 * ((d : ℤ) - 1) < N := by
    have hs := hshort t0 ht0H
    change d ≤ len t0 at hdlen
    omega
  have hhalfR : (len t0 : ℝ) ≤ 2 * d := by exact_mod_cast hhalf
  have hvol : Real.exp (-p) / 2 * N ≤ (d : ℝ) := by
    have hv := hlength t0 ht0H
    nlinarith only [hv, hhalfR]
  have hthreshold : Real.exp (-(p + 1)) ≤ Real.exp (-p) / 2 := by
    simpa only [show -(p + 1) = -p - 1 by ring] using exp_sub_one_le_half_exp (-p)
  refine ⟨S, hSH, ⟨t0, ht0⟩, ?_, a, d, hd, ?_, hdshort, ?_, ?_⟩
  · simpa only [Fintype.card_unit, Nat.cast_one, mul_one] using hSdense
  · omega
  · exact (mul_le_mul_of_nonneg_right hthreshold (Nat.cast_nonneg _)).trans hvol
  · intro t ht
    have hc := integer_grid_interval_correlation (start t) (len t) hL
      (Real.exp_pos (-p)) hrho (hsmall t (hSH ht)) (f t) (hf t (hSH ht)) (hcorr t (hSH ht))
    rw [(hround t ht).1, (hround t ht).2] at hc
    have hupp : (a : ℤ) + d = b := by exact_mod_cast had
    simpa only [hupp] using hthreshold.trans hc

end Erdos3

end

end OAI
