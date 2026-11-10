import DiophantineConsistency.Z10.Z10Regs
import DiophantineConsistency.Nine121.N105Prefix
import DiophantineConsistency.Nine121.N101Contract

/-! # Ten-integer package 106: the prefix registers and their sizes

Soundness step S7 of the route. The prefix of `Z10Regs` is the H1868 layout of package 105 at
the base `Bc b = 2^2134940 b²`, which is twice 105's base `Bq b = 2^2134939 b²`. The layout
data (`N105Layout`), the kernel coefficients (`N101Layout.c0/c1/c2`) and the two size cores
over plain variables (`N105Prefix.core_pos`, `core_le`) are reused; the statements about the
base are re-proved here for `Bc`.

In a commutative ring:

* `coded_eval`, `coded_sum`: the coded word is the source polynomial of `N105Layout` evaluated
  at the base, a sum of at most 1869 digits;
* `ker2_split`: the leading record of the quadratic kernel.

In a linearly ordered ring, with a bound `H ≥ 8` on every kernel coefficient, `1 ≤ b` and
`4096 H b² ≤ Bc b`:

* `coded_pos`: `coded > 0` as soon as `word ≥ Bc^116` (unconditional positivity);
* `coded_le`: on the range `0 ≤ word ≤ 35 b Bc^116`, `coded ≤ 2486 b² Bc^1868`;
* `sum_lt`: for `0 ≤ g < 4 · cap`, `Sc + Tc < NN`, `g < N0` and `mask < N0`.

In a model of `𝗜𝚺₁`, at the ports `pR` of the 121x8801 machine:

* `radix_eq'`, `threshold_eq'`, `radix_eq_H`: the scales are `2^2134940 = 8192 · Hc` and
  `2^34159017`, as images of model exponentials;
* `Bcm`, `ι_Bcm`, `v_facts`: the base as a model natural, a power of two at `b = 2^k`;
* `prefix_pos`: for a model natural `b > 0` and any model natural `g`, `coded > 0`,
  `mask, Tc, Sc ≥ 0` and `X ≥ NN − 1 ≥ 8`. The term `− 2` of `Tc` is absorbed by
  `N0 · AT · (Bc − 2) ≥ 2`;
* `prefix_naturals`: hence `X = ι Xn` with `Xn ≥ 8`, the two prefix inputs of
  `Z10BridgeSound.b_pow` and `Z10BridgeSound.central`. No cap on `g` is needed, because
  `X = (NN − 1)(Sc + 1) + NN · Tc`. -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Z10Prefix
open Polynomial
open Nine121 Nine121.SparseExtraction Nine121.N105Layout Z10Regs
open Nine121.N101Prefix (abs_kernel_le pow_step mul_pow_le_succ)
open Nine121.N105Prefix (core_pos core_le natDegree_sourcePoly)

section Ring
variable {A : Type*} [CommRing A]

theorem coded_eval (p : Fin 4 → A) (b g : A) (u : Fin 31 → A)
    (hu : word b g = ∑ i, u i * Bc b ^ weights i) :
    coded p b g = (sourcePoly p u).eval (Bc b) := by
  simp only [sourcePoly, eval_add, eval_mul, eval_pow, eval_wordPoly, eval_kernelPoly]
  rw [← hu, coded, ker0, ker1, ker2]
  ring

/-- The range-sum form of the coded word. -/
theorem coded_sum (p : Fin 4 → A) (b g : A) (u : Fin 31 → A)
    (hu : word b g = ∑ i, u i * Bc b ^ weights i) :
    coded p b g = ∑ e ∈ Finset.range 1869, (sourcePoly p u).coeff e * Bc b ^ e := by
  rw [coded_eval p b g u hu, eval_eq_sum_range' (n := 1869)
    (lt_of_le_of_lt (natDegree_sourcePoly p u) (by norm_num))]

/-- `ker2 = rest + Bc^1636`, the leading record split off. -/
theorem ker2_split (p : Fin 4 → A) (b : A) :
    ker2 p b = (∑ i : Fin 38, N101Layout.c2 p i.castSucc * Bc b ^ pos2 i.castSucc) +
      Bc b ^ 1636 := by
  rw [ker2, Fin.sum_univ_castSucc, show (Fin.last 38 : Fin 39) = ⟨38, by decide⟩ from rfl,
    N101Layout.c2_last, pos2_last, one_mul]

end Ring

section Order
variable {A : Type*} [CommRing A] [LinearOrder A] [IsStrictOrderedRing A]

theorem ell_ge (b : A) (hB : 0 ≤ Bc b) : Bc b ^ 116 ≤ ell b := by
  have h := Finset.single_le_sum (f := fun i : Fin 31 => Bc b ^ weights i)
    (fun i _ => pow_nonneg hB _) (Finset.mem_univ (20 : Fin 31))
  have e : weights 20 = 116 := rfl
  simp only [e] at h
  exact h

theorem ell_nonneg (b : A) (hB : 0 ≤ Bc b) : 0 ≤ ell b :=
  Finset.sum_nonneg (fun _ _ => pow_nonneg hB _)

theorem ell_le (b : A) (hB : 1 ≤ Bc b) : ell b ≤ 31 * Bc b ^ 116 := by
  calc ell b = ∑ i, Bc b ^ weights i := rfl
    _ ≤ ∑ _i : Fin 31, Bc b ^ 116 :=
        Finset.sum_le_sum (fun i _ => pow_le_pow_right₀ hB (weights_le i))
    _ = 31 * Bc b ^ 116 := by simp

theorem AT_le (b : A) (hB : 1 ≤ Bc b) : AT b ≤ 22 * Bc b ^ 1836 := by
  calc AT b = ∑ k, Bc b ^ targets k := rfl
    _ ≤ ∑ _k : Fin 22, Bc b ^ 1836 :=
        Finset.sum_le_sum (fun k _ => pow_le_pow_right₀ hB (targets_le k))
    _ = 22 * Bc b ^ 1836 := by simp

theorem AT_nonneg (b : A) (hB : 0 ≤ Bc b) : 0 ≤ AT b :=
  Finset.sum_nonneg (fun _ _ => pow_nonneg hB _)

theorem AT_ge_one (b : A) (hB : 1 ≤ Bc b) : 1 ≤ AT b := by
  have h := Finset.single_le_sum (f := fun k : Fin 22 => Bc b ^ targets k)
    (fun k _ => pow_nonneg (le_trans zero_le_one hB) _) (Finset.mem_univ (0 : Fin 22))
  exact le_trans (one_le_pow₀ hB) h

/-- The three kernel estimates. -/
theorem ker_bounds (p : Fin 4 → A) (b H : A) (hB : 1 ≤ Bc b)
    (hc : (∀ q, |N101Layout.c0 p q| ≤ H) ∧ (∀ q, |N101Layout.c1 p q| ≤ H) ∧
      (∀ q, |N101Layout.c2 p q| ≤ H)) :
    |ker0 p b| ≤ 6 * (H * Bc b ^ 1408) ∧ |ker1 p b| ≤ 36 * (H * Bc b ^ 1727) ∧
      Bc b ^ 1636 - 38 * (H * Bc b ^ 1635) ≤ ker2 p b ∧
      ker2 p b ≤ Bc b ^ 1636 + 38 * (H * Bc b ^ 1635) := by
  obtain ⟨h0, h1, h2⟩ := hc
  have k0 := abs_kernel_le pos0 (N101Layout.c0 p) H (Bc b) hB 1408 h0 pos0_le
  have k1 := abs_kernel_le pos1 (N101Layout.c1 p) H (Bc b) hB 1727 h1 pos1_le
  have k2 := abs_kernel_le (fun i : Fin 38 => pos2 i.castSucc)
    (fun i => N101Layout.c2 p i.castSucc) H (Bc b) hB 1635 (fun i => h2 _)
    (fun i => pos2_top _ (Fin.castSucc_lt_last i).ne)
  push_cast at k0 k1 k2
  rw [abs_le] at k2
  refine ⟨k0, k1, ?_, ?_⟩ <;> rw [ker2_split] <;> linarith [k2.1, k2.2]

/-- The scale consequences of `4096 H b² ≤ Bc b`. -/
theorem scale_facts (b H : A) (hb : 1 ≤ b) (hH : 8 ≤ H) (hBb : 4096 * H * (b * b) ≤ Bc b) :
    32768 ≤ Bc b ∧ 4096 * H ≤ Bc b ∧ 4096 * (b * b) ≤ Bc b ∧ b ≤ b * b := by
  have hb0 : (0 : A) ≤ b := by linarith
  have hbb : b ≤ b * b := le_mul_of_one_le_left hb0 hb
  have h1 : (1 : A) ≤ b * b := le_trans hb hbb
  have hH0 : (0 : A) ≤ H := by linarith
  have a1 : 4096 * H ≤ 4096 * H * (b * b) := le_mul_of_one_le_right (by linarith) h1
  have a2 : 4096 * (b * b) ≤ 4096 * H * (b * b) := by
    have := mul_le_mul_of_nonneg_right (show (4096 : A) ≤ 4096 * H by linarith)
      (by linarith : (0 : A) ≤ b * b)
    linarith
  refine ⟨by linarith, by linarith, by linarith, hbb⟩

/-- **Unconditional positivity** of the coded word (given `word ≥ Bc^116`). -/
theorem coded_pos (p : Fin 4 → A) (b g H : A) (hb : 1 ≤ b) (hH : 8 ≤ H)
    (hBb : 4096 * H * (b * b) ≤ Bc b)
    (hc : (∀ q, |N101Layout.c0 p q| ≤ H) ∧ (∀ q, |N101Layout.c1 p q| ≤ H) ∧
      (∀ q, |N101Layout.c2 p q| ≤ H))
    (hU : Bc b ^ 116 ≤ word b g) : 0 < coded p b g := by
  obtain ⟨hB32, hBH, -, -⟩ := scale_facts b H hb hH hBb
  obtain ⟨k0, k1, k2, -⟩ := ker_bounds p b H (by linarith) hc
  exact core_pos (Bc b) (word b g) _ _ _ H hB32 hBH hH k0 k1 k2 hU

/-- **The soundness-range upper bound** on the coded word. -/
theorem coded_le (p : Fin 4 → A) (b g H : A) (hb : 1 ≤ b) (hH : 8 ≤ H)
    (hBb : 4096 * H * (b * b) ≤ Bc b)
    (hc : (∀ q, |N101Layout.c0 p q| ≤ H) ∧ (∀ q, |N101Layout.c1 p q| ≤ H) ∧
      (∀ q, |N101Layout.c2 p q| ≤ H))
    (hU0 : 0 ≤ word b g) (hU : word b g ≤ 35 * (b * Bc b ^ 116)) :
    coded p b g ≤ 2486 * ((b * b) * Bc b ^ 1868) := by
  obtain ⟨hB32, hBH, -, -⟩ := scale_facts b H hb hH hBb
  obtain ⟨k0, k1, -, k2⟩ := ker_bounds p b H (by linarith) hc
  exact core_le (Bc b) (word b g) _ _ _ H b hb hB32 hBH hH k0 k1 k2 hU0 hU

/-- **The soundness range**: `Sc + Tc < NN`, `g < N0` and `mask < N0`. -/
theorem sum_lt (p : Fin 4 → A) (b g H : A) (hb : 1 ≤ b) (hH : 8 ≤ H)
    (hBb : 4096 * H * (b * b) ≤ Bc b)
    (hc : (∀ q, |N101Layout.c0 p q| ≤ H) ∧ (∀ q, |N101Layout.c1 p q| ≤ H) ∧
      (∀ q, |N101Layout.c2 p q| ≤ H))
    (hg0 : 0 ≤ g) (hg : g < 4 * cap b) :
    Sc p b g + Tc b < NN b ∧ g < N0 b ∧ mask b < N0 b := by
  obtain ⟨hB32, hBH, hBb', hbb'⟩ := scale_facts b H hb hH hBb
  have hB1 : (1 : A) ≤ Bc b := by linarith
  have hB0 : (0 : A) ≤ Bc b := by linarith
  have hb0 : (0 : A) ≤ b := by linarith
  have hbb : (1 : A) ≤ b * b := le_trans hb hbb'
  have hl := ell_le b hB1
  have hl0 := ell_nonneg b hB0
  have hT := AT_le b hB1
  have hT0 := AT_nonneg b hB0
  have hP : ∀ n, (0 : A) ≤ Bc b ^ n := fun n => pow_nonneg hB0 n
  have h4b : 4 * b ≤ Bc b := by linarith
  have hN0 : N0 b = Bc b * Bc b ^ 116 := by rw [N0, ← pow_succ']
  have e4 : 4 * cap b = 4 * b * Bc b ^ 116 := by rw [cap]; ring
  have hgN : g < N0 b := by
    rw [hN0]
    have := mul_le_mul_of_nonneg_right h4b (hP 116)
    linarith
  have hm : mask b < N0 b := by
    rw [mask]
    have := mul_nonneg hl0 (sub_nonneg.2 hb)
    linarith
  have hU0 : 0 ≤ word b g := by rw [word]; linarith
  have hU : word b g ≤ 35 * (b * Bc b ^ 116) := by
    rw [word]
    have := le_mul_of_one_le_left (hP 116) hb
    linarith
  have hG := coded_le p b g H hb hH hBb hc hU0 hU
  have k1 : Bc b ^ 1869 = Bc b * Bc b ^ 1868 := by rw [← pow_succ']
  have k2 : Bc b ^ 1837 ≤ (b * b) * Bc b ^ 1868 :=
    le_trans (pow_step _ hB1 _ _ (by norm_num)) (le_mul_of_one_le_left (hP 1868) hbb)
  have k3 : AT b * (Bc b - 1) ≤ 22 * Bc b ^ 1837 := by
    have a1 := mul_le_mul_of_nonneg_right hT (by linarith : (0 : A) ≤ Bc b - 1)
    have a2 : (22 : A) * Bc b ^ 1836 * (Bc b - 1) ≤ 22 * Bc b ^ 1836 * Bc b := by
      have := hP 1836; linarith
    have a3 : (22 : A) * Bc b ^ 1837 = 22 * Bc b ^ 1836 * Bc b := by rw [pow_succ]; ring
    linarith
  have k4 : (1 : A) ≤ (b * b) * Bc b ^ 1868 :=
    le_trans hbb (le_mul_of_one_le_right (by linarith) (one_le_pow₀ hB1))
  have hB8 : 32768 * (b * b) ≤ Bc b := by
    have := mul_le_mul_of_nonneg_right (show (4096 : A) * 8 ≤ 4096 * H by linarith)
      (le_trans zero_le_one hbb)
    linarith
  have k5 : 32768 * ((b * b) * Bc b ^ 1868) ≤ Bc b ^ 1869 := by
    rw [k1]
    have := mul_le_mul_of_nonneg_right hB8 (hP 1868)
    linarith
  have hX : 2 + AT b * (Bc b - 1) + 2 * coded p b g < Bc b ^ 1869 := by linarith
  have hL : NN b = N0 b * Bc b ^ 1869 := by
    rw [NN, N0, ← pow_add]
  have hNpos : 0 < N0 b := pow_pos (by linarith) _
  have a1 : N0 b * (2 + AT b * (Bc b - 1) + 2 * coded p b g) < N0 b * Bc b ^ 1869 :=
    mul_lt_mul_of_pos_left hX hNpos
  refine ⟨?_, hgN, hm⟩
  rw [hL, Sc, Tc]
  have e : g + N0 b * (AT b + 2 * coded p b g) + (mask b + N0 b * (AT b * (Bc b - 2)) - 2) =
      g + mask b - 2 + N0 b * (AT b * (Bc b - 1) + 2 * coded p b g) := by ring
  rw [e]
  linarith

end Order

section Model
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ModelDifferenceRing
open Nine121.N101Contract (Hc port_facts one_le_ι ι_exp_nat)

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

attribute [local irreducible] Mixed121Ports.ports

/-- The ports in the ring of differences. -/
local notation "pR" => Source31Facts.portsR (V := V) Mixed121Ports.ports

/-! ## Scales -/

theorem radix_eq' : ((radix : ℤ) : DiffRing V) = ι (Exp.exp (2134940 : V)) := by
  have h := ι_exp_nat (V := V) 2134940
  rw [Nat.cast_ofNat] at h
  rw [h, radix, Int.cast_pow, Int.cast_ofNat]

theorem threshold_eq' : ((threshold : ℤ) : DiffRing V) = ι (Exp.exp (34159017 : V)) := by
  have h := ι_exp_nat (V := V) 34159017
  rw [Nat.cast_ofNat] at h
  rw [h, threshold, Int.cast_pow, Int.cast_ofNat]

theorem ι_exp_thirteen : ι (Exp.exp (13 : V)) = (8192 : DiffRing V) := by
  have h := ι_exp_nat (V := V) 13
  rw [Nat.cast_ofNat] at h
  rw [h]; norm_num

theorem radix_eq_H : ((radix : ℤ) : DiffRing V) = 8192 * Hc := by
  rw [radix_eq', Hc, show (2134940 : V) = 13 + 2134927 by norm_num, exp_add, map_mul,
    ι_exp_thirteen]

/-- The model-natural base `Bc = 2^2134940 b²`. -/
def Bcm (b : V) : V := Exp.exp (2134940 : V) * (b * b)

theorem ι_Bcm (b : V) : ι (Bcm b) = Bc (ι b) := by
  rw [Bcm, map_mul, map_mul, Bc, radix_eq']

/-- The base dominates the kernel coefficients: `Bc = 8192 · Hc · b²`. -/
theorem hBc (b : V) : 4096 * Hc * (ι b * ι b) ≤ Bc (ι b) := by
  rw [Bc, radix_eq_H]
  have h8 := (port_facts (V := V)).1
  have h := _root_.mul_nonneg (by linarith : (0 : DiffRing V) ≤ Hc)
    (_root_.mul_self_nonneg (ι b))
  linarith

/-- At `b = 2^k` the base is `2^v`, `v = 2134940 + 2k`. -/
theorem v_facts (k v : V) (hv : v = 2134940 + k + k) :
    k ≤ v ∧ 1 ≤ v ∧ Bcm (Exp.exp k) = Exp.exp v := by
  refine ⟨by rw [hv]; exact le_add_left le_rfl, ?_, ?_⟩
  · rw [hv]; exact le_trans (by norm_num) (le_add_right (le_add_right le_rfl))
  · rw [Bcm, hv, exp_add, exp_add, mul_assoc]

/-! ## The prefix registers are model naturals -/

theorem prefix_pos (b g : V) (hb : 0 < b) :
    0 < coded pR (ι b) (ι g) ∧ 0 ≤ mask (ι b) ∧ 0 ≤ Tc (ι b) ∧ 0 ≤ Sc pR (ι b) (ι g) ∧
      NN (ι b) - 1 ≤ Xc pR (ι b) (ι g) ∧ 8 ≤ NN (ι b) - 1 := by
  obtain ⟨hH8, hc⟩ := port_facts (V := V)
  have hb1 := one_le_ι hb
  have hBb' := hBc b
  obtain ⟨hB32, -, hBb4, hbb⟩ := scale_facts (ι b) Hc hb1 hH8 hBb'
  have hB1 : (1 : DiffRing V) ≤ Bc (ι b) := by linarith
  have hB0 : (0 : DiffRing V) ≤ Bc (ι b) := by linarith
  have hP : ∀ n, (0 : DiffRing V) ≤ Bc (ι b) ^ n := fun n => pow_nonneg hB0 n
  have hg0 := ι_nonneg g
  have hl0 := ell_nonneg (ι b) hB0
  have hl := ell_le (ι b) hB1
  have hT0 := AT_nonneg (ι b) hB0
  have hT1 := AT_ge_one (ι b) hB1
  have hG := coded_pos pR (ι b) (ι g) Hc hb1 hH8 hBb' hc
    (by rw [word]; linarith [ell_ge (ι b) hB0])
  -- the mask is nonnegative
  have hm : 0 ≤ mask (ι b) := by
    rw [mask, N0, pow_succ']
    have a1 : ell (ι b) * (ι b - 1) ≤ 31 * Bc (ι b) ^ 116 * ι b :=
      mul_le_mul hl (by linarith) (by linarith) (by linarith [hP 116])
    have a2 : 4096 * (ι b * ι b) * Bc (ι b) ^ 116 ≤ Bc (ι b) * Bc (ι b) ^ 116 :=
      mul_le_mul_of_nonneg_right hBb4 (hP 116)
    have a3 : 31 * Bc (ι b) ^ 116 * ι b ≤ 31 * (ι b * ι b) * Bc (ι b) ^ 116 := by
      have := mul_le_mul_of_nonneg_right hbb (hP 116); linarith
    have a4 : (1 : DiffRing V) ≤ (ι b * ι b) * Bc (ι b) ^ 116 :=
      le_trans (le_trans hb1 hbb) (le_mul_of_one_le_right (by linarith) (one_le_pow₀ hB1))
    linarith
  -- the two units subtracted in `Tc` are absorbed by the high block
  have hN1 : (1 : DiffRing V) ≤ N0 (ι b) := by unfold N0; exact one_le_pow₀ hB1
  have h3 : (2 : DiffRing V) ≤ AT (ι b) * (Bc (ι b) - 2) := by
    have := mul_le_mul hT1 (by linarith : (2 : DiffRing V) ≤ Bc (ι b) - 2) (by norm_num)
      (by linarith)
    linarith
  have h4 : (2 : DiffRing V) ≤ N0 (ι b) * (AT (ι b) * (Bc (ι b) - 2)) := by
    have := mul_le_mul hN1 h3 (by norm_num) (by linarith)
    linarith
  have hTc : 0 ≤ Tc (ι b) := by rw [Tc]; linarith
  have hSc : 0 ≤ Sc pR (ι b) (ι g) := by
    rw [Sc]
    have := _root_.mul_nonneg (by linarith : (0 : DiffRing V) ≤ N0 (ι b))
      (by linarith : (0 : DiffRing V) ≤ AT (ι b) + 2 * coded pR (ι b) (ι g))
    linarith
  have hNB : Bc (ι b) ≤ Bc (ι b) ^ 1986 := by
    have := pow_step _ hB1 1 1986 (by norm_num); rwa [pow_one] at this
  have hNN : Bc (ι b) ≤ NN (ι b) := hNB
  have hX : NN (ι b) - 1 ≤ Xc pR (ι b) (ι g) := by
    rw [Xc]
    have h1 := _root_.mul_nonneg (by linarith : (0 : DiffRing V) ≤ NN (ι b) - 1) hSc
    have h2 := _root_.mul_nonneg (by linarith : (0 : DiffRing V) ≤ NN (ι b)) hTc
    linarith
  exact ⟨hG, hm, hTc, hSc, hX, by linarith⟩

/-- **S7, the prefix inputs of the bridge**: for a model natural `b > 0` and any model natural
`g`, the central-binomial argument `X` is a model natural `≥ 8`. -/
theorem prefix_naturals (b g : V) (hb : 0 < b) :
    ∃ Xn : V, Xc pR (ι b) (ι g) = ι Xn ∧ 8 ≤ Xn := by
  obtain ⟨-, -, -, -, hX, hN8⟩ := prefix_pos b g hb
  obtain ⟨Xn, hXn⟩ := nonneg_iff.mp (by linarith : (0 : DiffRing V) ≤ Xc pR (ι b) (ι g))
  refine ⟨Xn, hXn, ?_⟩
  apply (ι_le_ι (V := V)).mp
  rw [map_ofNat, ← hXn]
  linarith

#print axioms sum_lt
#print axioms prefix_naturals

end Model

end DiophantineConsistency.Z10Prefix
