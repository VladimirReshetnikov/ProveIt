import DiophantineConsistency.Nine121.N101Layout
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic.Linarith

/-! # Package 101's original31 prefix: definitions and the generic size estimates

The prefix of `101-constructive-reductions/nine/report_section.tex` (eq. origin-prefix), for the
translated original31 layout of `N101Layout`, in an arbitrary commutative ring:

  `B = 2^2134939 b²`, `ℓ = Σᵢ B^{wᵢ}`, `T* = Σₖ B^{qₖ}`, `U* = g + ℓ`,
  `G* = K₀(B) + U*(K₁(B) + U* K₂(B))`, `N₀ = B¹¹⁶`, `M₀ = N₀ − 1 − ℓ(b − 1)`,
  `T_c = M₀ + N₀ T*(B − 2)`, `S* = g + N₀(T* + 2G*)`, `L = 2bB¹⁹⁸³`,
  `R = L(1 + (T_c + S*)) − S* − 1`, `N = 2^16012032 B¹⁰⁵³`, `t = bB¹¹⁵`.

The two scales are the irreducible integers `baseScale`, `thresholdScale`, so no tactic ever
evaluates them. `Gs_eval` identifies `G*` with the evaluation of `N101Layout.sourcePoly` once
`U* = Σ uᵢ B^{wᵢ}`, and `natDegree_sourcePoly` bounds its degree by `1866`.

In a linearly ordered ring, with an abstract bound `H` on every kernel coefficient and
`4096 H b² ≤ B`, `8 ≤ H`, `1 ≤ b` (in the model: `H = 2^2134927`, `B = 4096 H b²`):

* `Gs_pos`: `G* > 0` as soon as `U* ≥ B¹¹⁵` (unconditional positivity of the prefix);
* `Gs_le`: on the soundness range `U* ≤ 35 b B¹¹⁵`, `G* ≤ 2486 b² B¹⁸⁶⁶`;
* `coeff_bound`: every coefficient `c` of `sourcePoly` at weights `0 ≤ uᵢ ≤ b` has
  `4|c| + 4 ≤ B`;
* `sum_lt_L`: on the soundness range, `S* + T_c < L`. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace Nine121.N101Prefix
open Polynomial SparseExtraction N101Layout

/-- The base scale `2^2134939` (`base_scale` of the JSON). -/
def baseScale : ℤ := 2 ^ 2134939

/-- The threshold scale `2^16012032` (`threshold_scale` of the JSON). -/
def thresholdScale : ℤ := 2 ^ 16012032

attribute [irreducible] baseScale thresholdScale

section Ring
variable {A : Type*} [CommRing A]

def Bq (b : A) : A := (baseScale : A) * (b * b)
def ell (b : A) : A := ∑ i, Bq b ^ weights i
def Tst (b : A) : A := ∑ k, Bq b ^ targets k
def ker0 (ports : Fin 4 → A) (b : A) : A := ∑ p, c0 ports p * Bq b ^ pos0 p
def ker1 (ports : Fin 4 → A) (b : A) : A := ∑ p, c1 ports p * Bq b ^ pos1 p
def ker2 (ports : Fin 4 → A) (b : A) : A := ∑ p, c2 ports p * Bq b ^ pos2 p
def Ust (b g : A) : A := g + ell b
def Gs (ports : Fin 4 → A) (b g : A) : A :=
  ker0 ports b + Ust b g * (ker1 ports b + Ust b g * ker2 ports b)
def N0 (b : A) : A := Bq b ^ 116
def maskq (b : A) : A := N0 b - 1 - ell b * (b - 1)
def Tcq (b : A) : A := maskq b + N0 b * (Tst b * (Bq b - 2))
def Scq (ports : Fin 4 → A) (b g : A) : A := g + N0 b * (Tst b + 2 * Gs ports b g)
def Lq (b : A) : A := 2 * b * Bq b ^ 1983
def Rq (ports : Fin 4 → A) (b g : A) : A :=
  Lq b * (1 + (Tcq b + Scq ports b g)) - Scq ports b g - 1
def Nq (b : A) : A := (thresholdScale : A) * Bq b ^ 1053
def tq (b : A) : A := b * Bq b ^ 115

theorem Gs_eval (ports : Fin 4 → A) (b g : A) (u : Fin 31 → A)
    (hu : Ust b g = ∑ i, u i * Bq b ^ weights i) :
    Gs ports b g = (sourcePoly ports u).eval (Bq b) := by
  simp only [sourcePoly, eval_add, eval_mul, eval_pow, eval_wordPoly, eval_kernelPoly]
  rw [← hu, Gs, ker0, ker1, ker2]
  ring

theorem natDegree_sourcePoly (ports : Fin 4 → A) (u : Fin 31 → A) :
    (sourcePoly ports u).natDegree ≤ 1866 := by
  have hw : (wordPoly weights u).natDegree ≤ 115 :=
    natDegree_sum_le_of_forall_le _ _ (fun i _ => (natDegree_monomial_le _).trans (weights_le i))
  have h2 : (kernelPoly pos2 (c2 ports)).natDegree ≤ 1636 :=
    natDegree_sum_le_of_forall_le _ _ (fun p _ => (natDegree_monomial_le _).trans (pos2_le p))
  have h1 : (kernelPoly pos1 (c1 ports)).natDegree ≤ 1726 :=
    natDegree_sum_le_of_forall_le _ _ (fun p _ => (natDegree_monomial_le _).trans (pos1_le p))
  have h0 : (kernelPoly pos0 (c0 ports)).natDegree ≤ 1406 :=
    natDegree_sum_le_of_forall_le _ _ (fun p _ => (natDegree_monomial_le _).trans (pos0_le p))
  have hq : (wordPoly weights u ^ 2 * kernelPoly pos2 (c2 ports)).natDegree ≤ 1866 :=
    (natDegree_mul_le_of_le (natDegree_pow_le_of_le 2 hw) h2).trans (by norm_num)
  have hl : (wordPoly weights u * kernelPoly pos1 (c1 ports)).natDegree ≤ 1866 :=
    (natDegree_mul_le_of_le hw h1).trans (by norm_num)
  exact natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le hq hl) (h0.trans (by norm_num))

/-- The range-sum form of `G*`. -/
theorem Gs_sum (ports : Fin 4 → A) (b g : A) (u : Fin 31 → A)
    (hu : Ust b g = ∑ i, u i * Bq b ^ weights i) :
    Gs ports b g = ∑ e ∈ Finset.range 1867, (sourcePoly ports u).coeff e * Bq b ^ e := by
  rw [Gs_eval ports b g u hu, eval_eq_sum_range' (n := 1867) (lt_of_le_of_lt (natDegree_sourcePoly ports u)
    (by norm_num))]

/-- `ker2 = rest + B¹⁶³⁶`, the leading record split off. -/
theorem ker2_split (ports : Fin 4 → A) (b : A) :
    ker2 ports b = (∑ i : Fin 38, c2 ports i.castSucc * Bq b ^ pos2 i.castSucc) + Bq b ^ 1636 := by
  rw [ker2, Fin.sum_univ_castSucc, show (Fin.last 38 : Fin 39) = ⟨38, by decide⟩ from rfl,
    c2_last, pos2_last, one_mul]

/-- A range sum supported on an injective table is the table sum. -/
theorem sum_range_table {M : Type*} [AddCommMonoid M] {m : ℕ} (w : Fin m → ℕ)
    (hw : Function.Injective w) (n : ℕ) (hn : ∀ i, w i < n) (f : ℕ → M)
    (hf : ∀ j < n, (∀ i, w i ≠ j) → f j = 0) :
    ∑ j ∈ Finset.range n, f j = ∑ i, f (w i) := by
  have himg : Finset.univ.image w ⊆ Finset.range n := by
    intro j hj
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hj
    exact Finset.mem_range.mpr (hn i)
  rw [← Finset.sum_subset himg, Finset.sum_image (fun i _ i' _ h => hw h)]
  intro j hj hnot
  apply hf j (Finset.mem_range.mp hj)
  rintro i rfl
  exact hnot (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)

end Ring

section Order
variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

theorem abs_kernel_le {m : ℕ} (pos : Fin m → ℕ) (c : Fin m → R) (H B : R) (hB : 1 ≤ B) (E : ℕ)
    (hc : ∀ p, |c p| ≤ H) (hpos : ∀ p, pos p ≤ E) :
    |∑ p, c p * B ^ pos p| ≤ m * (H * B ^ E) := by
  have hB0 : (0 : R) ≤ B := le_trans zero_le_one hB
  calc |∑ p, c p * B ^ pos p| ≤ ∑ p, |c p * B ^ pos p| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p : Fin m, H * B ^ E := by
        refine Finset.sum_le_sum (fun p _ => ?_)
        rw [abs_mul, abs_of_nonneg (pow_nonneg hB0 _)]
        exact mul_le_mul (hc p) (pow_le_pow_right₀ hB (hpos p)) (pow_nonneg hB0 _)
          ((abs_nonneg _).trans (hc p))
    _ = m * (H * B ^ E) := by simp

/-- The 81 kernel coefficients are bounded by `H` under the port bounds. -/
theorem c_bounds (p : Fin 4 → R) (H : R) (hp0 : 0 ≤ p 0) (hp1 : 0 ≤ p 1) (hp2 : 0 ≤ p 2)
    (hp3 : 0 ≤ p 3) (h20 : p 2 ≤ p 0) (h30 : p 3 ≤ 2 * p 0) (hH : 8 ≤ H) (hβ : 6 * p 0 ≤ H)
    (hββ : 6 * p 0 ^ 2 ≤ H) (hK : 2 * p 1 + 2 ≤ H) (hβK : 2 * p 0 + 2 * p 0 * p 1 ≤ H) :
    (∀ q, |c0 p q| ≤ H) ∧ (∀ q, |c1 p q| ≤ H) ∧ (∀ q, |c2 p q| ≤ H) := by
  have hA : 0 ≤ p 0 * p 3 := mul_nonneg hp0 hp3
  have hA' : p 0 * p 3 ≤ 2 * p 0 ^ 2 := by nlinarith
  have hC : 0 ≤ p 0 ^ 2 := sq_nonneg _
  have hD : 0 ≤ p 0 * p 1 := mul_nonneg hp0 hp1
  refine ⟨fun q => ?_, fun q => ?_, fun q => ?_⟩ <;> refine abs_le.2 ⟨?_, ?_⟩ <;>
    fin_cases q <;> simp [c0, c1, c2] <;> linarith

variable {A : Type*} [CommRing A] [LinearOrder A] [IsStrictOrderedRing A]


theorem ell_ge (b : A) (hB : 0 ≤ Bq b) : Bq b ^ 115 ≤ ell b := by
  have h := Finset.single_le_sum (f := fun i : Fin 31 => Bq b ^ weights i)
    (fun i _ => pow_nonneg hB _) (Finset.mem_univ (20 : Fin 31))
  have e : weights 20 = 115 := rfl
  simp only [e] at h
  exact h

theorem ell_nonneg (b : A) (hB : 0 ≤ Bq b) : 0 ≤ ell b :=
  Finset.sum_nonneg (fun i _ => pow_nonneg hB _)

theorem ell_le (b : A) (hB : 1 ≤ Bq b) : ell b ≤ 31 * Bq b ^ 115 := by
  calc ell b = ∑ i, Bq b ^ weights i := rfl
    _ ≤ ∑ _i : Fin 31, Bq b ^ 115 :=
        Finset.sum_le_sum (fun i _ => pow_le_pow_right₀ hB (weights_le i))
    _ = 31 * Bq b ^ 115 := by simp

theorem Tst_le (b : A) (hB : 1 ≤ Bq b) : Tst b ≤ 22 * Bq b ^ 1834 := by
  calc Tst b = ∑ k, Bq b ^ targets k := rfl
    _ ≤ ∑ _k : Fin 22, Bq b ^ 1834 :=
        Finset.sum_le_sum (fun k _ => pow_le_pow_right₀ hB (targets_le k))
    _ = 22 * Bq b ^ 1834 := by simp

theorem Tst_nonneg (b : A) (hB : 0 ≤ Bq b) : 0 ≤ Tst b :=
  Finset.sum_nonneg (fun k _ => pow_nonneg hB _)

/-- The three kernel estimates. -/
theorem ker_bounds (ports : Fin 4 → A) (b H : A) (hB : 1 ≤ Bq b)
    (hc : (∀ q, |c0 ports q| ≤ H) ∧ (∀ q, |c1 ports q| ≤ H) ∧ (∀ q, |c2 ports q| ≤ H)) :
    |ker0 ports b| ≤ 6 * (H * Bq b ^ 1406) ∧ |ker1 ports b| ≤ 36 * (H * Bq b ^ 1726) ∧
      Bq b ^ 1636 - 38 * (H * Bq b ^ 1635) ≤ ker2 ports b ∧
      ker2 ports b ≤ Bq b ^ 1636 + 38 * (H * Bq b ^ 1635) := by
  obtain ⟨h0, h1, h2⟩ := hc
  have k0 := abs_kernel_le pos0 (c0 ports) H (Bq b) hB 1406 h0 pos0_le
  have k1 := abs_kernel_le pos1 (c1 ports) H (Bq b) hB 1726 h1 pos1_le
  have k2 := abs_kernel_le (fun i : Fin 38 => pos2 i.castSucc) (fun i => c2 ports i.castSucc) H
    (Bq b) hB 1635 (fun i => h2 _) (fun i => pos2_top _ (Fin.castSucc_lt_last i).ne)
  push_cast at k0 k1 k2
  rw [abs_le] at k2
  refine ⟨k0, k1, ?_, ?_⟩ <;> rw [ker2_split] <;> linarith [k2.1, k2.2]

theorem pow_step (B : A) (hB : 1 ≤ B) (a c : ℕ) (h : a ≤ c) : B ^ a ≤ B ^ c :=
  pow_le_pow_right₀ hB h

/-- `x · Bᵃ ≤ Bᵃ⁺¹` from `x ≤ B`. -/
theorem mul_pow_le_succ (B x : A) (hB : 0 ≤ B) (hx : x ≤ B) (a : ℕ) : x * B ^ a ≤ B ^ (a + 1) := by
  rw [pow_succ']
  exact mul_le_mul_of_nonneg_right hx (pow_nonneg hB a)

/-- Core of the unconditional positivity, over plain variables. -/
theorem core_pos (B U X0 X1 X2 H : A) (hB32 : 32768 ≤ B) (hBH : 4096 * H ≤ B) (hH : 8 ≤ H)
    (k0 : |X0| ≤ 6 * (H * B ^ 1406)) (k1 : |X1| ≤ 36 * (H * B ^ 1726))
    (k2 : B ^ 1636 - 38 * (H * B ^ 1635) ≤ X2) (hU : B ^ 115 ≤ U) :
    0 < X0 + U * (X1 + U * X2) := by
  have hB1 : (1 : A) ≤ B := by linarith
  have hB0 : (0 : A) ≤ B := by linarith
  have hP : ∀ n, (0 : A) ≤ B ^ n := fun n => pow_nonneg hB0 n
  have hH0 : (0 : A) ≤ H := by linarith
  have e1 : 4096 * H * B ^ 1635 ≤ B ^ 1636 := mul_pow_le_succ B _ hB0 hBH 1635
  have e2 : 4096 * H * B ^ 1726 ≤ B ^ 1727 := mul_pow_le_succ B _ hB0 hBH 1726
  have e3 : 4096 * H * B ^ 1406 ≤ B ^ 1407 := mul_pow_le_succ B _ hB0 hBH 1406
  have hX2 : B ^ 1636 ≤ 2 * X2 := by linarith [hP 1636]
  have hX1 : -B ^ 1727 ≤ X1 := by linarith [neg_abs_le X1, hP 1727]
  have hX0 : -B ^ 1407 ≤ X0 := by linarith [neg_abs_le X0, hP 1407]
  have hU0 : 0 ≤ U := le_trans (hP 115) hU
  have f1 : B ^ 1751 ≤ 2 * (U * X2) := by
    have a1 : B ^ 115 * B ^ 1636 ≤ U * B ^ 1636 := mul_le_mul_of_nonneg_right hU (hP 1636)
    have a2 : U * B ^ 1636 ≤ U * (2 * X2) := mul_le_mul_of_nonneg_left hX2 hU0
    have a3 : B ^ 1751 = B ^ 115 * B ^ 1636 := by rw [← pow_add]
    linarith
  have f2 : 4 * B ^ 1727 ≤ B ^ 1751 := by
    have a1 : (4 : A) ≤ B ^ 24 :=
      le_trans (by linarith) (le_trans (le_of_eq (pow_one B).symm) (pow_step B hB1 1 24 (by norm_num)))
    have a2 := mul_le_mul_of_nonneg_right a1 (hP 1727)
    have a3 : B ^ 1751 = B ^ 24 * B ^ 1727 := by rw [← pow_add]
    linarith
  have f3 : B ^ 1751 ≤ 4 * (X1 + U * X2) := by linarith
  have hY0 : 0 ≤ X1 + U * X2 := by linarith [hP 1751]
  have f4 : B ^ 1866 ≤ 4 * (U * (X1 + U * X2)) := by
    have a1 : B ^ 115 * (X1 + U * X2) ≤ U * (X1 + U * X2) := mul_le_mul_of_nonneg_right hU hY0
    have a2 : B ^ 115 * B ^ 1751 ≤ B ^ 115 * (4 * (X1 + U * X2)) :=
      mul_le_mul_of_nonneg_left f3 (hP 115)
    have a3 : B ^ 1866 = B ^ 115 * B ^ 1751 := by rw [← pow_add]
    linarith
  have f5 : 8 * B ^ 1407 ≤ B ^ 1866 := by
    have a1 : (8 : A) ≤ B ^ 459 :=
      le_trans (by linarith) (le_trans (le_of_eq (pow_one B).symm) (pow_step B hB1 1 459 (by norm_num)))
    have a2 := mul_le_mul_of_nonneg_right a1 (hP 1407)
    have a3 : B ^ 1866 = B ^ 459 * B ^ 1407 := by rw [← pow_add]
    linarith
  have hpos : (0 : A) < B ^ 1866 := pow_pos (by linarith) _
  linarith

/-- Core of the soundness-range upper bound, over plain variables. -/
theorem core_le (B U X0 X1 X2 H b : A) (hb : 1 ≤ b) (hB32 : 32768 ≤ B) (hBH : 4096 * H ≤ B)
    (hH : 8 ≤ H) (k0 : |X0| ≤ 6 * (H * B ^ 1406)) (k1 : |X1| ≤ 36 * (H * B ^ 1726))
    (k2 : X2 ≤ B ^ 1636 + 38 * (H * B ^ 1635)) (hU0 : 0 ≤ U) (hU : U ≤ 35 * (b * B ^ 115)) :
    X0 + U * (X1 + U * X2) ≤ 2486 * ((b * b) * B ^ 1866) := by
  have hB1 : (1 : A) ≤ B := by linarith
  have hB0 : (0 : A) ≤ B := by linarith
  have hP : ∀ n, (0 : A) ≤ B ^ n := fun n => pow_nonneg hB0 n
  have hH0 : (0 : A) ≤ H := by linarith
  have e1 : 4096 * H * B ^ 1635 ≤ B ^ 1636 := mul_pow_le_succ B _ hB0 hBH 1635
  have e2 : 4096 * H * B ^ 1726 ≤ B ^ 1727 := mul_pow_le_succ B _ hB0 hBH 1726
  have e3 : 4096 * H * B ^ 1406 ≤ B ^ 1407 := mul_pow_le_succ B _ hB0 hBH 1406
  have hX2 : X2 ≤ 2 * B ^ 1636 := by linarith [hP 1636]
  have hX1 : X1 ≤ B ^ 1727 := by linarith [le_abs_self X1, hP 1727]
  have hX0 : X0 ≤ B ^ 1407 := by linarith [le_abs_self X0, hP 1407]
  have hb0 : (0 : A) ≤ b := by linarith
  have hbb : (1 : A) ≤ b * b := by nlinarith
  have hW0 : 0 ≤ b * B ^ 115 := mul_nonneg hb0 (hP 115)
  have g1 : U * U ≤ (35 * (b * B ^ 115)) * (35 * (b * B ^ 115)) :=
    mul_le_mul hU hU hU0 (by linarith)
  have hWW : (b * B ^ 115) * (b * B ^ 115) * B ^ 1636 = (b * b) * B ^ 1866 := by
    rw [show (1866 : ℕ) = 115 + 115 + 1636 by norm_num, pow_add, pow_add]; ring
  have g2 : U * (U * X2) ≤ 2450 * ((b * b) * B ^ 1866) := by
    have a1 : U * (U * X2) ≤ U * (U * (2 * B ^ 1636)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hX2 hU0) hU0
    have a2 : U * U * (2 * B ^ 1636) ≤
        (35 * (b * B ^ 115)) * (35 * (b * B ^ 115)) * (2 * B ^ 1636) :=
      mul_le_mul_of_nonneg_right g1 (by linarith [hP 1636])
    have a3 : U * (U * (2 * B ^ 1636)) = U * U * (2 * B ^ 1636) := by ring
    have a4 : (35 * (b * B ^ 115)) * (35 * (b * B ^ 115)) * (2 * B ^ 1636) =
        2450 * ((b * B ^ 115) * (b * B ^ 115) * B ^ 1636) := by ring
    linarith
  have g3 : U * X1 ≤ 35 * ((b * b) * B ^ 1866) := by
    have a0 : U * X1 ≤ U * B ^ 1727 := mul_le_mul_of_nonneg_left hX1 hU0
    have a1 : U * B ^ 1727 ≤ 35 * (b * B ^ 115) * B ^ 1727 :=
      mul_le_mul_of_nonneg_right hU (hP 1727)
    have a2 : (b * B ^ 115) * B ^ 1727 = b * B ^ 1842 := by
      rw [show (1842 : ℕ) = 115 + 1727 by norm_num, pow_add]; ring
    have a3 : b * B ^ 1842 ≤ b * B ^ 1866 :=
      mul_le_mul_of_nonneg_left (pow_step B hB1 _ _ (by norm_num)) hb0
    have a4 : b * B ^ 1866 ≤ (b * b) * B ^ 1866 :=
      mul_le_mul_of_nonneg_right (le_mul_of_one_le_left hb0 hb) (hP 1866)
    have a5 : 35 * (b * B ^ 115) * B ^ 1727 = 35 * ((b * B ^ 115) * B ^ 1727) := by ring
    linarith
  have g4 : X0 ≤ (b * b) * B ^ 1866 := by
    have a1 : B ^ 1407 ≤ B ^ 1866 := pow_step B hB1 _ _ (by norm_num)
    have a2 : B ^ 1866 ≤ (b * b) * B ^ 1866 := le_mul_of_one_le_left (hP 1866) hbb
    linarith
  have e : X0 + U * (X1 + U * X2) = X0 + U * X1 + U * (U * X2) := by ring
  rw [e]
  linarith

theorem scale_facts (b H : A) (hb : 1 ≤ b) (hH : 8 ≤ H) (hBb : 4096 * H * (b * b) ≤ Bq b) :
    32768 ≤ Bq b ∧ 4096 * H ≤ Bq b ∧ 4096 * (b * b) ≤ Bq b ∧ b ≤ b * b := by
  have hb0 : (0 : A) ≤ b := by linarith
  have hbb : b ≤ b * b := le_mul_of_one_le_left hb0 hb
  have h1 : (1 : A) ≤ b * b := le_trans hb hbb
  have hH0 : (0 : A) ≤ H := by linarith
  have a1 : 4096 * H ≤ 4096 * H * (b * b) := le_mul_of_one_le_right (by linarith) h1
  have a2 : 4096 * (b * b) ≤ 4096 * H * (b * b) := by
    have := mul_le_mul_of_nonneg_right (show (4096 : A) ≤ 4096 * H by linarith) (by linarith : (0:A) ≤ b * b)
    linarith
  refine ⟨by linarith, by linarith, by linarith, hbb⟩

/-- **Unconditional positivity** of `G*` (given `U* ≥ B¹¹⁵`). -/
theorem Gs_pos (ports : Fin 4 → A) (b g H : A) (hb : 1 ≤ b) (hH : 8 ≤ H)
    (hBb : 4096 * H * (b * b) ≤ Bq b)
    (hc : (∀ q, |c0 ports q| ≤ H) ∧ (∀ q, |c1 ports q| ≤ H) ∧ (∀ q, |c2 ports q| ≤ H))
    (hU : Bq b ^ 115 ≤ Ust b g) : 0 < Gs ports b g := by
  obtain ⟨hB32, hBH, -, -⟩ := scale_facts b H hb hH hBb
  obtain ⟨k0, k1, k2, -⟩ := ker_bounds ports b H (by linarith) hc
  exact core_pos (Bq b) (Ust b g) _ _ _ H hB32 hBH hH k0 k1 k2 hU

/-- **The soundness-range upper bound** on `G*`. -/
theorem Gs_le (ports : Fin 4 → A) (b g H : A) (hb : 1 ≤ b) (hH : 8 ≤ H)
    (hBb : 4096 * H * (b * b) ≤ Bq b)
    (hc : (∀ q, |c0 ports q| ≤ H) ∧ (∀ q, |c1 ports q| ≤ H) ∧ (∀ q, |c2 ports q| ≤ H))
    (hU0 : 0 ≤ Ust b g) (hU : Ust b g ≤ 35 * (b * Bq b ^ 115)) :
    Gs ports b g ≤ 2486 * ((b * b) * Bq b ^ 1866) := by
  obtain ⟨hB32, hBH, -, -⟩ := scale_facts b H hb hH hBb
  obtain ⟨k0, k1, -, k2⟩ := ker_bounds ports b H (by linarith) hc
  exact core_le (Bq b) (Ust b g) _ _ _ H b hb hB32 hBH hH k0 k1 k2 hU0 hU

/-- **The coefficient bound** `4|c| + 4 ≤ B` for weights `0 ≤ uᵢ ≤ b`. -/
theorem coeff_bound (ports : Fin 4 → A) (b H : A) (hb : 1 ≤ b) (hH : 8 ≤ H)
    (hBb : 4096 * H * (b * b) ≤ Bq b)
    (hc : (∀ q, |c0 ports q| ≤ H) ∧ (∀ q, |c1 ports q| ≤ H) ∧ (∀ q, |c2 ports q| ≤ H))
    (u : Fin 31 → A) (hu0 : ∀ i, 0 ≤ u i) (hub : ∀ i, u i ≤ b) (e : ℕ) :
    4 * |(sourcePoly ports u).coeff e| + 4 ≤ Bq b := by
  obtain ⟨h0, h1, h2⟩ := hc
  obtain ⟨-, -, -, hbb'⟩ := scale_facts b H hb hH hBb
  have hH0 : (0 : A) ≤ H := by linarith
  have hb0 : (0 : A) ≤ b := by linarith
  have q2 := abs_coeff_quad_le weights u hu0 pos2 pos2_injective (c2 ports) H hH0 h2 e
  have q1 := abs_coeff_lin_le weights u hu0 pos1 pos1_injective (c1 ports) H hH0 h1 e
  have q0 := abs_coeff_const_le pos0 pos0_injective (c0 ports) H hH0 h0 e
  have hs : ∑ i, u i ≤ 31 * b := by
    calc ∑ i, u i ≤ ∑ _i : Fin 31, b := Finset.sum_le_sum (fun i _ => hub i)
      _ = 31 * b := by simp
  have hs0 : 0 ≤ ∑ i, u i := Finset.sum_nonneg (fun i _ => hu0 i)
  have hss : (∑ i, u i) ^ 2 ≤ (31 * b) ^ 2 := pow_le_pow_left₀ hs0 hs 2
  have habs : |(sourcePoly ports u).coeff e| ≤ H * (∑ i, u i) ^ 2 + H * ∑ i, u i + H := by
    rw [sourcePoly, coeff_add, coeff_add]
    have a1 := abs_add_le ((wordPoly weights u ^ 2 * kernelPoly pos2 (c2 ports)).coeff e +
      (wordPoly weights u * kernelPoly pos1 (c1 ports)).coeff e) ((kernelPoly pos0 (c0 ports)).coeff e)
    have a2 := abs_add_le ((wordPoly weights u ^ 2 * kernelPoly pos2 (c2 ports)).coeff e)
      ((wordPoly weights u * kernelPoly pos1 (c1 ports)).coeff e)
    linarith
  have hbb : (1 : A) ≤ b * b := le_trans hb hbb'
  have t1 : H * (∑ i, u i) ^ 2 ≤ H * (31 * b) ^ 2 := mul_le_mul_of_nonneg_left hss hH0
  have t2 : H * ∑ i, u i ≤ H * (31 * (b * b)) :=
    mul_le_mul_of_nonneg_left (le_trans hs (by linarith)) hH0
  have t3 : H ≤ H * (b * b) := le_mul_of_one_le_right hH0 hbb
  have t5 : H * (31 * b) ^ 2 = 961 * (H * (b * b)) := by ring
  linarith

/-- **The soundness range**: `S* + T_c < L`, `g < N₀` and `M₀ < N₀`. -/
theorem sum_lt_L (ports : Fin 4 → A) (b g H : A) (hb : 1 ≤ b) (hH : 8 ≤ H)
    (hBb : 4096 * H * (b * b) ≤ Bq b)
    (hc : (∀ q, |c0 ports q| ≤ H) ∧ (∀ q, |c1 ports q| ≤ H) ∧ (∀ q, |c2 ports q| ≤ H))
    (hg0 : 0 ≤ g) (hg : g < 4 * tq b) :
    Scq ports b g + Tcq b < Lq b ∧ g < N0 b ∧ maskq b < N0 b := by
  obtain ⟨hB32, hBH, hBb', hbb'⟩ := scale_facts b H hb hH hBb
  have hB1 : (1 : A) ≤ Bq b := by linarith
  have hB0 : (0 : A) ≤ Bq b := by linarith
  have hb0 : (0 : A) ≤ b := by linarith
  have hbb : (1 : A) ≤ b * b := le_trans hb hbb'
  have hl := ell_le b hB1
  have hl0 := ell_nonneg b hB0
  have hT := Tst_le b hB1
  have hT0 := Tst_nonneg b hB0
  have hP : ∀ n, (0 : A) ≤ Bq b ^ n := fun n => pow_nonneg hB0 n
  have h4b : 4 * b ≤ Bq b := by linarith
  have hN0 : N0 b = Bq b * Bq b ^ 115 := by rw [N0, ← pow_succ']
  have e4 : 4 * tq b = 4 * b * Bq b ^ 115 := by rw [tq]; ring
  have hgN : g < N0 b := by
    rw [hN0]
    have := mul_le_mul_of_nonneg_right h4b (hP 115)
    linarith
  have hm : maskq b < N0 b := by
    rw [maskq]
    have := mul_nonneg hl0 (sub_nonneg.2 hb)
    linarith
  have hU0 : 0 ≤ Ust b g := by rw [Ust]; linarith
  have hU : Ust b g ≤ 35 * (b * Bq b ^ 115) := by
    rw [Ust]
    have := le_mul_of_one_le_left (hP 115) hb
    linarith
  have hG := Gs_le ports b g H hb hH hBb hc hU0 hU
  have k1 : Bq b ^ 1867 = Bq b * Bq b ^ 1866 := by rw [← pow_succ']
  have k2 : Bq b ^ 1835 ≤ (b * b) * Bq b ^ 1866 :=
    le_trans (pow_step _ hB1 _ _ (by norm_num)) (le_mul_of_one_le_left (hP 1866) hbb)
  have k3 : Tst b * (Bq b - 1) ≤ 22 * Bq b ^ 1835 := by
    have a1 := mul_le_mul_of_nonneg_right hT (by linarith : (0 : A) ≤ Bq b - 1)
    have a2 : (22 : A) * Bq b ^ 1834 * (Bq b - 1) ≤ 22 * Bq b ^ 1834 * Bq b := by
      have := hP 1834; linarith
    have a3 : (22 : A) * Bq b ^ 1835 = 22 * Bq b ^ 1834 * Bq b := by rw [pow_succ]; ring
    linarith
  have k4 : (1 : A) ≤ (b * b) * Bq b ^ 1866 :=
    le_trans hbb (le_mul_of_one_le_right (by linarith) (one_le_pow₀ hB1))
  have hB8 : 32768 * (b * b) ≤ Bq b := by
    have := mul_le_mul_of_nonneg_right (show (4096 : A) * 8 ≤ 4096 * H by linarith)
      (le_trans zero_le_one hbb)
    linarith
  have k5 : 32768 * ((b * b) * Bq b ^ 1866) ≤ Bq b ^ 1867 := by
    rw [k1]
    have := mul_le_mul_of_nonneg_right hB8 (hP 1866)
    linarith
  have hX : 2 + Tst b * (Bq b - 1) + 2 * Gs ports b g < Bq b ^ 1867 := by linarith
  have hL : Lq b = 2 * b * (N0 b * Bq b ^ 1867) := by
    rw [Lq, N0, ← pow_add]
  have hNpos : 0 < N0 b := pow_pos (by linarith) _
  have a1 : N0 b * (2 + Tst b * (Bq b - 1) + 2 * Gs ports b g) < N0 b * Bq b ^ 1867 :=
    mul_lt_mul_of_pos_left hX hNpos
  have a2 : N0 b * Bq b ^ 1867 ≤ 2 * b * (N0 b * Bq b ^ 1867) := by
    have h0 : 0 ≤ N0 b * Bq b ^ 1867 := mul_nonneg hNpos.le (hP 1867)
    have : (1 : A) ≤ 2 * b := by linarith
    exact le_mul_of_one_le_left h0 this
  refine ⟨?_, hgN, hm⟩
  rw [hL, Scq, Tcq]
  have e : g + N0 b * (Tst b + 2 * Gs ports b g) + (maskq b + N0 b * (Tst b * (Bq b - 2))) =
      g + maskq b + N0 b * (Tst b * (Bq b - 1) + 2 * Gs ports b g) := by ring
  rw [e]
  linarith

end Order

end Nine121.N101Prefix
