import DiophantineConsistency.Nine121.N105Layout
import DiophantineConsistency.Nine121.N101Prefix

/-! # Package 105's H1868 prefix: definitions and the generic size estimates

The prefix of `105-bootstrap-certificates/nine/PROOF.md` (§2) for the H1868 layout of
`N105Layout`, in an arbitrary commutative ring:

  `B = 2^2134939 b²`, `ℓ = Σᵢ B^{wᵢ}`, `T* = Σₖ B^{qₖ}`, `U* = g + ℓ`,
  `G* = K₀(B) + U*(K₁(B) + U* K₂(B))`, `N₀ = B¹¹⁷`, `M₀ = N₀ − 1 − ℓ(b − 1)`,
  `T_c = M₀ + N₀ T*(B − 2)`, `S* = g + N₀(T* + 2G*)`, `L = 2bB¹⁹⁸⁶`,
  `R = L(1 + (T_c + S*)) − S* − 1`, `N = 2^16012032 B¹⁰⁵⁵`, `t = bB¹¹⁶`.

The base `Bq` and the two irreducible scales are package 101's (`N101Prefix.Bq`, `baseScale`,
`thresholdScale`); the kernel coefficients are 101's (`N101Layout.c0/c1/c2`, bounded by
`N101Prefix.c_bounds`). Only the positions and the exponents change, by the shift of
`N105Layout`: `W = 116`, `H = 1868`, largest target `1836`.

In a linearly ordered ring, with an abstract bound `H` on every kernel coefficient and
`4096 H b² ≤ B`, `8 ≤ H`, `1 ≤ b`:

* `Gs_pos`: `G* > 0` as soon as `U* ≥ B¹¹⁶` (unconditional positivity of the prefix);
* `Gs_le`: on the soundness range `U* ≤ 35 b B¹¹⁶`, `G* ≤ 2486 b² B¹⁸⁶⁸`;
* `coeff_bound`: every coefficient `c` of `N105Layout.sourcePoly` at weights `0 ≤ uᵢ ≤ b` has
  `4|c| + 4 ≤ B`;
* `sum_lt_L`: on the soundness range, `S* + T_c < L`, `g < N₀`, `M₀ < N₀`. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace Nine121.N105Prefix
open Polynomial SparseExtraction N105Layout
open N101Prefix (Bq baseScale thresholdScale abs_kernel_le pow_step mul_pow_le_succ scale_facts
  sum_range_table)

section Ring
variable {A : Type*} [CommRing A]

def ell (b : A) : A := ∑ i, Bq b ^ weights i
def Tst (b : A) : A := ∑ k, Bq b ^ targets k
def ker0 (ports : Fin 4 → A) (b : A) : A := ∑ p, N101Layout.c0 ports p * Bq b ^ pos0 p
def ker1 (ports : Fin 4 → A) (b : A) : A := ∑ p, N101Layout.c1 ports p * Bq b ^ pos1 p
def ker2 (ports : Fin 4 → A) (b : A) : A := ∑ p, N101Layout.c2 ports p * Bq b ^ pos2 p
def Ust (b g : A) : A := g + ell b
def Gs (ports : Fin 4 → A) (b g : A) : A :=
  ker0 ports b + Ust b g * (ker1 ports b + Ust b g * ker2 ports b)
def N0 (b : A) : A := Bq b ^ 117
def maskq (b : A) : A := N0 b - 1 - ell b * (b - 1)
def Tcq (b : A) : A := maskq b + N0 b * (Tst b * (Bq b - 2))
def Scq (ports : Fin 4 → A) (b g : A) : A := g + N0 b * (Tst b + 2 * Gs ports b g)
def Lq (b : A) : A := 2 * b * Bq b ^ 1986
def Rq (ports : Fin 4 → A) (b g : A) : A :=
  Lq b * (1 + (Tcq b + Scq ports b g)) - Scq ports b g - 1
def Nq (b : A) : A := (thresholdScale : A) * Bq b ^ 1055
def tq (b : A) : A := b * Bq b ^ 116

theorem Gs_eval (ports : Fin 4 → A) (b g : A) (u : Fin 31 → A)
    (hu : Ust b g = ∑ i, u i * Bq b ^ weights i) :
    Gs ports b g = (sourcePoly ports u).eval (Bq b) := by
  simp only [sourcePoly, eval_add, eval_mul, eval_pow, eval_wordPoly, eval_kernelPoly]
  rw [← hu, Gs, ker0, ker1, ker2]
  ring

theorem natDegree_sourcePoly (ports : Fin 4 → A) (u : Fin 31 → A) :
    (sourcePoly ports u).natDegree ≤ 1868 := by
  have hw : (wordPoly weights u).natDegree ≤ 116 :=
    natDegree_sum_le_of_forall_le _ _ (fun i _ => (natDegree_monomial_le _).trans (weights_le i))
  have h2 : (kernelPoly pos2 (N101Layout.c2 ports)).natDegree ≤ 1636 :=
    natDegree_sum_le_of_forall_le _ _ (fun p _ => (natDegree_monomial_le _).trans (pos2_le p))
  have h1 : (kernelPoly pos1 (N101Layout.c1 ports)).natDegree ≤ 1727 :=
    natDegree_sum_le_of_forall_le _ _ (fun p _ => (natDegree_monomial_le _).trans (pos1_le p))
  have h0 : (kernelPoly pos0 (N101Layout.c0 ports)).natDegree ≤ 1408 :=
    natDegree_sum_le_of_forall_le _ _ (fun p _ => (natDegree_monomial_le _).trans (pos0_le p))
  have hq : (wordPoly weights u ^ 2 * kernelPoly pos2 (N101Layout.c2 ports)).natDegree ≤ 1868 :=
    (natDegree_mul_le_of_le (natDegree_pow_le_of_le 2 hw) h2).trans (by norm_num)
  have hl : (wordPoly weights u * kernelPoly pos1 (N101Layout.c1 ports)).natDegree ≤ 1868 :=
    (natDegree_mul_le_of_le hw h1).trans (by norm_num)
  exact natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le hq hl) (h0.trans (by norm_num))

/-- The range-sum form of `G*`. -/
theorem Gs_sum (ports : Fin 4 → A) (b g : A) (u : Fin 31 → A)
    (hu : Ust b g = ∑ i, u i * Bq b ^ weights i) :
    Gs ports b g = ∑ e ∈ Finset.range 1869, (sourcePoly ports u).coeff e * Bq b ^ e := by
  rw [Gs_eval ports b g u hu, eval_eq_sum_range' (n := 1869) (lt_of_le_of_lt (natDegree_sourcePoly ports u)
    (by norm_num))]

/-- `ker2 = rest + B¹⁶³⁶`, the leading record split off. -/
theorem ker2_split (ports : Fin 4 → A) (b : A) :
    ker2 ports b = (∑ i : Fin 38, N101Layout.c2 ports i.castSucc * Bq b ^ pos2 i.castSucc) +
      Bq b ^ 1636 := by
  rw [ker2, Fin.sum_univ_castSucc, show (Fin.last 38 : Fin 39) = ⟨38, by decide⟩ from rfl,
    N101Layout.c2_last, pos2_last, one_mul]

end Ring

section Order
variable {A : Type*} [CommRing A] [LinearOrder A] [IsStrictOrderedRing A]

theorem ell_ge (b : A) (hB : 0 ≤ Bq b) : Bq b ^ 116 ≤ ell b := by
  have h := Finset.single_le_sum (f := fun i : Fin 31 => Bq b ^ weights i)
    (fun i _ => pow_nonneg hB _) (Finset.mem_univ (20 : Fin 31))
  have e : weights 20 = 116 := rfl
  simp only [e] at h
  exact h

theorem ell_nonneg (b : A) (hB : 0 ≤ Bq b) : 0 ≤ ell b :=
  Finset.sum_nonneg (fun i _ => pow_nonneg hB _)

theorem ell_le (b : A) (hB : 1 ≤ Bq b) : ell b ≤ 31 * Bq b ^ 116 := by
  calc ell b = ∑ i, Bq b ^ weights i := rfl
    _ ≤ ∑ _i : Fin 31, Bq b ^ 116 :=
        Finset.sum_le_sum (fun i _ => pow_le_pow_right₀ hB (weights_le i))
    _ = 31 * Bq b ^ 116 := by simp

theorem Tst_le (b : A) (hB : 1 ≤ Bq b) : Tst b ≤ 22 * Bq b ^ 1836 := by
  calc Tst b = ∑ k, Bq b ^ targets k := rfl
    _ ≤ ∑ _k : Fin 22, Bq b ^ 1836 :=
        Finset.sum_le_sum (fun k _ => pow_le_pow_right₀ hB (targets_le k))
    _ = 22 * Bq b ^ 1836 := by simp

theorem Tst_nonneg (b : A) (hB : 0 ≤ Bq b) : 0 ≤ Tst b :=
  Finset.sum_nonneg (fun k _ => pow_nonneg hB _)

/-- The three kernel estimates. -/
theorem ker_bounds (ports : Fin 4 → A) (b H : A) (hB : 1 ≤ Bq b)
    (hc : (∀ q, |N101Layout.c0 ports q| ≤ H) ∧ (∀ q, |N101Layout.c1 ports q| ≤ H) ∧
      (∀ q, |N101Layout.c2 ports q| ≤ H)) :
    |ker0 ports b| ≤ 6 * (H * Bq b ^ 1408) ∧ |ker1 ports b| ≤ 36 * (H * Bq b ^ 1727) ∧
      Bq b ^ 1636 - 38 * (H * Bq b ^ 1635) ≤ ker2 ports b ∧
      ker2 ports b ≤ Bq b ^ 1636 + 38 * (H * Bq b ^ 1635) := by
  obtain ⟨h0, h1, h2⟩ := hc
  have k0 := abs_kernel_le pos0 (N101Layout.c0 ports) H (Bq b) hB 1408 h0 pos0_le
  have k1 := abs_kernel_le pos1 (N101Layout.c1 ports) H (Bq b) hB 1727 h1 pos1_le
  have k2 := abs_kernel_le (fun i : Fin 38 => pos2 i.castSucc) (fun i => N101Layout.c2 ports i.castSucc) H
    (Bq b) hB 1635 (fun i => h2 _) (fun i => pos2_top _ (Fin.castSucc_lt_last i).ne)
  push_cast at k0 k1 k2
  rw [abs_le] at k2
  refine ⟨k0, k1, ?_, ?_⟩ <;> rw [ker2_split] <;> linarith [k2.1, k2.2]

/-- Core of the unconditional positivity, over plain variables. -/
theorem core_pos (B U X0 X1 X2 H : A) (hB32 : 32768 ≤ B) (hBH : 4096 * H ≤ B) (hH : 8 ≤ H)
    (k0 : |X0| ≤ 6 * (H * B ^ 1408)) (k1 : |X1| ≤ 36 * (H * B ^ 1727))
    (k2 : B ^ 1636 - 38 * (H * B ^ 1635) ≤ X2) (hU : B ^ 116 ≤ U) :
    0 < X0 + U * (X1 + U * X2) := by
  have hB1 : (1 : A) ≤ B := by linarith
  have hB0 : (0 : A) ≤ B := by linarith
  have hP : ∀ n, (0 : A) ≤ B ^ n := fun n => pow_nonneg hB0 n
  have hH0 : (0 : A) ≤ H := by linarith
  have e1 : 4096 * H * B ^ 1635 ≤ B ^ 1636 := mul_pow_le_succ B _ hB0 hBH 1635
  have e2 : 4096 * H * B ^ 1727 ≤ B ^ 1728 := mul_pow_le_succ B _ hB0 hBH 1727
  have e3 : 4096 * H * B ^ 1408 ≤ B ^ 1409 := mul_pow_le_succ B _ hB0 hBH 1408
  have hX2 : B ^ 1636 ≤ 2 * X2 := by linarith [hP 1636]
  have hX1 : -B ^ 1728 ≤ X1 := by linarith [neg_abs_le X1, hP 1728]
  have hX0 : -B ^ 1409 ≤ X0 := by linarith [neg_abs_le X0, hP 1409]
  have hU0 : 0 ≤ U := le_trans (hP 116) hU
  have f1 : B ^ 1752 ≤ 2 * (U * X2) := by
    have a1 : B ^ 116 * B ^ 1636 ≤ U * B ^ 1636 := mul_le_mul_of_nonneg_right hU (hP 1636)
    have a2 : U * B ^ 1636 ≤ U * (2 * X2) := mul_le_mul_of_nonneg_left hX2 hU0
    have a3 : B ^ 1752 = B ^ 116 * B ^ 1636 := by rw [← pow_add]
    linarith
  have f2 : 4 * B ^ 1728 ≤ B ^ 1752 := by
    have a1 : (4 : A) ≤ B ^ 24 :=
      le_trans (by linarith) (le_trans (le_of_eq (pow_one B).symm) (pow_step B hB1 1 24 (by norm_num)))
    have a2 := mul_le_mul_of_nonneg_right a1 (hP 1728)
    have a3 : B ^ 1752 = B ^ 24 * B ^ 1728 := by rw [← pow_add]
    linarith
  have f3 : B ^ 1752 ≤ 4 * (X1 + U * X2) := by linarith
  have hY0 : 0 ≤ X1 + U * X2 := by linarith [hP 1752]
  have f4 : B ^ 1868 ≤ 4 * (U * (X1 + U * X2)) := by
    have a1 : B ^ 116 * (X1 + U * X2) ≤ U * (X1 + U * X2) := mul_le_mul_of_nonneg_right hU hY0
    have a2 : B ^ 116 * B ^ 1752 ≤ B ^ 116 * (4 * (X1 + U * X2)) :=
      mul_le_mul_of_nonneg_left f3 (hP 116)
    have a3 : B ^ 1868 = B ^ 116 * B ^ 1752 := by rw [← pow_add]
    linarith
  have f5 : 8 * B ^ 1409 ≤ B ^ 1868 := by
    have a1 : (8 : A) ≤ B ^ 459 :=
      le_trans (by linarith) (le_trans (le_of_eq (pow_one B).symm) (pow_step B hB1 1 459 (by norm_num)))
    have a2 := mul_le_mul_of_nonneg_right a1 (hP 1409)
    have a3 : B ^ 1868 = B ^ 459 * B ^ 1409 := by rw [← pow_add]
    linarith
  have hpos : (0 : A) < B ^ 1868 := pow_pos (by linarith) _
  linarith

/-- Core of the soundness-range upper bound, over plain variables. -/
theorem core_le (B U X0 X1 X2 H b : A) (hb : 1 ≤ b) (hB32 : 32768 ≤ B) (hBH : 4096 * H ≤ B)
    (hH : 8 ≤ H) (k0 : |X0| ≤ 6 * (H * B ^ 1408)) (k1 : |X1| ≤ 36 * (H * B ^ 1727))
    (k2 : X2 ≤ B ^ 1636 + 38 * (H * B ^ 1635)) (hU0 : 0 ≤ U) (hU : U ≤ 35 * (b * B ^ 116)) :
    X0 + U * (X1 + U * X2) ≤ 2486 * ((b * b) * B ^ 1868) := by
  have hB1 : (1 : A) ≤ B := by linarith
  have hB0 : (0 : A) ≤ B := by linarith
  have hP : ∀ n, (0 : A) ≤ B ^ n := fun n => pow_nonneg hB0 n
  have hH0 : (0 : A) ≤ H := by linarith
  have e1 : 4096 * H * B ^ 1635 ≤ B ^ 1636 := mul_pow_le_succ B _ hB0 hBH 1635
  have e2 : 4096 * H * B ^ 1727 ≤ B ^ 1728 := mul_pow_le_succ B _ hB0 hBH 1727
  have e3 : 4096 * H * B ^ 1408 ≤ B ^ 1409 := mul_pow_le_succ B _ hB0 hBH 1408
  have hX2 : X2 ≤ 2 * B ^ 1636 := by linarith [hP 1636]
  have hX1 : X1 ≤ B ^ 1728 := by linarith [le_abs_self X1, hP 1728]
  have hX0 : X0 ≤ B ^ 1409 := by linarith [le_abs_self X0, hP 1409]
  have hb0 : (0 : A) ≤ b := by linarith
  have hbb : (1 : A) ≤ b * b := by nlinarith
  have hW0 : 0 ≤ b * B ^ 116 := mul_nonneg hb0 (hP 116)
  have g1 : U * U ≤ (35 * (b * B ^ 116)) * (35 * (b * B ^ 116)) :=
    mul_le_mul hU hU hU0 (by linarith)
  have hWW : (b * B ^ 116) * (b * B ^ 116) * B ^ 1636 = (b * b) * B ^ 1868 := by
    rw [show (1868 : ℕ) = 116 + 116 + 1636 by norm_num, pow_add, pow_add]; ring
  have g2 : U * (U * X2) ≤ 2450 * ((b * b) * B ^ 1868) := by
    have a1 : U * (U * X2) ≤ U * (U * (2 * B ^ 1636)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hX2 hU0) hU0
    have a2 : U * U * (2 * B ^ 1636) ≤
        (35 * (b * B ^ 116)) * (35 * (b * B ^ 116)) * (2 * B ^ 1636) :=
      mul_le_mul_of_nonneg_right g1 (by linarith [hP 1636])
    have a3 : U * (U * (2 * B ^ 1636)) = U * U * (2 * B ^ 1636) := by ring
    have a4 : (35 * (b * B ^ 116)) * (35 * (b * B ^ 116)) * (2 * B ^ 1636) =
        2450 * ((b * B ^ 116) * (b * B ^ 116) * B ^ 1636) := by ring
    linarith
  have g3 : U * X1 ≤ 35 * ((b * b) * B ^ 1868) := by
    have a0 : U * X1 ≤ U * B ^ 1728 := mul_le_mul_of_nonneg_left hX1 hU0
    have a1 : U * B ^ 1728 ≤ 35 * (b * B ^ 116) * B ^ 1728 :=
      mul_le_mul_of_nonneg_right hU (hP 1728)
    have a2 : (b * B ^ 116) * B ^ 1728 = b * B ^ 1844 := by
      rw [show (1844 : ℕ) = 116 + 1728 by norm_num, pow_add]; ring
    have a3 : b * B ^ 1844 ≤ b * B ^ 1868 :=
      mul_le_mul_of_nonneg_left (pow_step B hB1 _ _ (by norm_num)) hb0
    have a4 : b * B ^ 1868 ≤ (b * b) * B ^ 1868 :=
      mul_le_mul_of_nonneg_right (le_mul_of_one_le_left hb0 hb) (hP 1868)
    have a5 : 35 * (b * B ^ 116) * B ^ 1728 = 35 * ((b * B ^ 116) * B ^ 1728) := by ring
    linarith
  have g4 : X0 ≤ (b * b) * B ^ 1868 := by
    have a1 : B ^ 1409 ≤ B ^ 1868 := pow_step B hB1 _ _ (by norm_num)
    have a2 : B ^ 1868 ≤ (b * b) * B ^ 1868 := le_mul_of_one_le_left (hP 1868) hbb
    linarith
  have e : X0 + U * (X1 + U * X2) = X0 + U * X1 + U * (U * X2) := by ring
  rw [e]
  linarith

/-- **Unconditional positivity** of `G*` (given `U* ≥ B¹¹⁶`). -/
theorem Gs_pos (ports : Fin 4 → A) (b g H : A) (hb : 1 ≤ b) (hH : 8 ≤ H)
    (hBb : 4096 * H * (b * b) ≤ Bq b)
    (hc : (∀ q, |N101Layout.c0 ports q| ≤ H) ∧ (∀ q, |N101Layout.c1 ports q| ≤ H) ∧
      (∀ q, |N101Layout.c2 ports q| ≤ H))
    (hU : Bq b ^ 116 ≤ Ust b g) : 0 < Gs ports b g := by
  obtain ⟨hB32, hBH, -, -⟩ := scale_facts b H hb hH hBb
  obtain ⟨k0, k1, k2, -⟩ := ker_bounds ports b H (by linarith) hc
  exact core_pos (Bq b) (Ust b g) _ _ _ H hB32 hBH hH k0 k1 k2 hU

/-- **The soundness-range upper bound** on `G*`. -/
theorem Gs_le (ports : Fin 4 → A) (b g H : A) (hb : 1 ≤ b) (hH : 8 ≤ H)
    (hBb : 4096 * H * (b * b) ≤ Bq b)
    (hc : (∀ q, |N101Layout.c0 ports q| ≤ H) ∧ (∀ q, |N101Layout.c1 ports q| ≤ H) ∧
      (∀ q, |N101Layout.c2 ports q| ≤ H))
    (hU0 : 0 ≤ Ust b g) (hU : Ust b g ≤ 35 * (b * Bq b ^ 116)) :
    Gs ports b g ≤ 2486 * ((b * b) * Bq b ^ 1868) := by
  obtain ⟨hB32, hBH, -, -⟩ := scale_facts b H hb hH hBb
  obtain ⟨k0, k1, -, k2⟩ := ker_bounds ports b H (by linarith) hc
  exact core_le (Bq b) (Ust b g) _ _ _ H b hb hB32 hBH hH k0 k1 k2 hU0 hU

/-- **The coefficient bound** `4|c| + 4 ≤ B` for weights `0 ≤ uᵢ ≤ b`. -/
theorem coeff_bound (ports : Fin 4 → A) (b H : A) (hb : 1 ≤ b) (hH : 8 ≤ H)
    (hBb : 4096 * H * (b * b) ≤ Bq b)
    (hc : (∀ q, |N101Layout.c0 ports q| ≤ H) ∧ (∀ q, |N101Layout.c1 ports q| ≤ H) ∧
      (∀ q, |N101Layout.c2 ports q| ≤ H))
    (u : Fin 31 → A) (hu0 : ∀ i, 0 ≤ u i) (hub : ∀ i, u i ≤ b) (e : ℕ) :
    4 * |(sourcePoly ports u).coeff e| + 4 ≤ Bq b := by
  obtain ⟨h0, h1, h2⟩ := hc
  obtain ⟨-, -, -, hbb'⟩ := scale_facts b H hb hH hBb
  have hH0 : (0 : A) ≤ H := by linarith
  have hb0 : (0 : A) ≤ b := by linarith
  have q2 := abs_coeff_quad_le weights u hu0 pos2 pos2_injective (N101Layout.c2 ports) H hH0 h2 e
  have q1 := abs_coeff_lin_le weights u hu0 pos1 pos1_injective (N101Layout.c1 ports) H hH0 h1 e
  have q0 := abs_coeff_const_le pos0 pos0_injective (N101Layout.c0 ports) H hH0 h0 e
  have hs : ∑ i, u i ≤ 31 * b := by
    calc ∑ i, u i ≤ ∑ _i : Fin 31, b := Finset.sum_le_sum (fun i _ => hub i)
      _ = 31 * b := by simp
  have hs0 : 0 ≤ ∑ i, u i := Finset.sum_nonneg (fun i _ => hu0 i)
  have hss : (∑ i, u i) ^ 2 ≤ (31 * b) ^ 2 := pow_le_pow_left₀ hs0 hs 2
  have habs : |(sourcePoly ports u).coeff e| ≤ H * (∑ i, u i) ^ 2 + H * ∑ i, u i + H := by
    rw [sourcePoly, coeff_add, coeff_add]
    have a1 := abs_add_le ((wordPoly weights u ^ 2 * kernelPoly pos2 (N101Layout.c2 ports)).coeff e +
      (wordPoly weights u * kernelPoly pos1 (N101Layout.c1 ports)).coeff e)
      ((kernelPoly pos0 (N101Layout.c0 ports)).coeff e)
    have a2 := abs_add_le ((wordPoly weights u ^ 2 * kernelPoly pos2 (N101Layout.c2 ports)).coeff e)
      ((wordPoly weights u * kernelPoly pos1 (N101Layout.c1 ports)).coeff e)
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
    (hc : (∀ q, |N101Layout.c0 ports q| ≤ H) ∧ (∀ q, |N101Layout.c1 ports q| ≤ H) ∧
      (∀ q, |N101Layout.c2 ports q| ≤ H))
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
  have hN0 : N0 b = Bq b * Bq b ^ 116 := by rw [N0, ← pow_succ']
  have e4 : 4 * tq b = 4 * b * Bq b ^ 116 := by rw [tq]; ring
  have hgN : g < N0 b := by
    rw [hN0]
    have := mul_le_mul_of_nonneg_right h4b (hP 116)
    linarith
  have hm : maskq b < N0 b := by
    rw [maskq]
    have := mul_nonneg hl0 (sub_nonneg.2 hb)
    linarith
  have hU0 : 0 ≤ Ust b g := by rw [Ust]; linarith
  have hU : Ust b g ≤ 35 * (b * Bq b ^ 116) := by
    rw [Ust]
    have := le_mul_of_one_le_left (hP 116) hb
    linarith
  have hG := Gs_le ports b g H hb hH hBb hc hU0 hU
  have k1 : Bq b ^ 1869 = Bq b * Bq b ^ 1868 := by rw [← pow_succ']
  have k2 : Bq b ^ 1837 ≤ (b * b) * Bq b ^ 1868 :=
    le_trans (pow_step _ hB1 _ _ (by norm_num)) (le_mul_of_one_le_left (hP 1868) hbb)
  have k3 : Tst b * (Bq b - 1) ≤ 22 * Bq b ^ 1837 := by
    have a1 := mul_le_mul_of_nonneg_right hT (by linarith : (0 : A) ≤ Bq b - 1)
    have a2 : (22 : A) * Bq b ^ 1836 * (Bq b - 1) ≤ 22 * Bq b ^ 1836 * Bq b := by
      have := hP 1836; linarith
    have a3 : (22 : A) * Bq b ^ 1837 = 22 * Bq b ^ 1836 * Bq b := by rw [pow_succ]; ring
    linarith
  have k4 : (1 : A) ≤ (b * b) * Bq b ^ 1868 :=
    le_trans hbb (le_mul_of_one_le_right (by linarith) (one_le_pow₀ hB1))
  have hB8 : 32768 * (b * b) ≤ Bq b := by
    have := mul_le_mul_of_nonneg_right (show (4096 : A) * 8 ≤ 4096 * H by linarith)
      (le_trans zero_le_one hbb)
    linarith
  have k5 : 32768 * ((b * b) * Bq b ^ 1868) ≤ Bq b ^ 1869 := by
    rw [k1]
    have := mul_le_mul_of_nonneg_right hB8 (hP 1868)
    linarith
  have hX : 2 + Tst b * (Bq b - 1) + 2 * Gs ports b g < Bq b ^ 1869 := by linarith
  have hL : Lq b = 2 * b * (N0 b * Bq b ^ 1869) := by
    rw [Lq, N0, ← pow_add]
  have hNpos : 0 < N0 b := pow_pos (by linarith) _
  have a1 : N0 b * (2 + Tst b * (Bq b - 1) + 2 * Gs ports b g) < N0 b * Bq b ^ 1869 :=
    mul_lt_mul_of_pos_left hX hNpos
  have a2 : N0 b * Bq b ^ 1869 ≤ 2 * b * (N0 b * Bq b ^ 1869) := by
    have h0 : 0 ≤ N0 b * Bq b ^ 1869 := mul_nonneg hNpos.le (hP 1869)
    have : (1 : A) ≤ 2 * b := by linarith
    exact le_mul_of_one_le_left h0 this
  refine ⟨?_, hgN, hm⟩
  rw [hL, Scq, Tcq]
  have e : g + N0 b * (Tst b + 2 * Gs ports b g) + (maskq b + N0 b * (Tst b * (Bq b - 2))) =
      g + maskq b + N0 b * (Tst b * (Bq b - 1) + 2 * Gs ports b g) := by ring
  rw [e]
  linarith

end Order

end Nine121.N105Prefix
