import DiophantineConsistency.Nine121.N82Layout
import DiophantineConsistency.Nine121.N101Prefix

/-! # Package 71's source65 prefix (package 82's nine-positive equation): definitions and estimates

The prefix of `82-pell-congruences/nine_full_radical/PROOF.md` (§2), which keeps package 71's
source65 registers unchanged, for the shared-tap layout of `N82Layout`, in an arbitrary
commutative ring:

  `B = 2^2134939 b²`, `ℓ = Σᵢ B^{wᵢ}`, `T* = Σₖ B^{qₖ}`, `U* = g + ℓ`,
  `G* = K₀(B) + U*(K₁(B) + U* K₂(B))`, `N₀ = B¹¹⁷`, `M₀ = N₀ − 1 − ℓ(b − 1)`,
  `T_c = M₀ + N₀ T*(B − 2)`, `S* = g + N₀(T* + 2G*)`, `L = bB¹⁹⁹¹`,
  `R = L(1 + (T_c + S*)) − S* − 1`, `N = 2^17079501 b B¹⁰⁵⁷`, `t = bB¹¹⁶`.

The base `Bq` and the base scale are package 101's (`N101Prefix.Bq`, `baseScale`); the threshold
scale `2^17079501` is the irreducible integer `thresholdScale82`. Height `1873`, `W = 116`,
largest target `1841`, kernel degrees `1384, 1739, 1641` (leading quadratic coefficient `1`).

In a linearly ordered ring, with an abstract bound `H` on every kernel coefficient and
`4096 H b² ≤ B`, `8 ≤ H`, `1 ≤ b`:

* `Gs_pos`: `G* > 0` as soon as `U* ≥ B¹¹⁶` (unconditional positivity of the prefix);
* `Gs_le`: on the soundness range `U* ≤ 35 b B¹¹⁶`, `G* ≤ 2486 b² B¹⁸⁷³`;
* `coeff_bound`: every coefficient `c` of `N82Layout.sourcePoly` at weights `0 ≤ uᵢ ≤ b` has
  `4|c| + 4 ≤ B`;
* `sum_lt_L`: on the soundness range, `S* + T_c < L`, `g < N₀`, `M₀ < N₀`;
* `c_bounds`: the 84 kernel coefficients are bounded by `H` under the port bounds. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace Nine121.N82Prefix
open Polynomial SparseExtraction N82Layout
open N101Prefix (Bq baseScale abs_kernel_le pow_step mul_pow_le_succ scale_facts sum_range_table)

/-- The threshold scale `2^17079501` (`threshold_scale` of the JSON). -/
def thresholdScale82 : ℤ := 2 ^ 17079501

attribute [irreducible] thresholdScale82

section Ring
variable {A : Type*} [CommRing A]

def ell (b : A) : A := ∑ i, Bq b ^ weights i
def Tst (b : A) : A := ∑ k, Bq b ^ targets k
def ker0 (ports : Fin 4 → A) (b : A) : A := ∑ p, c0 ports p * Bq b ^ pos0 p
def ker1 (ports : Fin 4 → A) (b : A) : A := ∑ p, c1 ports p * Bq b ^ pos1 p
def ker2 (ports : Fin 4 → A) (b : A) : A := ∑ p, c2 ports p * Bq b ^ pos2 p
def Ust (b g : A) : A := g + ell b
def Gs (ports : Fin 4 → A) (b g : A) : A :=
  ker0 ports b + Ust b g * (ker1 ports b + Ust b g * ker2 ports b)
def N0 (b : A) : A := Bq b ^ 117
def maskq (b : A) : A := N0 b - 1 - ell b * (b - 1)
def Tcq (b : A) : A := maskq b + N0 b * (Tst b * (Bq b - 2))
def Scq (ports : Fin 4 → A) (b g : A) : A := g + N0 b * (Tst b + 2 * Gs ports b g)
def Lq (b : A) : A := b * Bq b ^ 1991
def Rq (ports : Fin 4 → A) (b g : A) : A :=
  Lq b * (1 + (Tcq b + Scq ports b g)) - Scq ports b g - 1
def Nq (b : A) : A := (thresholdScale82 : A) * b * Bq b ^ 1057
def tq (b : A) : A := b * Bq b ^ 116

theorem Gs_eval (ports : Fin 4 → A) (b g : A) (u : Fin 31 → A)
    (hu : Ust b g = ∑ i, u i * Bq b ^ weights i) :
    Gs ports b g = (sourcePoly ports u).eval (Bq b) := by
  simp only [sourcePoly, eval_add, eval_mul, eval_pow, eval_wordPoly, eval_kernelPoly]
  rw [← hu, Gs, ker0, ker1, ker2]
  ring

theorem natDegree_sourcePoly (ports : Fin 4 → A) (u : Fin 31 → A) :
    (sourcePoly ports u).natDegree ≤ 1873 := by
  have hw : (wordPoly weights u).natDegree ≤ 116 :=
    natDegree_sum_le_of_forall_le _ _ (fun i _ => (natDegree_monomial_le _).trans (weights_le i))
  have h2 : (kernelPoly pos2 (c2 ports)).natDegree ≤ 1641 :=
    natDegree_sum_le_of_forall_le _ _ (fun p _ => (natDegree_monomial_le _).trans (pos2_le p))
  have h1 : (kernelPoly pos1 (c1 ports)).natDegree ≤ 1739 :=
    natDegree_sum_le_of_forall_le _ _ (fun p _ => (natDegree_monomial_le _).trans (pos1_le p))
  have h0 : (kernelPoly pos0 (c0 ports)).natDegree ≤ 1384 :=
    natDegree_sum_le_of_forall_le _ _ (fun p _ => (natDegree_monomial_le _).trans (pos0_le p))
  have hq : (wordPoly weights u ^ 2 * kernelPoly pos2 (c2 ports)).natDegree ≤ 1873 :=
    (natDegree_mul_le_of_le (natDegree_pow_le_of_le 2 hw) h2).trans (by norm_num)
  have hl : (wordPoly weights u * kernelPoly pos1 (c1 ports)).natDegree ≤ 1873 :=
    (natDegree_mul_le_of_le hw h1).trans (by norm_num)
  exact natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le hq hl) (h0.trans (by norm_num))

/-- The range-sum form of `G*`. -/
theorem Gs_sum (ports : Fin 4 → A) (b g : A) (u : Fin 31 → A)
    (hu : Ust b g = ∑ i, u i * Bq b ^ weights i) :
    Gs ports b g = ∑ e ∈ Finset.range 1874, (sourcePoly ports u).coeff e * Bq b ^ e := by
  rw [Gs_eval ports b g u hu, eval_eq_sum_range' (n := 1874) (lt_of_le_of_lt (natDegree_sourcePoly ports u)
    (by norm_num))]

/-- `ker2 = rest + B¹⁶⁴¹`, the leading record split off. -/
theorem ker2_split (ports : Fin 4 → A) (b : A) :
    ker2 ports b = (∑ i : Fin 38, c2 ports i.castSucc * Bq b ^ pos2 i.castSucc) + Bq b ^ 1641 := by
  rw [ker2, Fin.sum_univ_castSucc, show (Fin.last 38 : Fin 39) = ⟨38, by decide⟩ from rfl,
    c2_last, pos2_last, one_mul]

end Ring

section Order
variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- The 84 kernel coefficients are bounded by `H` under the port bounds. -/
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

end Order

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

theorem Tst_le (b : A) (hB : 1 ≤ Bq b) : Tst b ≤ 22 * Bq b ^ 1841 := by
  calc Tst b = ∑ k, Bq b ^ targets k := rfl
    _ ≤ ∑ _k : Fin 22, Bq b ^ 1841 :=
        Finset.sum_le_sum (fun k _ => pow_le_pow_right₀ hB (targets_le k))
    _ = 22 * Bq b ^ 1841 := by simp

theorem Tst_nonneg (b : A) (hB : 0 ≤ Bq b) : 0 ≤ Tst b :=
  Finset.sum_nonneg (fun k _ => pow_nonneg hB _)

/-- The three kernel estimates. -/
theorem ker_bounds (ports : Fin 4 → A) (b H : A) (hB : 1 ≤ Bq b)
    (hc : (∀ q, |c0 ports q| ≤ H) ∧ (∀ q, |c1 ports q| ≤ H) ∧ (∀ q, |c2 ports q| ≤ H)) :
    |ker0 ports b| ≤ 7 * (H * Bq b ^ 1384) ∧ |ker1 ports b| ≤ 38 * (H * Bq b ^ 1739) ∧
      Bq b ^ 1641 - 38 * (H * Bq b ^ 1640) ≤ ker2 ports b ∧
      ker2 ports b ≤ Bq b ^ 1641 + 38 * (H * Bq b ^ 1640) := by
  obtain ⟨h0, h1, h2⟩ := hc
  have k0 := abs_kernel_le pos0 (c0 ports) H (Bq b) hB 1384 h0 pos0_le
  have k1 := abs_kernel_le pos1 (c1 ports) H (Bq b) hB 1739 h1 pos1_le
  have k2 := abs_kernel_le (fun i : Fin 38 => pos2 i.castSucc) (fun i => c2 ports i.castSucc) H
    (Bq b) hB 1640 (fun i => h2 _) (fun i => pos2_top _ (Fin.castSucc_lt_last i).ne)
  push_cast at k0 k1 k2
  rw [abs_le] at k2
  refine ⟨k0, k1, ?_, ?_⟩ <;> rw [ker2_split] <;> linarith [k2.1, k2.2]

/-- Core of the unconditional positivity, over plain variables. -/
theorem core_pos (B U X0 X1 X2 H : A) (hB32 : 32768 ≤ B) (hBH : 4096 * H ≤ B) (hH : 8 ≤ H)
    (k0 : |X0| ≤ 7 * (H * B ^ 1384)) (k1 : |X1| ≤ 38 * (H * B ^ 1739))
    (k2 : B ^ 1641 - 38 * (H * B ^ 1640) ≤ X2) (hU : B ^ 116 ≤ U) :
    0 < X0 + U * (X1 + U * X2) := by
  have hB1 : (1 : A) ≤ B := by linarith
  have hB0 : (0 : A) ≤ B := by linarith
  have hP : ∀ n, (0 : A) ≤ B ^ n := fun n => pow_nonneg hB0 n
  have hH0 : (0 : A) ≤ H := by linarith
  have e1 : 4096 * H * B ^ 1640 ≤ B ^ 1641 := mul_pow_le_succ B _ hB0 hBH 1640
  have e2 : 4096 * H * B ^ 1739 ≤ B ^ 1740 := mul_pow_le_succ B _ hB0 hBH 1739
  have e3 : 4096 * H * B ^ 1384 ≤ B ^ 1385 := mul_pow_le_succ B _ hB0 hBH 1384
  have hX2 : B ^ 1641 ≤ 2 * X2 := by linarith [hP 1641]
  have hX1 : -B ^ 1740 ≤ X1 := by linarith [neg_abs_le X1, hP 1740]
  have hX0 : -B ^ 1385 ≤ X0 := by linarith [neg_abs_le X0, hP 1385]
  have hU0 : 0 ≤ U := le_trans (hP 116) hU
  have f1 : B ^ 1757 ≤ 2 * (U * X2) := by
    have a1 : B ^ 116 * B ^ 1641 ≤ U * B ^ 1641 := mul_le_mul_of_nonneg_right hU (hP 1641)
    have a2 : U * B ^ 1641 ≤ U * (2 * X2) := mul_le_mul_of_nonneg_left hX2 hU0
    have a3 : B ^ 1757 = B ^ 116 * B ^ 1641 := by rw [← pow_add]
    linarith
  have f2 : 4 * B ^ 1740 ≤ B ^ 1757 := by
    have a1 : (4 : A) ≤ B ^ 17 :=
      le_trans (by linarith) (le_trans (le_of_eq (pow_one B).symm) (pow_step B hB1 1 17 (by norm_num)))
    have a2 := mul_le_mul_of_nonneg_right a1 (hP 1740)
    have a3 : B ^ 1757 = B ^ 17 * B ^ 1740 := by rw [← pow_add]
    linarith
  have f3 : B ^ 1757 ≤ 4 * (X1 + U * X2) := by linarith
  have hY0 : 0 ≤ X1 + U * X2 := by linarith [hP 1757]
  have f4 : B ^ 1873 ≤ 4 * (U * (X1 + U * X2)) := by
    have a1 : B ^ 116 * (X1 + U * X2) ≤ U * (X1 + U * X2) := mul_le_mul_of_nonneg_right hU hY0
    have a2 : B ^ 116 * B ^ 1757 ≤ B ^ 116 * (4 * (X1 + U * X2)) :=
      mul_le_mul_of_nonneg_left f3 (hP 116)
    have a3 : B ^ 1873 = B ^ 116 * B ^ 1757 := by rw [← pow_add]
    linarith
  have f5 : 8 * B ^ 1385 ≤ B ^ 1873 := by
    have a1 : (8 : A) ≤ B ^ 488 :=
      le_trans (by linarith) (le_trans (le_of_eq (pow_one B).symm) (pow_step B hB1 1 488 (by norm_num)))
    have a2 := mul_le_mul_of_nonneg_right a1 (hP 1385)
    have a3 : B ^ 1873 = B ^ 488 * B ^ 1385 := by rw [← pow_add]
    linarith
  have hpos : (0 : A) < B ^ 1873 := pow_pos (by linarith) _
  linarith

/-- Core of the soundness-range upper bound, over plain variables. -/
theorem core_le (B U X0 X1 X2 H b : A) (hb : 1 ≤ b) (hB32 : 32768 ≤ B) (hBH : 4096 * H ≤ B)
    (hH : 8 ≤ H) (k0 : |X0| ≤ 7 * (H * B ^ 1384)) (k1 : |X1| ≤ 38 * (H * B ^ 1739))
    (k2 : X2 ≤ B ^ 1641 + 38 * (H * B ^ 1640)) (hU0 : 0 ≤ U) (hU : U ≤ 35 * (b * B ^ 116)) :
    X0 + U * (X1 + U * X2) ≤ 2486 * ((b * b) * B ^ 1873) := by
  have hB1 : (1 : A) ≤ B := by linarith
  have hB0 : (0 : A) ≤ B := by linarith
  have hP : ∀ n, (0 : A) ≤ B ^ n := fun n => pow_nonneg hB0 n
  have hH0 : (0 : A) ≤ H := by linarith
  have e1 : 4096 * H * B ^ 1640 ≤ B ^ 1641 := mul_pow_le_succ B _ hB0 hBH 1640
  have e2 : 4096 * H * B ^ 1739 ≤ B ^ 1740 := mul_pow_le_succ B _ hB0 hBH 1739
  have e3 : 4096 * H * B ^ 1384 ≤ B ^ 1385 := mul_pow_le_succ B _ hB0 hBH 1384
  have hX2 : X2 ≤ 2 * B ^ 1641 := by linarith [hP 1641]
  have hX1 : X1 ≤ B ^ 1740 := by linarith [le_abs_self X1, hP 1740]
  have hX0 : X0 ≤ B ^ 1385 := by linarith [le_abs_self X0, hP 1385]
  have hb0 : (0 : A) ≤ b := by linarith
  have hbb : (1 : A) ≤ b * b := by nlinarith
  have hW0 : 0 ≤ b * B ^ 116 := mul_nonneg hb0 (hP 116)
  have g1 : U * U ≤ (35 * (b * B ^ 116)) * (35 * (b * B ^ 116)) :=
    mul_le_mul hU hU hU0 (by linarith)
  have hWW : (b * B ^ 116) * (b * B ^ 116) * B ^ 1641 = (b * b) * B ^ 1873 := by
    rw [show (1873 : ℕ) = 116 + 116 + 1641 by norm_num, pow_add, pow_add]; ring
  have g2 : U * (U * X2) ≤ 2450 * ((b * b) * B ^ 1873) := by
    have a1 : U * (U * X2) ≤ U * (U * (2 * B ^ 1641)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hX2 hU0) hU0
    have a2 : U * U * (2 * B ^ 1641) ≤
        (35 * (b * B ^ 116)) * (35 * (b * B ^ 116)) * (2 * B ^ 1641) :=
      mul_le_mul_of_nonneg_right g1 (by linarith [hP 1641])
    have a3 : U * (U * (2 * B ^ 1641)) = U * U * (2 * B ^ 1641) := by ring
    have a4 : (35 * (b * B ^ 116)) * (35 * (b * B ^ 116)) * (2 * B ^ 1641) =
        2450 * ((b * B ^ 116) * (b * B ^ 116) * B ^ 1641) := by ring
    linarith
  have g3 : U * X1 ≤ 35 * ((b * b) * B ^ 1873) := by
    have a0 : U * X1 ≤ U * B ^ 1740 := mul_le_mul_of_nonneg_left hX1 hU0
    have a1 : U * B ^ 1740 ≤ 35 * (b * B ^ 116) * B ^ 1740 :=
      mul_le_mul_of_nonneg_right hU (hP 1740)
    have a2 : (b * B ^ 116) * B ^ 1740 = b * B ^ 1856 := by
      rw [show (1856 : ℕ) = 116 + 1740 by norm_num, pow_add]; ring
    have a3 : b * B ^ 1856 ≤ b * B ^ 1873 :=
      mul_le_mul_of_nonneg_left (pow_step B hB1 _ _ (by norm_num)) hb0
    have a4 : b * B ^ 1873 ≤ (b * b) * B ^ 1873 :=
      mul_le_mul_of_nonneg_right (le_mul_of_one_le_left hb0 hb) (hP 1873)
    have a5 : 35 * (b * B ^ 116) * B ^ 1740 = 35 * ((b * B ^ 116) * B ^ 1740) := by ring
    linarith
  have g4 : X0 ≤ (b * b) * B ^ 1873 := by
    have a1 : B ^ 1385 ≤ B ^ 1873 := pow_step B hB1 _ _ (by norm_num)
    have a2 : B ^ 1873 ≤ (b * b) * B ^ 1873 := le_mul_of_one_le_left (hP 1873) hbb
    linarith
  have e : X0 + U * (X1 + U * X2) = X0 + U * X1 + U * (U * X2) := by ring
  rw [e]
  linarith

/-- **Unconditional positivity** of `G*` (given `U* ≥ B¹¹⁶`). -/
theorem Gs_pos (ports : Fin 4 → A) (b g H : A) (hb : 1 ≤ b) (hH : 8 ≤ H)
    (hBb : 4096 * H * (b * b) ≤ Bq b)
    (hc : (∀ q, |c0 ports q| ≤ H) ∧ (∀ q, |c1 ports q| ≤ H) ∧ (∀ q, |c2 ports q| ≤ H))
    (hU : Bq b ^ 116 ≤ Ust b g) : 0 < Gs ports b g := by
  obtain ⟨hB32, hBH, -, -⟩ := scale_facts b H hb hH hBb
  obtain ⟨k0, k1, k2, -⟩ := ker_bounds ports b H (by linarith) hc
  exact core_pos (Bq b) (Ust b g) _ _ _ H hB32 hBH hH k0 k1 k2 hU

/-- **The soundness-range upper bound** on `G*`. -/
theorem Gs_le (ports : Fin 4 → A) (b g H : A) (hb : 1 ≤ b) (hH : 8 ≤ H)
    (hBb : 4096 * H * (b * b) ≤ Bq b)
    (hc : (∀ q, |c0 ports q| ≤ H) ∧ (∀ q, |c1 ports q| ≤ H) ∧ (∀ q, |c2 ports q| ≤ H))
    (hU0 : 0 ≤ Ust b g) (hU : Ust b g ≤ 35 * (b * Bq b ^ 116)) :
    Gs ports b g ≤ 2486 * ((b * b) * Bq b ^ 1873) := by
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
      (wordPoly weights u * kernelPoly pos1 (c1 ports)).coeff e)
      ((kernelPoly pos0 (c0 ports)).coeff e)
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
  have k1 : Bq b ^ 1874 = Bq b * Bq b ^ 1873 := by rw [← pow_succ']
  have k2 : Bq b ^ 1842 ≤ (b * b) * Bq b ^ 1873 :=
    le_trans (pow_step _ hB1 _ _ (by norm_num)) (le_mul_of_one_le_left (hP 1873) hbb)
  have k3 : Tst b * (Bq b - 1) ≤ 22 * Bq b ^ 1842 := by
    have a1 := mul_le_mul_of_nonneg_right hT (by linarith : (0 : A) ≤ Bq b - 1)
    have a2 : (22 : A) * Bq b ^ 1841 * (Bq b - 1) ≤ 22 * Bq b ^ 1841 * Bq b := by
      have := hP 1841; linarith
    have a3 : (22 : A) * Bq b ^ 1842 = 22 * Bq b ^ 1841 * Bq b := by rw [pow_succ]; ring
    linarith
  have k4 : (1 : A) ≤ (b * b) * Bq b ^ 1873 :=
    le_trans hbb (le_mul_of_one_le_right (by linarith) (one_le_pow₀ hB1))
  have hB8 : 32768 * (b * b) ≤ Bq b := by
    have := mul_le_mul_of_nonneg_right (show (4096 : A) * 8 ≤ 4096 * H by linarith)
      (le_trans zero_le_one hbb)
    linarith
  have k5 : 32768 * ((b * b) * Bq b ^ 1873) ≤ Bq b ^ 1874 := by
    rw [k1]
    have := mul_le_mul_of_nonneg_right hB8 (hP 1873)
    linarith
  have hX : 2 + Tst b * (Bq b - 1) + 2 * Gs ports b g < Bq b ^ 1874 := by linarith
  have hL : Lq b = b * (N0 b * Bq b ^ 1874) := by
    rw [Lq, N0, ← pow_add]
  have hNpos : 0 < N0 b := pow_pos (by linarith) _
  have a1 : N0 b * (2 + Tst b * (Bq b - 1) + 2 * Gs ports b g) < N0 b * Bq b ^ 1874 :=
    mul_lt_mul_of_pos_left hX hNpos
  have a2 : N0 b * Bq b ^ 1874 ≤ b * (N0 b * Bq b ^ 1874) := by
    have h0 : 0 ≤ N0 b * Bq b ^ 1874 := mul_nonneg hNpos.le (hP 1874)
    exact le_mul_of_one_le_left h0 hb
  refine ⟨?_, hgN, hm⟩
  rw [hL, Scq, Tcq]
  have e : g + N0 b * (Tst b + 2 * Gs ports b g) + (maskq b + N0 b * (Tst b * (Bq b - 2))) =
      g + maskq b + N0 b * (Tst b * (Bq b - 1) + 2 * Gs ports b g) := by ring
  rw [e]
  linarith

end Order

end Nine121.N82Prefix
