import DiophantineConsistency.Compact44.P72Early
import DiophantineConsistency.AdaptiveGap85GenericSignedHalfIndex
import DiophantineConsistency.ArithmeticAdaptiveIndexComparison2011
import DiophantineConsistency.ArithmeticPellFirstIndex

/-! # P13, section 6: exact indices and `q ∣ X`

Combine the early congruence `(2n) % μ = R + 1` (`R + 1 < μ`) with the main,
strong and auxiliary norms. Then:

* `2n ≥ R + 1`, so `n ≥ 13` and `k ≥ R + 1`;
* the comparison gives `n < m`, `14 ≤ m` and `2R < c`;
* the signed half-index theorem gives `m = R`. Then `2n = R + 1`;
* `k − R − 1 = 4Qs` is a multiple of `M = 4q²Y`, so the carrier gives
  `M ∣ H·S·X`, hence `q ∣ H·X` and `q ∣ X`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
noncomputable section
namespace P72Exact
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ModelDifferenceRing ArithmeticGcdNormalization ArithmeticPellRecurrence ArithmeticPellHalfIndex
open ArithmeticPellCongruences P72Mu
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem large_of_six (a p : V) (hp : 6 ≤ p) :
    (a + 2) * delta a * delta a < ycoord p a := by
  have hx : (a + 2) * delta a * delta a ≤
      32 * (a + 2) * delta a * delta a + 32 * (a + 2) * delta a := by
    calc (a + 2) * delta a * delta a ≤ 32 * ((a + 2) * delta a * delta a) :=
          le_mul_of_one_le_left (by simp) (by simp)
      _ = 32 * (a + 2) * delta a * delta a := by ring
      _ ≤ 32 * (a + 2) * delta a * delta a + 32 * (a + 2) * delta a := by simp
  have hpos : 0 < 6 * (a + 2) := mul_pos (by simp) (by simp)
  have h := lt_of_le_of_lt hx (lt_add_of_pos_right _ hpos)
  rw [← ArithmeticPellFirstIndex.y_six] at h
  exact lt_of_lt_of_le h ((y_strictMono a).monotone hp)

/-- The index window: from the early congruence alone, `13 ≤ n < m`, `14 ≤ m`,
`2R < c` and the size bound `(a+2)Δ² < c` that the signed half-index step needs. -/
theorem index_window (q X Y k R c a y0 n s μ m η : V)
    (hq3 : 3 ≤ q) (hX : 0 < X) (hy0 : 0 < y0) (hYq : Y = q * (q * q) * y0)
    (hη : 0 < η) (hc : c = η + Y * k) (ha : a = X * Y + Y)
    (hR26 : 26 ≤ R)
    (hny : 2 * ycoord n (2 * ((X * Y) * Y - 1) + 1) = k)
    (hks : k = 2 * n + 4 * ((X * Y) * Y) * s)
    (hnmod : (2 * n) % μ = R + 1)
    (hmy : ycoord m a = c) :
    13 ≤ n ∧ n < m ∧ 14 ≤ m ∧ 2 * R < c ∧ (a + 2) * delta a * delta a < c ∧ 0 < k ∧ 2 ≤ Y ∧
      0 < c := by
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq3
  have hY0 : 0 < Y := by rw [hYq]; exact mul_pos (mul_pos hq0 (mul_pos hq0 hq0)) hy0
  have hc0 : 0 < c := by rw [hc]; exact add_pos_of_pos_of_nonneg hη (Arithmetic.zero_le _)
  -- (1) 2n ≥ R + 1
  have h2n : R + 1 ≤ 2 * n := by rw [← hnmod]; exact mod_le _ _
  have hn13 : 13 ≤ n := by
    have h27 : 2 * 13 < 2 * n := lt_of_lt_of_le (by
      calc (2 * 13 : V) = 26 := by norm_num
        _ < 26 + 1 := lt_add_one _
        _ ≤ R + 1 := (add_le_add_iff_right 1).mpr hR26) h2n
    exact le_of_lt (lt_of_mul_lt_mul_left h27 (Arithmetic.zero_le _))
  have hRk : R + 1 ≤ k := le_trans h2n (by rw [hks]; exact le_add_of_nonneg_right (Arithmetic.zero_le _))
  have hk0 : 0 < k := lt_of_lt_of_le (by simp) hRk
  -- (2) comparison
  have hY2 : 2 ≤ Y := by
    rw [hYq]
    calc (2 : V) ≤ 3 := by norm_num
      _ ≤ q := hq3
      _ ≤ q * (q * q) := le_mul_of_one_le_right (Arithmetic.zero_le _)
          (one_le_mul_of_one_le_of_one_le (pos_iff_one_le.mp hq0) (pos_iff_one_le.mp hq0))
      _ ≤ q * (q * q) * y0 := le_mul_of_one_le_right (Arithmetic.zero_le _) (pos_iff_one_le.mp hy0)
  let E : V := X * Y
  let Q : V := E * Y
  let B : V := 2 * (Q - 1) + 1
  have hE : 0 < E := mul_pos hX hY0
  have hQ1 : Q - 1 + 1 = Q := tsub_add_cancel_of_le (pos_iff_one_le.mp (mul_pos hE hY0))
  have hB : B + 2 = 2 * Q + 1 := by
    show 2 * (Q - 1) + 1 + 2 = 2 * Q + 1
    calc 2 * (Q - 1) + 1 + 2 = 2 * (Q - 1 + 1) + 1 := by ring
      _ = 2 * Q + 1 := by rw [hQ1]
  have hab : a ≤ B := by
    have hEsub : E - 1 + 1 = E := tsub_add_cancel_of_le (pos_iff_one_le.mp hE)
    have hYsub : Y - 2 + 2 = Y := tsub_add_cancel_of_le hY2
    have heq : a + 2 + (E - 1) * (2 * (Y - 2) + 3) + (Y - 2) = B + 2 := by
      rw [hB, ha]
      calc X * Y + Y + 2 + (E - 1) * (2 * (Y - 2) + 3) + (Y - 2) =
          (E - 1 + 1) + (Y - 2 + 2) + 2 + (E - 1) * (2 * (Y - 2) + 3) + (Y - 2) := by
            rw [hEsub, hYsub]
        _ = 2 * ((E - 1 + 1) * (Y - 2 + 2)) + 1 := by ring
        _ = 2 * Q + 1 := by rw [hEsub, hYsub]
    have heq' : a + 2 ≤ B + 2 := by rw [← heq]; simp [add_assoc]
    exact (add_le_add_iff_right (2 : V)).mp heq'
  have hkc : k < c := calc
    k ≤ k * Y := le_mul_of_one_le_right (by simp) (le_trans (by simp : (1 : V) ≤ 2) hY2)
    _ < k * Y + η := lt_add_of_pos_right _ hη
    _ = c := by rw [hc]; ring
  have hnm : n < m := by
    by_contra hn
    have hm : m ≤ n := le_of_not_gt hn
    have hcle : c ≤ k := calc
      c = ycoord m a := hmy.symm
      _ ≤ ycoord n a := (y_strictMono a).monotone hm
      _ ≤ ycoord n B := (ArithmeticAdaptiveIndexComparison2011.base_mono a B hab n).2
      _ ≤ 2 * ycoord n B := le_mul_of_one_le_left (by simp) (by simp)
      _ = k := hny
    exact (not_le_of_gt hkc) hcle
  have hm14 : 14 ≤ m := by
    have h := le_trans (_root_.add_le_add hn13 (le_refl (1 : V))) (lt_iff_succ_le.mp hnm)
    simpa only [show (13 : V) + 1 = 14 by ring] using h
  have hhalf : 2 * R < c := calc
    2 * R < 2 * (R + 1) := mul_lt_mul_of_pos_left (lt_add_one R) (by simp)
    _ ≤ 2 * k := mul_le_mul_of_nonneg_left hRk (by simp)
    _ ≤ k * Y := by simpa only [mul_comm] using mul_le_mul_of_nonneg_left hY2 (Arithmetic.zero_le k)
    _ < k * Y + η := lt_add_of_pos_right _ hη
    _ = c := by rw [hc]; ring
  have hbig : (a + 2) * delta a * delta a < c := by
    rw [← hmy]; exact large_of_six a m (le_trans (by norm_num) hm14)
  exact ⟨hn13, hnm, hm14, hhalf, hbig, hk0, hY2, hc0⟩

/-- Once the rank is the main index, the early congruence forces `2n = R + 1`. -/
theorem index_close (R n μ m : V) (hRμ : R + 1 < μ) (hnmod : (2 * n) % μ = R + 1)
    (hnm : n < m) (hmR : m = R) : 2 * n = R + 1 := by
  -- 2n = R + 1
  have hnR : n < R := by rwa [← hmR]
  have hsmall : 2 * n < μ + (R + 1) := calc
    2 * n < 2 * R := mul_lt_mul_of_pos_left hnR (by simp)
    _ = R + R := by ring
    _ < μ + (R + 1) := add_lt_add (lt_trans (lt_add_one R) hRμ) (lt_add_one R)
  have hdiv : (2 * n) / μ = 0 := by
    by_contra hz
    have hd : 1 ≤ (2 * n) / μ := pos_iff_one_le.mp (pos_iff_ne_zero.mpr hz)
    have he : μ + (R + 1) ≤ 2 * n := calc
      μ + (R + 1) ≤ μ * ((2 * n) / μ) + (R + 1) :=
        _root_.add_le_add (le_mul_of_one_le_right (by simp) hd) (le_refl _)
      _ = 2 * n := by rw [← hnmod]; exact div_add_mod _ _
    exact (not_le_of_gt hsmall) he
  have hnR1 : 2 * n = R + 1 := by
    have he := (div_add_mod (2 * n) μ).symm
    rw [hdiv, hnmod] at he
    simpa only [mul_zero, zero_add] using he
  exact hnR1

/-- The index part: `13 ≤ n`, `n < m`, `m = R` and `2n = R + 1`, from the
early congruence and the main, ordinary strong and auxiliary norms. No carrier
is needed. -/
theorem indices_ordinary (q X Y k R g c a y0 i' f T u n s μ m η : V)
    (hq3 : 3 ≤ q) (hX : 0 < X) (hy0 : 0 < y0) (hYq : Y = q * (q * q) * y0)
    (hη : 0 < η) (hc : c = η + Y * k) (hi' : 0 < i') (hf : 0 < f)
    (ha : a = X * Y + Y)
    (hR26 : 26 ≤ R)
    (hny : 2 * ycoord n (2 * ((X * Y) * Y - 1) + 1) = k)
    (hks : k = 2 * n + 4 * ((X * Y) * Y) * s) (hRμ : R + 1 < μ)
    (hnmod : (2 * n) % μ = R + 1)
    (hmy : ycoord m a = c)
    (hg : g * g = 1 + delta a * c * c)
    (hs' : (i' * c * c) * (i' * c * c) + delta a = delta a * (f * f))
    (haux : ((3 + 4 * a) + a * a) * (f * f - 1) *
        (absdiff (f * f * (T * c)) (f * f * R + c) * absdiff (f * f * (T * c)) (f * f * R + c)) +
        absdiff (f * f * (T * c) + u) (f * f * R + c) * absdiff (f * f * (T * c) + u) (f * f * R + c) =
      1 + ((3 + 4 * a) + a * a) * (f * f - 1) *
        (absdiff (f * f * (T * c) + u) (f * f * R + c) * absdiff (f * f * (T * c) + u) (f * f * R + c))) :
    13 ≤ n ∧ n < m ∧ m = R ∧ 2 * n = R + 1 := by
  obtain ⟨hn13, hnm, hm14, hhalf, hbig, hk0, hY2, hc0⟩ :=
    index_window q X Y k R c a y0 n s μ m η hq3 hX hy0 hYq hη hc ha hR26 hny hks hnmod hmy
  -- the ordinary strong norm
  have hD : (3 + 4 * a) + a * a = delta a := by unfold delta; ring
  have hf1 : 1 ≤ f * f := one_le_mul_of_one_le_of_one_le (pos_iff_one_le.mp hf) (pos_iff_one_le.mp hf)
  let z : V := absdiff (f * f * (T * c + 0)) (f * f * R + c)
  let yv : V := absdiff (f * f * (T * c) + u) (f * f * R + c)
  have haux' : (i' * c * c) * (i' * c * c) * z * z + yv * yv =
      1 + (i' * c * c) * (i' * c * c) * yv * yv := by
    have e : ((3 + 4 * a) + a * a) * (f * f - 1) = (i' * c * c) * (i' * c * c) := by
      obtain ⟨g', hg'⟩ : ∃ g' : V, f * f = g' + 1 := ⟨f * f - 1, (tsub_add_cancel_of_le hf1).symm⟩
      rw [hg', add_tsub_cancel_right, hD]
      apply add_right_cancel (b := delta a)
      rw [hs', hg']; ring
    rw [e] at haux
    simp only [z, yv, add_zero]
    linear_combination haux
  have hc2 : 2 ≤ c := le_trans (by
      calc (2 : V) ≤ 1 * 2 := by simp
        _ ≤ k * Y := mul_le_mul (pos_iff_one_le.mp hk0) hY2 (by simp) (Arithmetic.zero_le _)) (le_of_lt (by
      calc k * Y < k * Y + η := lt_add_of_pos_right _ hη
        _ = c := by rw [hc]; ring))
  have hI2 : 2 ≤ i' * c * c := calc
    2 ≤ c := hc2
    _ ≤ i' * c := le_mul_of_one_le_left (Arithmetic.zero_le _) (pos_iff_one_le.mp hi')
    _ ≤ i' * c * c := le_mul_of_one_le_right (Arithmetic.zero_le _) (pos_iff_one_le.mp hc0)
  have hyv : 0 < yv := pos_iff_ne_zero.mpr (by
    intro hy0'
    have hp : (i' * c * c) * (i' * c * c) * z * z = 1 := by
      simpa only [hy0', mul_zero, zero_mul, add_zero] using haux'
    have hd : (i' * c * c) * (i' * c * c) ∣ (1 : V) := ⟨z * z, by simpa only [mul_assoc] using hp.symm⟩
    have hle : (i' * c * c) * (i' * c * c) ≤ 1 := Arithmetic.le_of_dvd (by simp) hd
    have hIle : i' * c * c ≤ (i' * c * c) * (i' * c * c) :=
      le_mul_of_one_le_right (by simp) (le_trans (by simp : (1 : V) ≤ 2) hI2)
    exact (not_le_of_gt (lt_of_lt_of_le (by simp : (1 : V) < 2) hI2)) (le_trans hIle hle))
  have hm0 : 0 < m := lt_of_lt_of_le (by norm_num) hm14
  have hRabs : absdiff R 0 = R := by simp [absdiff]
  have hR0 : 0 < absdiff R 0 := by rw [hRabs]; exact lt_of_lt_of_le (by norm_num) hR26
  have hmR : m = R := by
    have h := AdaptiveGap85GenericSignedHalfIndex.signed_half_index_of_facts a c g f i' T R 0 yv m
      hc0 hi' hf hm0 hyv hmy hR0 (by rw [hRabs]; exact hhalf) hg hs' hbig haux'
    rwa [hRabs] at h
  exact ⟨hn13, hnm, hmR, index_close R n μ m hRμ hnmod hnm hmR⟩

theorem exact_ordinary (q X Y k R H M S g c a γ y0 i' f T u n s μ m η : V)
    (hq3 : 3 ≤ q) (hX : 0 < X) (hy0 : 0 < y0) (hYq : Y = q * (q * q) * y0)
    (hη : 0 < η) (hc : c = η + Y * k) (hi' : 0 < i') (hf : 0 < f)
    (ha : a = X * Y + Y)
    (hS : S = 4 * (Y * q)) (hM : M = S * q)
    (hcar : M * g + H * k = M * (X + a * c) + H * (M * γ + S * X + R + 1))
    (hqH : Bez q H 1)
    (hR26 : 26 ≤ R)
    -- early
    (hny : 2 * ycoord n (2 * ((X * Y) * Y - 1) + 1) = k)
    (hks : k = 2 * n + 4 * ((X * Y) * Y) * s) (hRμ : R + 1 < μ)
    (hnmod : (2 * n) % μ = R + 1)
    -- main, strong, auxiliary
    (hmy : ycoord m a = c)
    (hg : g * g = 1 + delta a * c * c)
    (hs' : (i' * c * c) * (i' * c * c) + delta a = delta a * (f * f))
    (haux : ((3 + 4 * a) + a * a) * (f * f - 1) *
        (absdiff (f * f * (T * c)) (f * f * R + c) * absdiff (f * f * (T * c)) (f * f * R + c)) +
        absdiff (f * f * (T * c) + u) (f * f * R + c) * absdiff (f * f * (T * c) + u) (f * f * R + c) =
      1 + ((3 + 4 * a) + a * a) * (f * f - 1) *
        (absdiff (f * f * (T * c) + u) (f * f * R + c) * absdiff (f * f * (T * c) + u) (f * f * R + c))) :
    13 ≤ n ∧ n < m ∧ m = R ∧ 2 * n = R + 1 ∧ q ∣ X := by
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq3
  have hY0 : 0 < Y := by rw [hYq]; exact mul_pos (mul_pos hq0 (mul_pos hq0 hq0)) hy0
  obtain ⟨hn13, hnm, hmR, hnR1⟩ := indices_ordinary q X Y k R g c a y0 i' f T u n s μ m η
    hq3 hX hy0 hYq hη hc hi' hf ha hR26 hny hks hRμ hnmod hmy hg hs' haux
  -- q ∣ X
  have hS0 : 0 < S := by rw [hS]; exact mul_pos (by norm_num) (mul_pos hY0 hq0)
  have hM0 : 0 < M := by rw [hM]; exact mul_pos hS0 hq0
  have hcar' : M * (g + H * (X * q * y0 * s)) = M * (X + a * c + H * γ) + H * S * X := by
    have h1 : M * g + H * k = M * (g + H * (X * q * y0 * s)) + H * (R + 1) := by
      rw [hks, hnR1, hM, hS, hYq]; ring
    have h2 : M * (X + a * c) + H * (M * γ + S * X + R + 1) =
        M * (X + a * c + H * γ) + H * S * X + H * (R + 1) := by ring
    rw [h1, h2] at hcar
    exact add_right_cancel hcar
  have hMd : M ∣ H * S * X := by
    have h : (M * (g + H * (X * q * y0 * s))) % M = (M * (X + a * c + H * γ) + H * S * X) % M :=
      congrArg (fun z : V => z % M) hcar'
    rw [show M * (g + H * (X * q * y0 * s)) = (g + H * (X * q * y0 * s)) * M by ring,
      mod_mul_self_left] at h
    rw [show M * (X + a * c + H * γ) + H * S * X = H * S * X + M * (X + a * c + H * γ) by ring,
      mod_add_mul' _ _ hM0] at h
    exact mod_eq_zero_iff_dvd.mp h.symm
  have hqHX : q ∣ H * X := by
    rw [hM, show H * S * X = H * X * S by ring, mul_comm S q] at hMd
    exact (mul_dvd_mul_iff_right (ne_of_gt hS0)).mp hMd
  exact ⟨hn13, hnm, hmR, hnR1, unit_certificate_cancel (bez_swap hqH) hqHX⟩

/-- P13's form: the normalized strong norm `f² = 1 + Δ(c²i)²`, through the
ordinary strong index `i' = Δi`. -/
theorem exact (q X Y k R H M S g c a γ y0 i f T u n s μ m η : V)
    (hq3 : 3 ≤ q) (hX : 0 < X) (hy0 : 0 < y0) (hYq : Y = q * (q * q) * y0)
    (hη : 0 < η) (hc : c = η + Y * k) (hi : 0 < i) (hf : 0 < f)
    (ha : a = X * Y + Y)
    (hS : S = 4 * (Y * q)) (hM : M = S * q)
    (hcar : M * g + H * k = M * (X + a * c) + H * (M * γ + S * X + R + 1))
    (hqH : Bez q H 1)
    (hR26 : 26 ≤ R)
    (hny : 2 * ycoord n (2 * ((X * Y) * Y - 1) + 1) = k)
    (hks : k = 2 * n + 4 * ((X * Y) * Y) * s) (hRμ : R + 1 < μ)
    (hnmod : (2 * n) % μ = R + 1)
    (hmy : ycoord m a = c)
    (hg : g * g = 1 + delta a * c * c)
    (hstrong : f * f = 1 + ((3 + 4 * a) + a * a) * (((c * c) * i) * ((c * c) * i)))
    (haux : ((3 + 4 * a) + a * a) * (f * f - 1) *
        (absdiff (f * f * (T * c)) (f * f * R + c) * absdiff (f * f * (T * c)) (f * f * R + c)) +
        absdiff (f * f * (T * c) + u) (f * f * R + c) * absdiff (f * f * (T * c) + u) (f * f * R + c) =
      1 + ((3 + 4 * a) + a * a) * (f * f - 1) *
        (absdiff (f * f * (T * c) + u) (f * f * R + c) * absdiff (f * f * (T * c) + u) (f * f * R + c))) :
    13 ≤ n ∧ n < m ∧ m = R ∧ 2 * n = R + 1 ∧ q ∣ X := by
  have hD : (3 + 4 * a) + a * a = delta a := by unfold delta; ring
  exact exact_ordinary q X Y k R H M S g c a γ y0 (((3 + 4 * a) + a * a) * i) f T u n s μ m η
    hq3 hX hy0 hYq hη hc (mul_pos (by positivity) hi) hf ha hS hM hcar hqH hR26 hny hks hRμ hnmod
    hmy hg (by rw [hstrong, ← hD]; ring) haux

end P72Exact

#print axioms P72Exact.index_window
#print axioms P72Exact.index_close
#print axioms P72Exact.indices_ordinary
#print axioms P72Exact.exact_ordinary
#print axioms P72Exact.exact
