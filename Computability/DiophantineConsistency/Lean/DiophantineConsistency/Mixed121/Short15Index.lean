import DiophantineConsistency.Compact44.P72Exact
import DiophantineConsistency.Compact44.OrdinaryBlankSignedIndex
import DiophantineConsistency.ArithmeticPellCommonUnit

/-! # Fifteen-positive forms: the window, the index oracles and the negative branch

The fifteen-positive forms make the index multiplier explicit, `Nk = k − hE − R`,
and a zero only gives `Nk·Nt = 1`. This module supplies the port-free steps:

* `window_ring0`: `P72Window.window_ring` with `0 ≤ C` in place of `1 ≤ C`;
* `index_window'`: `P72Exact.index_window` with `13 ≤ n` and `R + 1 ≤ k` in place
  of the early congruence;
* `close_neg`: `(2n + 1) % μ = R`, `R + 1 < μ` and `n < m = R` give `2n + 1 = R`;
* `minus_false`: the negative branch is impossible. If `c = y_{2n+1}(a)` and
  `k = 2y_n(B)` with `B = 2XY² − 1`, then with `a' + 2 = x_2(a)`
  (`ArithmeticPellCommonUnit.composition`), `y_{2n}(a) = y_n(a')·2(a+2)` and
  `a' ≥ B`, so `c > y_{2n}(a) ≥ (a+2)k`; but `c = kY + η < (Y+1)k`;
* `oracle_free`, `oracle_gap`, `oracle_old`: the auxiliary norm with a free partner,
  with `y = V + e`, and at the old ordinate pin the main index to `R`, through
  `AdaptiveGap85GenericSignedHalfIndex.signed_half_index_of_facts` and
  `OrdinaryBlankSignedIndex.signed_half_index_blank`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
noncomputable section
namespace Short15Index
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ModelDifferenceRing ArithmeticPellRecurrence ArithmeticPellHalfIndex ArithmeticPellCongruences
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The rank window with a nonnegative transport gap. -/
theorem window_ring0 {q F α C β J MC MF : DiffRing V} (hq : q = F + (C + α))
    (hF : 1 ≤ F) (hα : 1 ≤ α) (hC : 0 ≤ C) (hJ : 1 ≤ J) (hβJ : β * J = q - 1)
    (hMC' : MC + 1 ≤ β) (hMF' : MF + 1 ≤ 2 * β) :
    ((q - 1) * (q - F) + α) * (q * q - 1) + (MC + MF * q) * J + 1 < q * (q * (q * q)) := by
  have hq2 : 2 ≤ q := by rw [hq]; linarith
  have h1 : q - F ≤ q - 1 := by linarith
  have h3 : α ≤ q - F := by rw [hq]; linarith
  have h4 : q * (q - F) ≤ q * (q - 1) := mul_le_mul_of_nonneg_left h1 (by linarith)
  have hG : (q - 1) * (q - F) + α ≤ q * q - q := by nlinarith
  have hqq : 0 ≤ q * q - 1 := by nlinarith
  have hGq : ((q - 1) * (q - F) + α) * (q * q - 1) ≤ (q * q - q) * (q * q - 1) :=
    mul_le_mul_of_nonneg_right hG hqq
  have hW : (MC + MF * q) * J ≤ ((β - 1) + (2 * β - 1) * q) * J := by
    apply mul_le_mul_of_nonneg_right _ (by linarith)
    have : MF * q ≤ (2 * β - 1) * q := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    linarith
  have hW2 : ((β - 1) + (2 * β - 1) * q) * J = (1 + 2 * q) * (q - 1) - (1 + q) * J := by
    rw [← hβJ]; ring
  have hJq : (1 + q) * 1 ≤ (1 + q) * J := mul_le_mul_of_nonneg_left hJ (by linarith)
  have hcube : 0 ≤ q * q * (q - 1) := mul_nonneg (by nlinarith) (by linarith)
  nlinarith

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

/-- The index window without the early congruence. -/
theorem index_window' (q X Y k R c a y0 n m η : V)
    (hq3 : 3 ≤ q) (hX : 0 < X) (hy0 : 0 < y0) (hYq : Y = q * (q * q) * y0)
    (hη : 0 < η) (hc : c = η + Y * k) (ha : a = X * Y + Y)
    (hn13 : 13 ≤ n) (hRk : R + 1 ≤ k)
    (hny : 2 * ycoord n (2 * ((X * Y) * Y - 1) + 1) = k)
    (hmy : ycoord m a = c) :
    n < m ∧ 14 ≤ m ∧ 2 * R < c ∧ (a + 2) * delta a * delta a < c ∧ 0 < c := by
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq3
  have hY0 : 0 < Y := by rw [hYq]; exact mul_pos (mul_pos hq0 (mul_pos hq0 hq0)) hy0
  have hc0 : 0 < c := by rw [hc]; exact add_pos_of_pos_of_nonneg hη (Arithmetic.zero_le _)
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
  have hk0 : 0 < k := lt_of_lt_of_le (by simp) hRk
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
  exact ⟨hnm, hm14, hhalf, hbig, hc0⟩

/-- The negative-branch close: `2n + 1 = R`. -/
theorem close_neg (R n μ m : V) (hRμ : R + 1 < μ) (hmod : (2 * n + 1) % μ = R)
    (hnm : n < m) (hmR : m = R) : 2 * n + 1 = R := by
  have hnR : n < R := by rwa [← hmR]
  have hn1 : n + 1 ≤ R := lt_iff_succ_le.mp hnR
  have hsmall : 2 * n + 1 < μ + R := calc
    2 * n + 1 < 2 * n + 2 := by
        rw [show (2 : V) * n + 2 = 2 * n + 1 + 1 by ring]; exact lt_add_one _
    _ = 2 * (n + 1) := by ring
    _ ≤ 2 * R := mul_le_mul_of_nonneg_left hn1 (by simp)
    _ = R + R := by ring
    _ < μ + R := (add_lt_add_iff_right R).mpr (lt_trans (lt_add_one R) hRμ)
  have hdiv : (2 * n + 1) / μ = 0 := by
    by_contra hz
    have hd : 1 ≤ (2 * n + 1) / μ := pos_iff_one_le.mp (pos_iff_ne_zero.mpr hz)
    have he : μ + R ≤ 2 * n + 1 := calc
      μ + R ≤ μ * ((2 * n + 1) / μ) + R :=
        _root_.add_le_add (le_mul_of_one_le_right (by simp) hd) (le_refl _)
      _ = 2 * n + 1 := by rw [← hmod]; exact div_add_mod _ _
    exact (not_le_of_gt hsmall) he
  have he := (div_add_mod (2 * n + 1) μ).symm
  rw [hdiv, hmod] at he
  simpa only [mul_zero, zero_add] using he

/-- The negative branch: `c = y_{2n+1}(a)`, `k = 2y_n(2XY² − 1)` and `c = kY + η`
with `η < k` are incompatible. -/
theorem minus_false (X Y k c a n m η ζ : V) (hX : 0 < X) (hY : 0 < Y) (hζ : 0 < ζ)
    (hk : k = η + ζ) (hc : c = η + Y * k) (ha : a = X * Y + Y)
    (hny : 2 * ycoord n (2 * ((X * Y) * Y - 1) + 1) = k) (hmy : ycoord m a = c)
    (hm : m = 2 * n + 1) : False := by
  have hx1 : xcoord 1 a = a + 2 := by
    have h := x_succ (0 : V) a
    rw [zero_add, x_zero, y_zero] at h
    rw [h]; ring
  have hy1 : ycoord 1 a = 1 := by
    have h := y_succ (0 : V) a
    rw [zero_add, x_zero, y_zero] at h
    rw [h]; ring
  have hx2 : xcoord 2 a = (a + 2) * (a + 2) + delta a := by
    have h := x_succ (1 : V) a
    rw [show (1 : V) + 1 = 2 by norm_num, hx1, hy1] at h
    rw [h]; ring
  have hy2 : ycoord 2 a = 2 * (a + 2) := by
    have h := y_succ (1 : V) a
    rw [show (1 : V) + 1 = 2 by norm_num, hx1, hy1] at h
    rw [h]; ring
  have ha2 : 2 ≤ a + 2 := le_add_self
  have hsq : a + 2 ≤ (a + 2) * (a + 2) :=
    le_mul_of_one_le_left (Arithmetic.zero_le _) (le_trans (by norm_num) ha2)
  have h2x : 2 ≤ xcoord 2 a := by
    rw [hx2]; exact le_trans (le_trans ha2 hsq) le_self_add
  set a' : V := xcoord 2 a - 2 with ha'def
  have ha' : a' + 2 = xcoord 2 a := tsub_add_cancel_of_le h2x
  have hcomp := (ArithmeticPellCommonUnit.composition a' a 2 ha' n).2
  rw [hy2] at hcomp
  -- a' ≥ B = 2XY² − 1
  set Q : V := X * Y * Y with hQ
  have hQ0 : 0 < Q := mul_pos (mul_pos hX hY) hY
  have hQ1 : Q - 1 + 1 = Q := tsub_add_cancel_of_le (pos_iff_one_le.mp hQ0)
  have hB : 2 * (Q - 1) + 1 + 2 = 2 * Q + 1 := by
    calc 2 * (Q - 1) + 1 + 2 = 2 * (Q - 1 + 1) + 1 := by ring
      _ = 2 * Q + 1 := by rw [hQ1]
  have hYY : 1 ≤ Y * Y := one_le_mul_of_one_le_of_one_le (pos_iff_one_le.mp hY) (pos_iff_one_le.mp hY)
  have haa : 2 * Q + 1 ≤ a * a := by
    have e : a * a = 2 * Q + (X * Y * (X * Y) + Y * Y) := by rw [ha, hQ]; ring
    rw [e]
    exact (add_le_add_iff_left (2 * Q)).mpr (le_trans hYY le_add_self)
  have hBa : 2 * (Q - 1) + 1 ≤ a' := by
    apply (add_le_add_iff_right (2 : V)).mp
    rw [hB, ha', hx2]
    calc 2 * Q + 1 ≤ a * a := haa
      _ ≤ (a + 2) * (a + 2) := mul_le_mul le_self_add le_self_add (Arithmetic.zero_le _)
          (Arithmetic.zero_le _)
      _ ≤ (a + 2) * (a + 2) + delta a := le_self_add
  have hbase := (ArithmeticAdaptiveIndexComparison2011.base_mono (2 * (Q - 1) + 1) a' hBa n).2
  -- (a + 2)k ≤ y_{2n}(a) < c
  have hk2 : k * (a + 2) ≤ ycoord (2 * n) a := by
    rw [← hcomp, ← hny]
    calc 2 * ycoord n (2 * (Q - 1) + 1) * (a + 2) = ycoord n (2 * (Q - 1) + 1) * (2 * (a + 2)) := by ring
      _ ≤ ycoord n a' * (2 * (a + 2)) := mul_le_mul_of_nonneg_right hbase (Arithmetic.zero_le _)
  have hlt : ycoord (2 * n) a < c := by
    rw [← hmy, hm]; exact y_succ_lt _ _
  -- but c < (Y + 1)k ≤ (a + 2)k
  have hηk : η < k := by rw [hk]; exact lt_add_of_pos_right _ hζ
  have hYa : Y + 1 ≤ a + 2 := by
    rw [ha]
    calc Y + 1 ≤ Y + 2 := (add_le_add_iff_left Y).mpr (by norm_num)
      _ ≤ X * Y + Y + 2 := (add_le_add_iff_right 2).mpr le_add_self
  have hc' : c < k * (a + 2) := calc
    c = η + Y * k := hc
    _ < k + Y * k := (add_lt_add_iff_right _).mpr hηk
    _ = k * (Y + 1) := by ring
    _ ≤ k * (a + 2) := mul_le_mul_of_nonneg_left hYa (Arithmetic.zero_le _)
  exact absurd (lt_trans hc' (lt_of_le_of_lt hk2 hlt)) (_root_.lt_irrefl _)

/-! ## The index oracles -/

theorem ord_eq (a c f i : V) (hf : 0 < f)
    (hs : (i * c * c) * (i * c * c) + delta a = delta a * (f * f)) :
    delta a * (f * f - 1) = (i * c * c) * (i * c * c) := by
  have hf1 : 1 ≤ f * f := one_le_mul_of_one_le_of_one_le (pos_iff_one_le.mp hf) (pos_iff_one_le.mp hf)
  obtain ⟨g', hg'⟩ : ∃ g' : V, f * f = g' + 1 := ⟨f * f - 1, (tsub_add_cancel_of_le hf1).symm⟩
  rw [hg', add_tsub_cancel_right]
  apply add_right_cancel (b := delta a)
  rw [hs, hg']; ring

/-- A partner of an auxiliary norm with a large strong root is positive. -/
theorem partner_pos (I x y : V) (hI : 2 ≤ I) (h : I * I * x * x + y * y = 1 + I * I * y * y) :
    0 < y := pos_iff_ne_zero.mpr (by
  intro hy0'
  have hp : I * I * x * x = 1 := by simpa only [hy0', mul_zero, zero_mul, add_zero] using h
  have hd : I * I ∣ (1 : V) := ⟨x * x, by simpa only [mul_assoc] using hp.symm⟩
  have hle : I * I ≤ 1 := Arithmetic.le_of_dvd (by simp) hd
  have hIle : I ≤ I * I := le_mul_of_one_le_right (by simp) (le_trans (by simp : (1 : V) ≤ 2) hI)
  exact (not_le_of_gt (lt_of_lt_of_le (by simp : (1 : V) < 2) hI)) (le_trans hIle hle))

private theorem two_le_strong (c i R : V) (hi : 0 < i) (hR : 0 < R) (hhalf : 2 * R < c) :
    2 ≤ i * c * c := by
  have hc2 : 2 ≤ c := le_trans (by
    calc (2 : V) = 2 * 1 := by ring
      _ ≤ 2 * R := mul_le_mul_of_nonneg_left (pos_iff_one_le.mp hR) (by simp)) (le_of_lt hhalf)
  have hc0 : 0 < c := lt_of_lt_of_le (by norm_num) hc2
  calc 2 ≤ c := hc2
    _ ≤ i * c := le_mul_of_one_le_left (Arithmetic.zero_le _) (pos_iff_one_le.mp hi)
    _ ≤ i * c * c := le_mul_of_one_le_right (Arithmetic.zero_le _) (pos_iff_one_le.mp hc0)

/-- The oracle for a free positive partner `y` (package 59). -/
theorem oracle_free (a c R f i T y : V) (hc : 0 < c) (hi : 0 < i) (hf : 0 < f) (hy : 0 < y)
    (hR : 0 < R)
    (hs : (i * c * c) * (i * c * c) + delta a = delta a * (f * f))
    (haux : delta a * (f * f - 1) *
        (absdiff (f * f * (T * c)) (f * f * R + c) * absdiff (f * f * (T * c)) (f * f * R + c)) +
        y * y = 1 + delta a * (f * f - 1) * (y * y)) :
    ∀ m g : V, 0 < m → ycoord m a = c → g * g = 1 + delta a * c * c → 2 * R < c →
      (a + 2) * delta a * delta a < c → m = R := by
  intro m g hm hmy hg hhalf hbig
  have e := ord_eq a c f i hf hs
  have hRabs : absdiff R 0 = R := by simp [absdiff]
  have haux' : (i * c * c) * (i * c * c) * absdiff (f * f * (T * c + 0)) (f * f * R + c) *
      absdiff (f * f * (T * c + 0)) (f * f * R + c) + y * y = 1 + (i * c * c) * (i * c * c) * y * y := by
    rw [add_zero, ← e]; linear_combination haux
  have h := AdaptiveGap85GenericSignedHalfIndex.signed_half_index_of_facts a c g f i T R 0 y m
    hc hi hf hm hy hmy (by rw [hRabs]; exact hR) (by rw [hRabs]; exact hhalf) hg hs hbig haux'
  rwa [hRabs] at h

/-- The oracle for the partner `y = V + u` (package 56). -/
theorem oracle_gap (a c R f i T u : V) (hc : 0 < c) (hi : 0 < i) (hf : 0 < f) (hR : 0 < R)
    (hs : (i * c * c) * (i * c * c) + delta a = delta a * (f * f))
    (haux : delta a * (f * f - 1) *
        (absdiff (f * f * (T * c)) (f * f * R + c) * absdiff (f * f * (T * c)) (f * f * R + c)) +
        absdiff (f * f * (T * c) + u) (f * f * R + c) * absdiff (f * f * (T * c) + u) (f * f * R + c) =
      1 + delta a * (f * f - 1) *
        (absdiff (f * f * (T * c) + u) (f * f * R + c) * absdiff (f * f * (T * c) + u) (f * f * R + c))) :
    ∀ m g : V, 0 < m → ycoord m a = c → g * g = 1 + delta a * c * c → 2 * R < c →
      (a + 2) * delta a * delta a < c → m = R := by
  intro m g hm hmy hg hhalf hbig
  have e := ord_eq a c f i hf hs
  set yv : V := absdiff (f * f * (T * c) + u) (f * f * R + c) with hyv
  have hRabs : absdiff R 0 = R := by simp [absdiff]
  have haux' : (i * c * c) * (i * c * c) * absdiff (f * f * (T * c + 0)) (f * f * R + c) *
      absdiff (f * f * (T * c + 0)) (f * f * R + c) + yv * yv = 1 + (i * c * c) * (i * c * c) * yv * yv := by
    rw [add_zero, ← e]; linear_combination haux
  have hyv0 : 0 < yv := partner_pos (i * c * c) _ yv (two_le_strong c i R hi hR hhalf) haux'
  have h := AdaptiveGap85GenericSignedHalfIndex.signed_half_index_of_facts a c g f i T R 0 yv m
    hc hi hf hm hyv0 hmy (by rw [hRabs]; exact hR) (by rw [hRabs]; exact hhalf) hg hs hbig haux'
  rwa [hRabs] at h

/-- The oracle for the old ordinate `cTf − (f²R + c)` with partner `y = V + u` (package 47). -/
theorem oracle_old (a c R f i T u : V) (hc : 0 < c) (hi : 0 < i) (hf : 0 < f) (hR : 0 < R)
    (hs : (i * c * c) * (i * c * c) + delta a = delta a * (f * f))
    (haux : delta a * (f * f - 1) *
        (absdiff (c * T * f) (f * f * R + c) * absdiff (c * T * f) (f * f * R + c)) +
        absdiff (c * T * f + u) (f * f * R + c) * absdiff (c * T * f + u) (f * f * R + c) =
      1 + delta a * (f * f - 1) *
        (absdiff (c * T * f + u) (f * f * R + c) * absdiff (c * T * f + u) (f * f * R + c))) :
    ∀ m g : V, 0 < m → ycoord m a = c → g * g = 1 + delta a * c * c → 2 * R < c →
      (a + 2) * delta a * delta a < c → m = R := by
  intro m g hm hmy hg hhalf hbig
  have e := ord_eq a c f i hf hs
  set yv : V := absdiff (c * T * f + u) (f * f * R + c) with hyv
  have haux' : (i * c * c) * (i * c * c) * absdiff (c * T * f) (f * f * R + c) *
      absdiff (c * T * f) (f * f * R + c) + yv * yv = 1 + (i * c * c) * (i * c * c) * yv * yv := by
    rw [← e]; linear_combination haux
  have hyv0 : 0 < yv := partner_pos (i * c * c) _ yv (two_le_strong c i R hi hR hhalf) haux'
  exact OrdinaryBlankSignedIndex.signed_half_index_blank a c g f i T R yv m hc hi hf hm hyv0 hmy hR
    hhalf hg hs hbig haux'

end Short15Index

#print axioms Short15Index.window_ring0
#print axioms Short15Index.index_window'
#print axioms Short15Index.close_neg
#print axioms Short15Index.minus_false
#print axioms Short15Index.oracle_free
#print axioms Short15Index.oracle_gap
#print axioms Short15Index.oracle_old
