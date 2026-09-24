import Diophantine.Paper1978.Theorems12
import Diophantine.Paper1978.Combining

/-!
# Jones 1978, Lemma 3.4

With `M(i) = 1 + (1+i)β`, `T = R − eM(s)`, `P = R − bM(w)` (integers) and

* U2 `R = θ(1+β)`, U3 `M(u) ∣ hM(v) − x`, U4 `(hM(v) − R)² + x² < β`,
* `A(y) = [3(s+w)² + 9w + 3s − 2y]² + [M(y)²(1 + (R−T−P)²)(β − T² − P²) − (R−T−P)² − (g+1)M(y)²]²`,
* `B(y) = [3(s+w)² + 9w + 3s + 2 − 2y]² + [M(y)²(1 + (R−TP)²)(β − T² − P²) − (R−TP)² − (g+1)M(y)²]²`,
* `C(y) = 3g + 2 − y`,

> **Lemma 3.4.** For positive integers `n, x`: `x ∈ Wₙ` iff there are nonnegative integers
> `u, v, h, R, β, θ` with `J(u,v) = n` and
> `U2 ∧ U3 ∧ U4 ∧ (∀ y < 3n)(∃ b, e, g, s, w)[A(y)B(y)C(y) = 0]`.

The residue facts behind the proof (`T = S(R,β,s)` from `T² < β`, `S(R,β,3i) = T + P` from
`(T+P)² < 2β`, etc.) hold for every `β ≥ 1`; the article's "provided `β` is sufficiently
large" concerns only the converse direction, where `β` is chosen.
-/

namespace Jones1978

open Finset

/-- `M(y)` as an integer polynomial. -/
def Mz (β y : ℕ) : ℤ := 1 + (1 + y) * β

theorem Mz_eq (β y : ℕ) : Mz β y = (Mg β y : ℤ) := by rw [Mg_cast]; rfl

/-- `T = R − e M(s)`. -/
def Tz (R β e s : ℕ) : ℤ := R - e * Mz β s

/-- The polynomial `A(y)`. -/
def Apoly (R β y b e g s w : ℕ) : ℤ :=
  (3 * ((s : ℤ) + w) ^ 2 + 9 * w + 3 * s - 2 * y) ^ 2 +
    (Mz β y ^ 2 * (1 + ((R : ℤ) - Tz R β e s - Tz R β b w) ^ 2) *
        ((β : ℤ) - Tz R β e s ^ 2 - Tz R β b w ^ 2) -
      ((R : ℤ) - Tz R β e s - Tz R β b w) ^ 2 - ((g : ℤ) + 1) * Mz β y ^ 2) ^ 2

/-- The polynomial `B(y)`. -/
def Bpoly (R β y b e g s w : ℕ) : ℤ :=
  (3 * ((s : ℤ) + w) ^ 2 + 9 * w + 3 * s + 2 - 2 * y) ^ 2 +
    (Mz β y ^ 2 * (1 + ((R : ℤ) - Tz R β e s * Tz R β b w) ^ 2) *
        ((β : ℤ) - Tz R β e s ^ 2 - Tz R β b w ^ 2) -
      ((R : ℤ) - Tz R β e s * Tz R β b w) ^ 2 - ((g : ℤ) + 1) * Mz β y ^ 2) ^ 2

/-- The polynomial `C(y)`. -/
def Cpoly (g y : ℕ) : ℤ := 3 * g + 2 - y

/-- U2 ∧ U3 ∧ U4. -/
def U234 (x u v h R β θ : ℕ) : Prop :=
  R = θ * (1 + β) ∧ (Mg β u : ℤ) ∣ h * Mg β v - x ∧ (h * (Mg β v : ℤ) - R) ^ 2 + x ^ 2 < β

/-- The condition (3.4). -/
def Cond34 (n x u v h R β θ : ℕ) : Prop :=
  J u v = n ∧ U234 x u v h R β θ ∧
    ∀ y < 3 * n, ∃ b e g s w, Apoly R β y b e g s w * Bpoly R β y b e g s w * Cpoly g y = 0

/-! ### Residue facts -/

theorem Tz_modEq (R β e s : ℕ) : (R : ℤ) ≡ Tz R β e s [ZMOD Mg β s] := by
  unfold Tz
  rw [Mz_eq]
  exact (Int.modEq_iff_dvd.2 ⟨-e, by ring⟩)

/-- `T² < β` forces `T = S(R, β, s)`. -/
theorem S_eq_Tz {R β e s : ℕ} (h : Tz R β e s ^ 2 < β) : S R β s = Tz R β e s := by
  apply S_eq_of_sq_lt (Tz_modEq R β e s)
  have h1 := Mg_ge β s
  have h2 : (0 : ℤ) ≤ β := by positivity
  nlinarith

/-- `S(R, β, 0) = 0` from U2. -/
theorem S_zero_of_U2 {R β θ : ℕ} (h : R = θ * (1 + β)) : S R β 0 = 0 := by
  apply S_eq_of_sq_lt
  · rw [h]
    refine Int.modEq_iff_dvd.2 ⟨-θ, ?_⟩
    rw [Mg_cast]; push_cast; ring
  · have := Mg_pos β 0
    have : (0 : ℤ) < Mg β 0 := by exact_mod_cast this
    nlinarith

/-- `2|TP| ≤ T² + P²`. -/
theorem two_abs_mul_le (T P : ℤ) : 4 * (T * P) ^ 2 ≤ (T ^ 2 + P ^ 2) ^ 2 := by
  nlinarith [sq_nonneg (T ^ 2 - P ^ 2)]

/-! ### `A(y) = 0` and `B(y) = 0` -/

/-- `A(y) = 0` iff `y = 3 J(s,w)`, `M(y) ∣ R − T − P` and `T² + P² < β` (for some `g`). -/
theorem Apoly_eq_zero {R β y b e g s w : ℕ} (h : Apoly R β y b e g s w = 0) :
    y = 3 * J s w ∧ (Mg β y : ℤ) ∣ (R : ℤ) - Tz R β e s - Tz R β b w ∧
      Tz R β e s ^ 2 + Tz R β b w ^ 2 < β := by
  unfold Apoly at h
  obtain ⟨h1, h2⟩ := sq_add_sq_eq_zero.1 h
  refine ⟨?_, ?_⟩
  · have := two_J s w
    have h1' : ((3 * (s + w) ^ 2 + 9 * w + 3 * s : ℕ) : ℤ) = ((2 * y : ℕ) : ℤ) := by
      push_cast; linarith
    have h1'' : 3 * (s + w) ^ 2 + 9 * w + 3 * s = 2 * y := by exact_mod_cast h1'
    omega
  · have hM : (Mz β y) ≠ 0 := by rw [Mz_eq]; exact_mod_cast (Mg_pos β y).ne'
    have := (lemma_2_2 hM ((R : ℤ) - Tz R β e s - Tz R β b w)
      ((β : ℤ) - Tz R β e s ^ 2 - Tz R β b w ^ 2)).2 ⟨g, by linarith⟩
    rw [Mz_eq] at this
    exact ⟨this.1, by linarith [this.2]⟩

theorem Bpoly_eq_zero {R β y b e g s w : ℕ} (h : Bpoly R β y b e g s w = 0) :
    y = 3 * J s w + 1 ∧ (Mg β y : ℤ) ∣ (R : ℤ) - Tz R β e s * Tz R β b w ∧
      Tz R β e s ^ 2 + Tz R β b w ^ 2 < β := by
  unfold Bpoly at h
  obtain ⟨h1, h2⟩ := sq_add_sq_eq_zero.1 h
  refine ⟨?_, ?_⟩
  · have := two_J s w
    have h1' : ((3 * (s + w) ^ 2 + 9 * w + 3 * s + 2 : ℕ) : ℤ) = ((2 * y : ℕ) : ℤ) := by
      push_cast; linarith
    have h1'' : 3 * (s + w) ^ 2 + 9 * w + 3 * s + 2 = 2 * y := by exact_mod_cast h1'
    omega
  · have hM : (Mz β y) ≠ 0 := by rw [Mz_eq]; exact_mod_cast (Mg_pos β y).ne'
    have := (lemma_2_2 hM ((R : ℤ) - Tz R β e s * Tz R β b w)
      ((β : ℤ) - Tz R β e s ^ 2 - Tz R β b w ^ 2)).2 ⟨g, by linarith⟩
    rw [Mz_eq] at this
    exact ⟨this.1, by linarith [this.2]⟩

/-- Conversely, `A(3J(s,w)) = 0` for suitable `g` when `M(y) ∣ R − T − P` and `T² + P² < β`. -/
theorem exists_Apoly_eq_zero {R β b e s w : ℕ}
    (hdvd : (Mg β (3 * J s w) : ℤ) ∣ (R : ℤ) - Tz R β e s - Tz R β b w)
    (hlt : Tz R β e s ^ 2 + Tz R β b w ^ 2 < β) :
    ∃ g, Apoly R β (3 * J s w) b e g s w = 0 ∧
      (g : ℤ) + 1 ≤ (1 + ((R : ℤ) - Tz R β e s - Tz R β b w) ^ 2) *
        ((β : ℤ) - Tz R β e s ^ 2 - Tz R β b w ^ 2) := by
  have hM : (Mz β (3 * J s w)) ≠ 0 := by rw [Mz_eq]; exact_mod_cast (Mg_pos β _).ne'
  obtain ⟨g, hg⟩ := (lemma_2_2 hM ((R : ℤ) - Tz R β e s - Tz R β b w)
    ((β : ℤ) - Tz R β e s ^ 2 - Tz R β b w ^ 2)).1 ⟨by rw [Mz_eq]; exact hdvd, by linarith⟩
  refine ⟨g, ?_, ?_⟩
  swap
  · -- `(g+1) M² ≤ M²(1+v²)w'`
    have hM2 : 0 < Mz β (3 * J s w) ^ 2 := by positivity
    have h1 : ((g : ℤ) + 1) * Mz β (3 * J s w) ^ 2 ≤
        Mz β (3 * J s w) ^ 2 * ((1 + ((R : ℤ) - Tz R β e s - Tz R β b w) ^ 2) *
          ((β : ℤ) - Tz R β e s ^ 2 - Tz R β b w ^ 2)) := by
      have := sq_nonneg ((R : ℤ) - Tz R β e s - Tz R β b w)
      nlinarith
    rw [mul_comm ((g : ℤ) + 1)] at h1
    exact le_of_mul_le_mul_left h1 hM2
  unfold Apoly
  have h1 : 3 * ((s : ℤ) + w) ^ 2 + 9 * w + 3 * s - 2 * ((3 * J s w : ℕ) : ℤ) = 0 := by
    have := two_J s w
    have : ((2 * J s w : ℕ) : ℤ) = (((s + w) ^ 2 + 3 * w + s : ℕ) : ℤ) := by rw [this]
    push_cast at this ⊢
    linarith
  rw [h1]
  have hb : Mz β (3 * J s w) ^ 2 * (1 + ((R : ℤ) - Tz R β e s - Tz R β b w) ^ 2) *
      ((β : ℤ) - Tz R β e s ^ 2 - Tz R β b w ^ 2) -
      ((R : ℤ) - Tz R β e s - Tz R β b w) ^ 2 - ((g : ℤ) + 1) * Mz β (3 * J s w) ^ 2 = 0 := by
    linarith
  rw [hb]; ring

theorem exists_Bpoly_eq_zero {R β b e s w : ℕ}
    (hdvd : (Mg β (3 * J s w + 1) : ℤ) ∣ (R : ℤ) - Tz R β e s * Tz R β b w)
    (hlt : Tz R β e s ^ 2 + Tz R β b w ^ 2 < β) :
    ∃ g, Bpoly R β (3 * J s w + 1) b e g s w = 0 ∧
      (g : ℤ) + 1 ≤ (1 + ((R : ℤ) - Tz R β e s * Tz R β b w) ^ 2) *
        ((β : ℤ) - Tz R β e s ^ 2 - Tz R β b w ^ 2) := by
  have hM : (Mz β (3 * J s w + 1)) ≠ 0 := by rw [Mz_eq]; exact_mod_cast (Mg_pos β _).ne'
  obtain ⟨g, hg⟩ := (lemma_2_2 hM ((R : ℤ) - Tz R β e s * Tz R β b w)
    ((β : ℤ) - Tz R β e s ^ 2 - Tz R β b w ^ 2)).1 ⟨by rw [Mz_eq]; exact hdvd, by linarith⟩
  refine ⟨g, ?_, ?_⟩
  swap
  · have hM2 : 0 < Mz β (3 * J s w + 1) ^ 2 := by positivity
    have h1 : ((g : ℤ) + 1) * Mz β (3 * J s w + 1) ^ 2 ≤
        Mz β (3 * J s w + 1) ^ 2 * ((1 + ((R : ℤ) - Tz R β e s * Tz R β b w) ^ 2) *
          ((β : ℤ) - Tz R β e s ^ 2 - Tz R β b w ^ 2)) := by
      have := sq_nonneg ((R : ℤ) - Tz R β e s * Tz R β b w)
      nlinarith
    rw [mul_comm ((g : ℤ) + 1)] at h1
    exact le_of_mul_le_mul_left h1 hM2
  unfold Bpoly
  have h1 : 3 * ((s : ℤ) + w) ^ 2 + 9 * w + 3 * s + 2 - 2 * ((3 * J s w + 1 : ℕ) : ℤ) = 0 := by
    have := two_J s w
    have : ((2 * J s w : ℕ) : ℤ) = (((s + w) ^ 2 + 3 * w + s : ℕ) : ℤ) := by rw [this]
    push_cast at this ⊢
    linarith
  rw [h1]
  have hb : Mz β (3 * J s w + 1) ^ 2 * (1 + ((R : ℤ) - Tz R β e s * Tz R β b w) ^ 2) *
      ((β : ℤ) - Tz R β e s ^ 2 - Tz R β b w ^ 2) -
      ((R : ℤ) - Tz R β e s * Tz R β b w) ^ 2 - ((g : ℤ) + 1) * Mz β (3 * J s w + 1) ^ 2 = 0 := by
    linarith
  rw [hb]; ring

/-! ### Sufficiency -/

/-- U2–U4 give `S(R,β,0) = 0` and `S(R,β,u) = S(R,β,v) + x`. -/
theorem S_of_U234 {x u v h R β θ : ℕ} (hU : U234 x u v h R β θ) :
    S R β 0 = 0 ∧ S R β u = S R β v + x := by
  obtain ⟨hU2, hU3, hU4⟩ := hU
  have h0 := S_zero_of_U2 hU2
  refine ⟨h0, ?_⟩
  -- `S(v) = R − hM(v)`
  have hSv : S R β v = (R : ℤ) - h * Mg β v := by
    apply S_eq_of_sq_lt (Int.modEq_iff_dvd.2 ⟨-h, by ring⟩)
    have h1 := Mg_ge β v
    have h2 : (0 : ℤ) ≤ β := by positivity
    have h3 : ((h : ℤ) * Mg β v - R) ^ 2 < β := by have := sq_nonneg (x : ℤ); linarith
    have h4 : ((R : ℤ) - h * Mg β v) ^ 2 = ((h : ℤ) * Mg β v - R) ^ 2 := by ring
    rw [h4]; nlinarith
  rw [hSv]
  -- `x + R − hM(v) ≡ R (mod M(u))`
  have hcong : (R : ℤ) ≡ (R : ℤ) - h * Mg β v + x [ZMOD Mg β u] := by
    refine Int.modEq_iff_dvd.2 ?_
    rw [show (R : ℤ) - h * Mg β v + x - R = -((h : ℤ) * Mg β v - x) by ring]
    exact (dvd_neg).2 hU3
  have hsq : 4 * ((R : ℤ) - h * Mg β v + x) ^ 2 < 8 * β := by
    have h3 : ((R : ℤ) - h * Mg β v) ^ 2 + x ^ 2 < β := by
      have h4 : ((R : ℤ) - h * Mg β v) ^ 2 = ((h : ℤ) * Mg β v - R) ^ 2 := by ring
      rw [h4]; exact hU4
    nlinarith [sq_nonneg ((R : ℤ) - h * Mg β v - x)]
  rcases Nat.eq_zero_or_pos u with rfl | hu
  · -- `u = 0`: the residue `x + S(v)` is `≡ 0` and small, hence `0`
    rw [h0]
    have hM : (Mg β 0 : ℤ) = 1 + β := by rw [Mg_cast]; push_cast; ring
    have hdvd : (Mg β 0 : ℤ) ∣ (R : ℤ) - h * Mg β v + x := by
      have := (Int.modEq_iff_dvd.1 hcong)
      have h1 : (Mg β 0 : ℤ) ∣ (R : ℤ) := by
        rw [hU2, hM]; push_cast; exact ⟨θ, by ring⟩
      have := dvd_add this h1
      rwa [sub_add_cancel] at this
    have habs : |(R : ℤ) - h * Mg β v + x| < Mg β 0 := by
      apply abs_lt_of_sq_lt_sq _ (by rw [hM]; positivity)
      rw [hM]
      have : (0 : ℤ) ≤ β := by positivity
      nlinarith
    have := Int.eq_zero_of_abs_lt_dvd hdvd habs
    linarith
  · apply S_eq_of_sq_lt hcong
    have h1 := Mg_ge_of_pos (β := β) hu
    have h2 : (0 : ℤ) ≤ β := by positivity
    nlinarith

theorem cond32_of_cond34 {n x u v h R β θ : ℕ} (hc : Cond34 n x u v h R β θ) :
    Cond32 n x u v R β := by
  obtain ⟨hJ, hU, hABC⟩ := hc
  obtain ⟨h0, huv⟩ := S_of_U234 hU
  refine ⟨hJ, h0, huv, fun i hi => ⟨?_, ?_⟩⟩
  · -- `y = 3i`: only `A(y) = 0` is possible
    obtain ⟨b, e, g, s, w, hprod⟩ := hABC (3 * i) (by omega)
    rcases mul_eq_zero.1 hprod with hAB | hC
    · rcases mul_eq_zero.1 hAB with hA | hB
      · obtain ⟨hy, hdvd, hlt⟩ := Apoly_eq_zero hA
        have hJ' : J s w = i := by omega
        obtain ⟨rfl, rfl⟩ := J_eq_iff.1 hJ'
        have hT : S R β (K i) = Tz R β e (K i) :=
          S_eq_Tz (by nlinarith [sq_nonneg (Tz R β b (L i))])
        have hP : S R β (L i) = Tz R β b (L i) :=
          S_eq_Tz (by nlinarith [sq_nonneg (Tz R β e (K i))])
        rw [hT, hP]
        rcases Nat.eq_zero_or_pos i with rfl | hi0
        · -- `i = 0`: `s = w = 0`, `T = P = 0`
          simp only [K_zero, L_zero, mul_zero] at hT hP ⊢
          rw [h0] at hT hP
          rw [h0, ← hT, ← hP]; ring
        · apply S_eq_of_sq_lt
          · exact Int.modEq_iff_dvd.2 (by
              rw [show Tz R β e (K i) + Tz R β b (L i) - R =
                -((R : ℤ) - Tz R β e (K i) - Tz R β b (L i)) by ring]
              exact (dvd_neg).2 hdvd)
          · have h1 := Mg_ge_of_ge (β := β) (show 3 ≤ 3 * i by omega)
            have h1' : (1 + 4 * β : ℤ) ≤ Mg β (3 * i) := by push_cast at h1; linarith
            have h2 : (0 : ℤ) ≤ β := by positivity
            have h3 : 4 * (Tz R β e (K i) + Tz R β b (L i)) ^ 2 < 8 * β := by
              nlinarith [sq_nonneg (Tz R β e (K i) - Tz R β b (L i))]
            have h4 : (1 + 4 * (β : ℤ)) ^ 2 ≤ (Mg β (3 * i) : ℤ) ^ 2 :=
              pow_le_pow_left₀ (by positivity) h1' 2
            nlinarith
      · obtain ⟨hy, -, -⟩ := Bpoly_eq_zero hB
        omega
    · unfold Cpoly at hC; omega
  · -- `y = 3i + 1`: only `B(y) = 0` is possible
    obtain ⟨b, e, g, s, w, hprod⟩ := hABC (3 * i + 1) (by omega)
    rcases mul_eq_zero.1 hprod with hAB | hC
    · rcases mul_eq_zero.1 hAB with hA | hB
      · obtain ⟨hy, -, -⟩ := Apoly_eq_zero hA
        omega
      · obtain ⟨hy, hdvd, hlt⟩ := Bpoly_eq_zero hB
        have hJ' : J s w = i := by omega
        obtain ⟨rfl, rfl⟩ := J_eq_iff.1 hJ'
        have hT : S R β (K i) = Tz R β e (K i) :=
          S_eq_Tz (by nlinarith [sq_nonneg (Tz R β b (L i))])
        have hP : S R β (L i) = Tz R β b (L i) :=
          S_eq_Tz (by nlinarith [sq_nonneg (Tz R β e (K i))])
        rw [hT, hP]
        apply S_eq_of_sq_lt
        · exact Int.modEq_iff_dvd.2 (by
            rw [show Tz R β e (K i) * Tz R β b (L i) - R =
              -((R : ℤ) - Tz R β e (K i) * Tz R β b (L i)) by ring]
            exact (dvd_neg).2 hdvd)
        · have h1 := Mg_ge β (3 * i + 1)
          have h2 : (0 : ℤ) ≤ β := by positivity
          have h3 := two_abs_mul_le (Tz R β e (K i)) (Tz R β b (L i))
          have h4 : (0 : ℤ) ≤ Tz R β e (K i) ^ 2 + Tz R β b (L i) ^ 2 := by positivity
          nlinarith
    · unfold Cpoly at hC; omega

/-! ### Necessity, with size bounds on the witnesses -/

set_option maxHeartbeats 4000000 in
/-- Lemma 3.4, necessity, with all witnesses `b, e, g, s, w` below `3n + R³` (as needed
for Lemma 3.5). -/
theorem cond34_of_mem_bounded {n x : ℕ} (hn : 0 < n) (hx : 0 < x) (hW : x ∈ W n) :
    ∃ u v h R β θ, J u v = n ∧ U234 x u v h R β θ ∧
      ∀ y < 3 * n, ∃ b e g s w, b < 3 * n + R ^ 3 ∧ e < 3 * n + R ^ 3 ∧ g < 3 * n + R ^ 3 ∧
        s < 3 * n + R ^ 3 ∧ w < 3 * n + R ^ 3 ∧
        Apoly R β y b e g s w * Bpoly R β y b e g s w * Cpoly g y = 0 := by
  obtain ⟨X, hX⟩ := hW
  -- the values to be coded and their size
  obtain ⟨V, hV⟩ : ∃ V : ℕ → ℤ, V = fun k => P k X := ⟨_, rfl⟩
  have hXV : V (K n) = V (L n) + x := by rw [hV]; exact hX
  have hV0 : V 0 = 0 := by rw [hV]; exact P_zero X
  have hVadd : ∀ i, V (3 * i) = V (K i) + V (L i) := fun i => by rw [hV]; exact P_add' i X
  have hVmul : ∀ i, V (3 * i + 1) = V (K i) * V (L i) := fun i => by rw [hV]; exact P_mul i X
  obtain ⟨Vb, hVb⟩ : ∃ Vb : ℕ, Vb = 1 + ∑ k ∈ range (3 * n + 2), (V k).natAbs := ⟨_, rfl⟩
  have hVabs : ∀ k ≤ 3 * n + 1, |V k| < Vb := by
    intro k hk
    have h1 := Finset.single_le_sum (f := fun k => ((V k).natAbs : ℤ))
      (fun _ _ => by positivity) (Finset.mem_range.2 (by omega : k < 3 * n + 2))
    have h3 : (Vb : ℤ) = 1 + ∑ k ∈ range (3 * n + 2), ((V k).natAbs : ℤ) := by
      rw [hVb]; push_cast; ring
    simp only [Int.natCast_natAbs] at h1
    linarith
  have hVb1 : 1 ≤ Vb := by omega
  -- `β`
  obtain ⟨βmin, hβmin⟩ : ∃ βmin : ℕ, βmin = 1 + x ^ 2 + 2 * ∑ k ∈ range (3 * n + 2), (V k).natAbs ^ 2 :=
    ⟨_, rfl⟩
  obtain ⟨β, hβge, hβdvd, hβT⟩ := exists_good_β V (3 * n + 1) βmin
  have hβZ : (βmin : ℤ) ≤ β := by exact_mod_cast hβge
  have hβminZ : (βmin : ℤ) = 1 + x ^ 2 + 2 * ∑ k ∈ range (3 * n + 2), ((V k).natAbs : ℤ) ^ 2 := by
    rw [hβmin]; push_cast; ring
  have hVsq : ∀ k ≤ 3 * n + 1, (V k) ^ 2 ≤ ∑ k ∈ range (3 * n + 2), ((V k).natAbs : ℤ) ^ 2 := by
    intro k hk
    have := Finset.single_le_sum (f := fun k => ((V k).natAbs : ℤ) ^ 2)
      (fun _ _ => by positivity) (Finset.mem_range.2 (by omega : k < 3 * n + 2))
    simpa [Int.natCast_natAbs, sq_abs] using this
  have hsum_lt : ∀ k k', k ≤ 3 * n + 1 → k' ≤ 3 * n + 1 → V k ^ 2 + V k' ^ 2 < β := by
    intro k k' hk hk'
    have := hVsq k hk
    have := hVsq k' hk'
    have : (0 : ℤ) ≤ x ^ 2 := by positivity
    linarith
  have hβ2 : 2 ≤ β := by
    have : 1 + x ^ 2 ≤ βmin := by rw [hβmin]; omega
    have : 1 ≤ x ^ 2 := Nat.one_le_pow _ _ hx
    omega
  -- `R`
  obtain ⟨Rmin, hRmin⟩ : ∃ Rmin : ℕ, Rmin = Vb ^ 2 + 10 * β + 1 := ⟨_, rfl⟩
  obtain ⟨R, hR, hS⟩ := exists_S_eq_of_β V (3 * n + 1) Rmin β hβdvd hβT
  have hRV : Vb < R := by have : Vb ≤ Vb ^ 2 := Nat.le_self_pow (by norm_num) Vb; omega
  have hRV2 : Vb ^ 2 ≤ R := by omega
  have hR10 : 10 * β < R := by omega
  have hR1 : 1 ≤ R := by omega
  have hVle : ∀ k ≤ 3 * n + 1, V k ≤ R := by
    intro k hk
    have h1 := hVabs k hk
    have h2 : (Vb : ℤ) < R := by exact_mod_cast hRV
    have h4 : V k ≤ |V k| := le_abs_self _
    linarith
  have hVR : ∀ k ≤ 3 * n + 1, |V k| < R := by
    intro k hk
    have h2 : (Vb : ℤ) < R := by exact_mod_cast hRV
    linarith [hVabs k hk]
  have hVVR : ∀ k k', k ≤ 3 * n + 1 → k' ≤ 3 * n + 1 → |V k * V k'| ≤ R := by
    intro k k' hk hk'
    rw [abs_mul]
    have h1 := hVabs k hk
    have h2 := hVabs k' hk'
    have h3 : (Vb : ℤ) ^ 2 ≤ R := by exact_mod_cast hRV2
    have := abs_nonneg (V k)
    have := abs_nonneg (V k')
    nlinarith
  have hRZ : R ≤ 3 * n + R ^ 3 := by
    have : R ≤ R ^ 3 := Nat.le_self_pow (by norm_num) R
    omega
  -- the witnesses
  have h0 : S R β 0 = 0 := by rw [hS 0 (by omega)]; exact hV0
  have hM0 : (Mg β 0 : ℤ) ∣ R := by
    have := (S_spec R β 0).1
    rw [h0] at this
    simpa using (Int.modEq_iff_dvd.1 this.symm)
  obtain ⟨θ, hθ⟩ : ∃ θ : ℕ, R = θ * (1 + β) := by
    have : Mg β 0 ∣ R := by exact_mod_cast hM0
    obtain ⟨θ, hθ⟩ := this
    exact ⟨θ, by rw [hθ]; unfold Mg; ring⟩
  -- the quotients `(R − S(k)) / M(k)`, all below `R`
  have hdivM : ∀ k ≤ 3 * n + 1, ∃ q : ℕ, (R : ℤ) - V k = q * Mg β k ∧ q < R := by
    intro k hk
    have hc := (S_spec R β k).1
    rw [hS k hk] at hc
    obtain ⟨q, hq⟩ := Int.modEq_iff_dvd.1 hc.symm
    have hM : (0 : ℤ) < Mg β k := by exact_mod_cast Mg_pos β k
    have hM2 : (2 : ℤ) ≤ Mg β k := by
      have := Mg_ge β k
      have : (2 : ℤ) ≤ β := by exact_mod_cast hβ2
      linarith
    have hq0 : 0 ≤ q := by
      by_contra hneg
      push Not at hneg
      have : (Mg β k : ℤ) * q < 0 := mul_neg_of_pos_of_neg hM hneg
      have := hVle k hk
      linarith
    refine ⟨q.toNat, by rw [Int.toNat_of_nonneg hq0, hq]; ring, ?_⟩
    have hqR : q < R := by
      by_contra hcon
      push Not at hcon
      have h1 : (R : ℤ) * 2 ≤ Mg β k * q := by nlinarith
      have h2 := hVR k hk
      have h3 : -|V k| ≤ V k := neg_abs_le _
      linarith
    have : (q.toNat : ℤ) = q := Int.toNat_of_nonneg hq0
    have : (q.toNat : ℤ) < R := by rw [this]; exact hqR
    exact_mod_cast this
  have hKn : K n ≤ 3 * n + 1 := by have := K_le n; omega
  have hLn : L n ≤ 3 * n + 1 := by have := L_le n; omega
  obtain ⟨h, hh, -⟩ := hdivM (L n) hLn
  refine ⟨K n, L n, h, R, β, θ, J_K_L n, ⟨hθ, ?_, ?_⟩, fun y hy => ?_⟩
  · -- U3
    have : (h : ℤ) * Mg β (L n) - x = R - V (K n) := by
      have hXZ : V (K n) = V (L n) + x := hXV
      linarith
    rw [this]
    have hc := (S_spec R β (K n)).1
    rw [hS (K n) hKn] at hc
    exact Int.modEq_iff_dvd.1 hc.symm
  · -- U4
    have : (h : ℤ) * Mg β (L n) - R = -V (L n) := by linarith
    rw [this]
    have := hVsq (L n) hLn
    have : (0 : ℤ) ≤ ∑ k ∈ range (3 * n + 2), ((V k).natAbs : ℤ) ^ 2 := by positivity
    nlinarith
  · -- the `∀ y < 3n` conditions
    have hmod : y % 3 = 0 ∨ y % 3 = 1 ∨ y % 3 = 2 := by omega
    have hn3 : n ≤ 3 * n + R ^ 3 := by omega
    rcases hmod with hm | hm | hm
    · obtain ⟨i, rfl⟩ : ∃ i, y = 3 * i := ⟨y / 3, by omega⟩
      have hi : i < n := by omega
      have hKi : K i ≤ 3 * n + 1 := by have := K_le i; omega
      have hLi : L i ≤ 3 * n + 1 := by have := L_le i; omega
      obtain ⟨e, he, heR⟩ := hdivM (K i) hKi
      obtain ⟨b, hb, hbR⟩ := hdivM (L i) hLi
      have hT : Tz R β e (K i) = V (K i) := by unfold Tz; rw [Mz_eq]; linarith
      have hP : Tz R β b (L i) = V (L i) := by unfold Tz; rw [Mz_eq]; linarith
      have hy : 3 * i = 3 * J (K i) (L i) := by rw [J_K_L]
      rw [hy]
      obtain ⟨g, hg, hgle⟩ := exists_Apoly_eq_zero (R := R) (β := β) (b := b) (e := e) (s := K i) (w := L i)
        (by
          rw [hT, hP, J_K_L]
          have hc := (S_spec R β (3 * i)).1
          rw [hS (3 * i) (by omega)] at hc
          have hV3 : V (3 * i) = V (K i) + V (L i) := hVadd i
          rw [show (R : ℤ) - V (K i) - V (L i) = R - V (3 * i) by rw [hV3]; ring]
          exact Int.modEq_iff_dvd.1 hc.symm)
        (by rw [hT, hP]; exact hsum_lt _ _ hKi hLi)
      refine ⟨b, e, g, K i, L i, by omega, by omega, ?_, by have := K_le i; omega,
        by have := L_le i; omega, by rw [hg]; ring⟩
      -- `g + 1 ≤ (1 + v²) w' ≤ (1 + 9R²) β < R³`
      rw [hT, hP] at hgle
      have hv : |(R : ℤ) - V (K i) - V (L i)| ≤ 3 * R := by
        have h1 := abs_lt.1 (hVR (K i) hKi)
        have h2 := abs_lt.1 (hVR (L i) hLi)
        rw [abs_le]
        constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
      have hv2 : ((R : ℤ) - V (K i) - V (L i)) ^ 2 ≤ 9 * (R : ℤ) ^ 2 := by
        have := sq_le_sq' (abs_le.1 hv).1 (abs_le.1 hv).2
        calc ((R : ℤ) - V (K i) - V (L i)) ^ 2 ≤ (3 * (R : ℤ)) ^ 2 := this
          _ = 9 * (R : ℤ) ^ 2 := by ring
      have hw' : (β : ℤ) - V (K i) ^ 2 - V (L i) ^ 2 ≤ β := by
        have := sq_nonneg (V (K i)); have := sq_nonneg (V (L i)); linarith
      have hw'0 : 0 ≤ (β : ℤ) - V (K i) ^ 2 - V (L i) ^ 2 := by
        have := hsum_lt _ _ hKi hLi; linarith
      have hR2 : (0 : ℤ) < (R : ℤ) ^ 2 := by positivity
      have hR3 : 10 * (β : ℤ) * R ^ 2 < (R : ℤ) ^ 3 := by
        have h1 : (10 * β : ℤ) < R := by exact_mod_cast hR10
        calc 10 * (β : ℤ) * R ^ 2 < R * R ^ 2 := mul_lt_mul_of_pos_right h1 hR2
          _ = (R : ℤ) ^ 3 := by ring
      have hβR : (β : ℤ) ≤ β * R ^ 2 := le_mul_of_one_le_right (by positivity) (by linarith)
      have hgZ : (g : ℤ) < (R : ℤ) ^ 3 := by
        have h1 : (1 + ((R : ℤ) - V (K i) - V (L i)) ^ 2) * ((β : ℤ) - V (K i) ^ 2 - V (L i) ^ 2)
            ≤ (1 + 9 * (R : ℤ) ^ 2) * β := by
          apply mul_le_mul (by linarith) hw' hw'0 (by positivity)
        have h2 : (1 + 9 * (R : ℤ) ^ 2) * β = β + 9 * (β * R ^ 2) := by ring
        have h3 : 10 * (β : ℤ) * R ^ 2 = 10 * (β * R ^ 2) := by ring
        linarith
      have : (g : ℤ) < ((3 * n + R ^ 3 : ℕ) : ℤ) := by push_cast; linarith
      exact_mod_cast this
    · obtain ⟨i, rfl⟩ : ∃ i, y = 3 * i + 1 := ⟨y / 3, by omega⟩
      have hi : i < n := by omega
      have hKi : K i ≤ 3 * n + 1 := by have := K_le i; omega
      have hLi : L i ≤ 3 * n + 1 := by have := L_le i; omega
      obtain ⟨e, he, heR⟩ := hdivM (K i) hKi
      obtain ⟨b, hb, hbR⟩ := hdivM (L i) hLi
      have hT : Tz R β e (K i) = V (K i) := by unfold Tz; rw [Mz_eq]; linarith
      have hP : Tz R β b (L i) = V (L i) := by unfold Tz; rw [Mz_eq]; linarith
      have hy : 3 * i + 1 = 3 * J (K i) (L i) + 1 := by rw [J_K_L]
      rw [hy]
      obtain ⟨g, hg, hgle⟩ := exists_Bpoly_eq_zero (R := R) (β := β) (b := b) (e := e) (s := K i) (w := L i)
        (by
          rw [hT, hP, J_K_L]
          have hc := (S_spec R β (3 * i + 1)).1
          rw [hS (3 * i + 1) (by omega)] at hc
          have hV3 : V (3 * i + 1) = V (K i) * V (L i) := hVmul i
          rw [show (R : ℤ) - V (K i) * V (L i) = R - V (3 * i + 1) by rw [hV3]]
          exact Int.modEq_iff_dvd.1 hc.symm)
        (by rw [hT, hP]; exact hsum_lt _ _ hKi hLi)
      refine ⟨b, e, g, K i, L i, by omega, by omega, ?_, by have := K_le i; omega,
        by have := L_le i; omega, by rw [hg]; ring⟩
      rw [hT, hP] at hgle
      have hv : |(R : ℤ) - V (K i) * V (L i)| ≤ 2 * R := by
        have h1 := abs_le.1 (hVVR (K i) (L i) hKi hLi)
        rw [abs_le]
        constructor <;> linarith [h1.1, h1.2]
      have hv2 : ((R : ℤ) - V (K i) * V (L i)) ^ 2 ≤ 4 * (R : ℤ) ^ 2 := by
        have := sq_le_sq' (abs_le.1 hv).1 (abs_le.1 hv).2
        calc ((R : ℤ) - V (K i) * V (L i)) ^ 2 ≤ (2 * (R : ℤ)) ^ 2 := this
          _ = 4 * (R : ℤ) ^ 2 := by ring
      have hw' : (β : ℤ) - V (K i) ^ 2 - V (L i) ^ 2 ≤ β := by
        have := sq_nonneg (V (K i)); have := sq_nonneg (V (L i)); linarith
      have hw'0 : 0 ≤ (β : ℤ) - V (K i) ^ 2 - V (L i) ^ 2 := by
        have := hsum_lt _ _ hKi hLi; linarith
      have hR2 : (0 : ℤ) < (R : ℤ) ^ 2 := by positivity
      have hR3 : 10 * (β : ℤ) * R ^ 2 < (R : ℤ) ^ 3 := by
        have h1 : (10 * β : ℤ) < R := by exact_mod_cast hR10
        calc 10 * (β : ℤ) * R ^ 2 < R * R ^ 2 := mul_lt_mul_of_pos_right h1 hR2
          _ = (R : ℤ) ^ 3 := by ring
      have hβR : (β : ℤ) ≤ β * R ^ 2 := le_mul_of_one_le_right (by positivity) (by linarith)
      have hgZ : (g : ℤ) < (R : ℤ) ^ 3 := by
        have h1 : (1 + ((R : ℤ) - V (K i) * V (L i)) ^ 2) * ((β : ℤ) - V (K i) ^ 2 - V (L i) ^ 2)
            ≤ (1 + 4 * (R : ℤ) ^ 2) * β := by
          apply mul_le_mul (by linarith) hw' hw'0 (by positivity)
        have h2 : (1 + 4 * (R : ℤ) ^ 2) * β = β + 4 * (β * R ^ 2) := by ring
        have h3 : 10 * (β : ℤ) * R ^ 2 = 10 * (β * R ^ 2) := by ring
        have h4 : (0 : ℤ) ≤ β * R ^ 2 := by positivity
        linarith
      have : (g : ℤ) < ((3 * n + R ^ 3 : ℕ) : ℤ) := by push_cast; linarith
      exact_mod_cast this
    · obtain ⟨i, rfl⟩ : ∃ i, y = 3 * i + 2 := ⟨y / 3, by omega⟩
      refine ⟨0, 0, i, 0, 0, by omega, by omega, by omega, by omega, by omega, ?_⟩
      have : Cpoly i (3 * i + 2) = 0 := by unfold Cpoly; push_cast; ring
      rw [this, mul_zero]

theorem cond34_of_mem {n x : ℕ} (hn : 0 < n) (hx : 0 < x) (hW : x ∈ W n) :
    ∃ u v h R β θ, Cond34 n x u v h R β θ := by
  obtain ⟨u, v, h, R, β, θ, hJ, hU, hy⟩ := cond34_of_mem_bounded hn hx hW
  exact ⟨u, v, h, R, β, θ, hJ, hU, fun y hy' =>
    let ⟨b, e, g, s, w, _, _, _, _, _, hABC⟩ := hy y hy'
    ⟨b, e, g, s, w, hABC⟩⟩

/-- **Lemma 3.4.** -/
theorem lemma_3_4 {n x : ℕ} (hn : 0 < n) (hx : 0 < x) :
    x ∈ W n ↔ ∃ u v h R β θ, Cond34 n x u v h R β θ :=
  ⟨cond34_of_mem hn hx, fun ⟨u, v, _, R, β, _, hc⟩ =>
    (lemma_3_2 hn).2 ⟨u, v, R, β, cond32_of_cond34 hc⟩⟩

end Jones1978
