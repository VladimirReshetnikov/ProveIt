import DiophantineConsistency.NativePellStepDown
import DiophantineConsistency.SplitCertificate59

/-!
# Main Pell classification and preliminary bounds for the native source

The old-z transport row is never used. Classification and both half-modulus
bounds precede auxiliary step-down and any assertion that the rank is odd.
-/

namespace DiophantineConsistency.NativePellBootstrap

open Diophantine Pell Jones1980

/-- Classify the positive second coordinate of the main norm. -/
theorem main_classification {a c D : ℕ} (hc : 0 < c)
    (hnorm : D ^ 2 = 1 + ((a + 2) ^ 2 - 1) * c ^ 2) :
    ∃ p, 0 < p ∧ D = xn (by omega : 1 < a + 2) p ∧
      c = yn (by omega : 1 < a + 2) p := by
  obtain ⟨p,hD,hc'⟩ := eq_pell_of_sq (by omega : 1 < a + 2) hnorm
  refine ⟨p,?_,hD,hc'⟩
  by_contra hp
  have hp : p = 0 := by omega
  rw [hp,yn_zero] at hc'
  omega

/-- For bases at least three, every main second coordinate exceeding one
is strictly larger than twice its index. -/
theorem twice_index_lt {A c p : ℕ} (hA : 1 < A) (hA3 : 3 ≤ A)
    (hc : 1 < c) (hcp : c = yn hA p) : 2 * p < c := by
  by_contra hlt
  have hle : yn hA p ≤ 2 * p := by rw [← hcp]; omega
  have hp2 : p ≤ 2 := Jones1982.le_two_of_ψ_le hA hle
  interval_cases p
  · rw [yn_zero] at hcp; omega
  · rw [yn_one] at hcp; omega
  · change c = ψ hA 2 at hcp
    rw [ψ_two] at hcp; omega

/-- The native rank before interpretation of its target polynomial. -/
def nativeRank (x : Fin 31 → ℕ) : ℤ := (x 19 : ℤ) * x 8 - x 26

/-- Direct main classification from the three literal old-z source rows.
No port inequalities or auxiliary norm are used. -/
theorem source_main_classification (ports : Fin 4 → ℤ) (x : Fin 31 → ℕ)
    (hx : ∀ i, 0 < x i)
    (hs : ∀ k, SplitCertificate59.sourceRows ports (fun i => (x i : ℤ)) k = 0) :
    ∃ p, 0 < p ∧ x 22 = xn (by omega : 1 < x 20 + 2) p ∧
      x 19 = yn (by omega : 1 < x 20 + 2) p := by
  have h9 := hs 9
  have h10 := hs 10
  have h11 := hs 11
  change (-3 : ℤ) + x 30 + (-4) * x 20 + (-1) * ((x 20 : ℤ) ^ 2) = 0 at h9
  change (x 23 : ℤ) + (-1) * ((x 19 : ℤ) ^ 2) = 0 at h10
  change (-1 : ℤ) + (-1) * ((x 23 : ℤ) * x 30) + (x 22 : ℤ) ^ 2 = 0 at h11
  have hδ : x 30 = x 20 ^ 2 + 4 * x 20 + 3 := by
    have hz : (x 30 : ℤ) = (x 20 : ℤ) ^ 2 + 4 * x 20 + 3 := by nlinarith
    exact_mod_cast hz
  have hc2 : x 23 = x 19 ^ 2 := by
    have hz : (x 23 : ℤ) = (x 19 : ℤ) ^ 2 := by nlinarith
    exact_mod_cast hz
  have hn : x 22 ^ 2 = 1 + x 23 * x 30 := by
    have hz : (x 22 : ℤ) ^ 2 = 1 + (x 23 : ℤ) * x 30 := by nlinarith
    exact_mod_cast hz
  have hδ' : (x 20 + 2) ^ 2 - 1 = x 20 ^ 2 + 4 * x 20 + 3 := by
    have he : (x 20 + 2) ^ 2 = (x 20 ^ 2 + 4 * x 20 + 3) + 1 := by ring
    omega
  apply main_classification (hx 19)
  rw [hδ', ← hδ, mul_comm, ← hc2]
  exact hn

/-- The positive source fixes the main second coordinate above one, before
any Pell or auxiliary classification. -/
theorem source_c_bounds (ports : Fin 4 → ℤ) (x : Fin 31 → ℕ)
    (hx : ∀ i, 0 < x i)
    (hs : ∀ k, SplitCertificate59.sourceRows ports (fun i => (x i : ℤ)) k = 0) :
    x 19 = x 12 + (x 12 + x 13) * (x 16 * x 9) ∧ 3 ≤ x 19 := by
  have h3 := hs 3
  have h5 := hs 5
  change (x 20 : ℤ) + (-1) * x 17 + (-1) * ((x 9 : ℤ) * x 16) = 0 at h3
  change (x 19 : ℤ) + (-1) * ((x 13 : ℤ) * x 20) + x 13 * x 17 + (-1) * x 12 +
    (-1) * ((x 12 : ℤ) * x 20) + x 12 * x 17 = 0 at h5
  have hc : x 19 = x 12 + (x 12 + x 13) * (x 16 * x 9) := by
    have hz : (x 19 : ℤ) = x 12 + ((x 12 : ℤ) + x 13) * (x 16 * x 9) := by
      linear_combination h5 + ((x 12 : ℤ) + x 13) * h3
    exact_mod_cast hz
  refine ⟨hc,?_⟩
  have hk : 2 ≤ x 12 + x 13 := by have := hx 12; have := hx 13; omega
  have hY : 1 ≤ x 16 * x 9 := Nat.mul_pos (hx 16) (hx 9)
  have hη := hx 12
  rw [hc]
  nlinarith

/-- A positive beta gives a nontrivial Y directly from the first two rows. -/
theorem source_Y_ge_two (ports : Fin 4 → ℤ) (hβ : 0 < ports 0) (x : Fin 31 → ℕ)
    (hx : ∀ i, 0 < x i)
    (hs : ∀ k, SplitCertificate59.sourceRows ports (fun i => (x i : ℤ)) k = 0) :
    2 ≤ x 16 * x 9 := by
  have h0 := hs 0
  have h1 := hs 1
  change (x 24 : ℤ) + ((-2) * ports 0) * x 0 + (-(ports 0 ^ 2)) * ((x 0 : ℤ) ^ 2) = 0 at h0
  change (-1 : ℤ) + (-1) * x 24 + x 16 + (-ports 0) * x 0 +
    (-ports 0) * ((x 0 : ℤ) * x 24) = 0 at h1
  let q : ℤ := 1 + (x 0 : ℤ) * ports 0
  have hq : 2 ≤ q := by
    have hx0 : (1 : ℤ) ≤ x 0 := by exact_mod_cast hx 0
    dsimp [q]
    nlinarith [mul_nonneg (show 0 ≤ (x 0 : ℤ) - 1 by omega) (show 0 ≤ ports 0 - 1 by omega)]
  have hL : (x 24 : ℤ) = q ^ 2 - 1 := by dsimp [q]; linear_combination h0
  have hN : (x 16 : ℤ) = q * (1 + x 24) := by dsimp [q]; linear_combination h1
  have hL3 : (3 : ℤ) ≤ x 24 := by nlinarith
  have hN8 : (8 : ℤ) ≤ x 16 := by
    nlinarith [mul_nonneg (show 0 ≤ q - 2 by omega) (show 0 ≤ (x 24 : ℤ) - 3 by omega)]
  have hN2 : 2 ≤ x 16 := by exact_mod_cast (show (2 : ℤ) ≤ x 16 by omega)
  exact (Nat.mul_le_mul_right 1 hN2).trans (Nat.mul_le_mul_left _ (hx 9))

/-- The literal index row and positive h imply the half-modulus bound for
the native rank, independently of the auxiliary Pell step-down. -/
theorem source_rank_half_lt (ports : Fin 4 → ℤ) (hβ : 0 < ports 0)
    (x : Fin 31 → ℕ) (hx : ∀ i, 0 < x i)
    (hs : ∀ k, SplitCertificate59.sourceRows ports (fun i => (x i : ℤ)) k = 0) :
    2 * nativeRank x < (x 19 : ℤ) := by
  have hc := (source_c_bounds ports x hx hs).1
  have hY := source_Y_ge_two ports hβ x hx hs
  have h12 := hs 12
  change (-1 : ℤ) + x 26 + x 13 + x 12 + (-1) * ((x 8 : ℤ) * x 19) +
    (-1) * ((x 5 : ℤ) * x 17) = 0 at h12
  have hind : (x 12 : ℤ) + x 13 = 1 + nativeRank x + x 5 * x 17 := by
    dsimp [nativeRank]
    linear_combination h12
  have hcz : (x 19 : ℤ) = x 12 + ((x 12 : ℤ) + x 13) * ((x 16 : ℤ) * x 9) := by
    exact_mod_cast hc
  have hYz : (2 : ℤ) ≤ (x 16 : ℤ) * x 9 := by exact_mod_cast hY
  have hη : (0 : ℤ) < x 12 := by exact_mod_cast hx 12
  have hk : (0 : ℤ) ≤ (x 12 : ℤ) + x 13 := by positivity
  have hEh : (0 : ℤ) ≤ (x 5 : ℤ) * x 17 := by positivity
  nlinarith [mul_nonneg hk (show 0 ≤ (x 16 : ℤ) * x 9 - 2 by omega)]

/-- The actual positive source supplies classification and both half-modulus
bounds, without a first-index bound, oddness assumption, or auxiliary step-down. -/
theorem source_main_and_half_bounds (ports : Fin 4 → ℤ) (hβ : 0 < ports 0)
    (x : Fin 31 → ℕ) (hx : ∀ i, 0 < x i)
    (hs : ∀ k, SplitCertificate59.sourceRows ports (fun i => (x i : ℤ)) k = 0) :
    ∃ p, 0 < p ∧ x 22 = xn (by omega : 1 < x 20 + 2) p ∧
      x 19 = yn (by omega : 1 < x 20 + 2) p ∧ 2 * p < x 19 ∧
      2 * nativeRank x < (x 19 : ℤ) := by
  obtain ⟨p,hp,hD,hc⟩ := source_main_classification ports x hx hs
  refine ⟨p,hp,hD,hc,?_,source_rank_half_lt ports hβ x hx hs⟩
  exact twice_index_lt (by omega) (by have := hx 20; omega)
    (by have h := (source_c_bounds ports x hx hs).2; omega) hc

/-- The explicit least positive unit for the native first norm. -/
def firstUnit (Q : ℕ) : Pell.Solution₁ ((Q : ℤ) * (Q + 1)) :=
  Pell.Solution₁.mk (2 * Q + 1) 2 (by ring)

/-- No square lies at `Q(Q+1)+1`, and the next available second coordinate
is two. This proves the ordinary fundamental-unit assertion unboundedly. -/
theorem firstUnit_fundamental {Q : ℕ} (hQ : 0 < Q) :
    Pell.IsFundamental (firstUnit Q) := by
  refine ⟨by change (1 : ℤ) < 2 * Q + 1; omega, by change (0 : ℤ) < 2; norm_num, ?_⟩
  intro b hb
  change (2 * Q + 1 : ℤ) ≤ b.x
  have hQZ : (0 : ℤ) < Q := by exact_mod_cast hQ
  have hprop := b.prop
  have hysq : (4 : ℤ) ≤ b.y ^ 2 := by
    by_contra hlt
    have hsmall : b.y ^ 2 < (2 : ℤ) ^ 2 := by omega
    have habs := abs_lt_of_sq_lt_sq hsmall (by norm_num : (0 : ℤ) ≤ 2)
    have hycases : b.y = -1 ∨ b.y = 0 ∨ b.y = 1 := by
      rw [abs_lt] at habs
      omega
    have hnotone (hy : b.y ^ 2 = 1) : False := by
      have hlow : (Q : ℤ) ^ 2 < b.x ^ 2 := by nlinarith
      have hhigh : b.x ^ 2 < ((Q : ℤ) + 1) ^ 2 := by nlinarith
      have hlo : (Q : ℤ) < b.x := (sq_lt_sq₀ (by positivity) (by omega)).mp hlow
      have hhi : b.x < (Q : ℤ) + 1 := (sq_lt_sq₀ (by omega) (by positivity)).mp hhigh
      omega
    rcases hycases with hy | hy | hy
    · exact hnotone (by rw [hy]; norm_num)
    · have hx2 : (1 : ℤ) < b.x ^ 2 := by
        simpa using (sq_lt_sq₀ (by norm_num : (0 : ℤ) ≤ 1) (by omega)).mpr hb
      rw [hy] at hprop
      norm_num at hprop
      omega
    · exact hnotone (by rw [hy]; norm_num)
  have hxsq : (2 * Q + 1 : ℤ) ^ 2 ≤ b.x ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ (Q : ℤ) * (Q + 1) by positivity)
      (show 0 ≤ b.y ^ 2 - 4 by omega)]
  exact (sq_le_sq₀ (by positivity) (by omega)).mp hxsq

/-- Classification of the actual square first norm, whose second coordinate
is twice a Pell sequence value. -/
theorem first_norm_classification {Q tau k : ℕ} (hQ : 0 < Q) (hk : 0 < k)
    (hnorm : tau ^ 2 = 1 + Q * (Q + 1) * k ^ 2) :
    ∃ n, 0 < n ∧ tau = xn (by omega : 1 < 2 * Q + 1) n ∧
      k = 2 * yn (by omega : 1 < 2 * Q + 1) n := by
  have hprop : (tau : ℤ) ^ 2 - (Q : ℤ) * (Q + 1) * k ^ 2 = 1 := by
    have hz : (tau : ℤ) ^ 2 = 1 + (Q : ℤ) * (Q + 1) * k ^ 2 := by exact_mod_cast hnorm
    linear_combination hz
  have htau : 0 < tau := by nlinarith [Nat.zero_le (Q * (Q + 1) * k ^ 2)]
  obtain ⟨n,hn⟩ := (firstUnit_fundamental hQ).eq_pow_of_nonneg
    (a := Pell.Solution₁.mk tau k hprop) (by change (0 : ℤ) < tau; exact_mod_cast htau)
    (by change (0 : ℤ) ≤ k; positivity)
  obtain ⟨hnx,hny⟩ := pow_x_y (firstUnit Q) (by omega : 1 < 2 * Q + 1) rfl n
  rw [← hn,Pell.Solution₁.x_mk] at hnx
  rw [← hn,Pell.Solution₁.y_mk] at hny
  change (k : ℤ) = 2 * (yn (by omega : 1 < 2 * Q + 1) n : ℤ) at hny
  have hk' : k = 2 * yn (by omega : 1 < 2 * Q + 1) n := by exact_mod_cast hny
  refine ⟨n,?_,by exact_mod_cast hnx,hk'⟩
  by_contra hn0
  have hn0 : n = 0 := by omega
  rw [hn0,yn_zero,mul_zero] at hk'
  omega

/-- An index of six suffices; the fifth power lower bound already exceeds
the degree-five bootstrap polynomial. -/
theorem large_of_six_le {A c p : ℕ} (hA : 1 < A) (hp : 6 ≤ p)
    (hcp : c = yn hA p) : A * (A ^ 2 - 1) ^ 2 < c := by
  have h1 : (2 * A - 1) ^ (p - 1) ≤ c := by
    rw [hcp]
    have h := pow_le_ψ_succ hA (p - 1)
    rwa [Nat.sub_add_cancel (by omega : 1 ≤ p)] at h
  have h2 : A ^ 5 < (2 * A - 1) ^ (p - 1) :=
    calc A ^ 5 < (2 * A - 1) ^ 5 := Nat.pow_lt_pow_left (by omega) (by decide)
      _ ≤ (2 * A - 1) ^ (p - 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hlt : (A ^ 2 - 1) ^ 2 < (A ^ 2) ^ 2 :=
    Nat.pow_lt_pow_left (by have := Nat.one_le_pow 2 A (by omega); omega) two_ne_zero
  have h3 : A * (A ^ 2 - 1) ^ 2 < A ^ 5 := by
    convert Nat.mul_lt_mul_of_pos_left hlt (by omega : 0 < A) using 1
    ring
  omega

/-- The first norm's parameter Q, without subtracting natural coordinates. -/
def firstQ (x : Fin 31 → ℕ) : ℕ := x 21 * (x 16 * x 9) ^ 2

theorem firstQ_pos (x : Fin 31 → ℕ) (hx : ∀ i, 0 < x i) : 0 < firstQ x := by
  exact Nat.mul_pos (hx 21) (pow_pos (Nat.mul_pos (hx 16) (hx 9)) _)

/-- The two defining source rows reconstruct E and P over the naturals. -/
theorem source_first_registers (ports : Fin 4 → ℤ) (x : Fin 31 → ℕ)
    (hx : ∀ i, 0 < x i)
    (hs : ∀ k, SplitCertificate59.sourceRows ports (fun i => (x i : ℤ)) k = 0) :
    x 17 = x 21 * (x 16 * x 9) ∧
      x 18 = (x 12 + x 13) * (1 + firstQ x) := by
  have h3 := hs 3
  have h4 := hs 4
  have h6 := hs 6
  change (x 20 : ℤ) + (-1) * x 17 + (-1) * ((x 9 : ℤ) * x 16) = 0 at h3
  change (-1 : ℤ) * ((x 20 : ℤ) * x 21) + x 17 + x 17 * x 21 = 0 at h4
  change (x 18 : ℤ) + (-1) * ((x 17 : ℤ) * x 19) + (-1) * x 13 + (-1) * x 12 +
    x 12 * x 17 = 0 at h6
  have hE : x 17 = x 21 * (x 16 * x 9) := by
    have hz : (x 17 : ℤ) = x 21 * (x 16 * x 9) := by
      linear_combination h4 + (x 21 : ℤ) * h3
    exact_mod_cast hz
  have hc := (source_c_bounds ports x hx hs).1
  have hcZ : (x 19 : ℤ) = x 12 + ((x 12 : ℤ) + x 13) * (x 16 * x 9) := by exact_mod_cast hc
  have hEZ : (x 17 : ℤ) = x 21 * (x 16 * x 9) := by exact_mod_cast hE
  refine ⟨hE,?_⟩
  have hPZ : (x 18 : ℤ) = ((x 12 : ℤ) + x 13) * (1 + x 21 * (x 16 * x 9) ^ 2) := by
    rw [hcZ,hEZ] at h6
    linear_combination h6
  exact_mod_cast hPZ

/-- Exact classification of the literal square first norm. -/
theorem source_first_classification (ports : Fin 4 → ℤ) (x : Fin 31 → ℕ)
    (hx : ∀ i, 0 < x i)
    (hs : ∀ k, SplitCertificate59.sourceRows ports (fun i => (x i : ℤ)) k = 0) :
    ∃ n, 0 < n ∧ x 11 = xn (by have := firstQ_pos x hx; omega :
      1 < 2 * firstQ x + 1) n ∧
      x 12 + x 13 = 2 * yn (by have := firstQ_pos x hx; omega :
      1 < 2 * firstQ x + 1) n := by
  have hQ := firstQ_pos x hx
  have hP := (source_first_registers ports x hx hs).2
  have h7 := hs 7
  change (-1 : ℤ) + (-1) * ((x 18 : ℤ) ^ 2) + x 13 * x 18 + x 12 * x 18 +
    (x 11 : ℤ) ^ 2 = 0 at h7
  have hPZ : (x 18 : ℤ) = ((x 12 : ℤ) + x 13) * (1 + (firstQ x : ℤ)) := by exact_mod_cast hP
  have hnormZ : (x 11 : ℤ) ^ 2 = 1 + (firstQ x : ℤ) * (firstQ x + 1) *
      ((x 12 : ℤ) + x 13) ^ 2 := by
    rw [hPZ] at h7
    linear_combination h7
  apply first_norm_classification hQ (by have := hx 12; omega)
  exact_mod_cast hnormZ

/-- Once the outer rank lies in the first E-window, the literal index row
forces the first index above half the rank. -/
theorem first_index_lower {E Q k n R h : ℕ} (hQ : 0 < Q)
    (hEP : E ∣ 2 * Q) (hR : R + 1 < E)
    (hk : k = 2 * yn (by omega : 1 < 2 * Q + 1) n)
    (hind : k = 1 + R + E * h) : R + 1 ≤ 2 * n := by
  have hP : 1 < 2 * Q + 1 := by omega
  have hm : yn hP n ≡ n [MOD E] := by
    apply Nat.ModEq.of_dvd (show E ∣ 2 * Q + 1 - 1 by simpa using hEP)
    exact yn_modEq_a_sub_one hP n
  have hkmod : k ≡ 2 * n [MOD E] := by rw [hk]; exact hm.mul_left 2
  have hkR : k ≡ R + 1 [MOD E] := by
    show k % E = (R + 1) % E
    rw [hind,show 1 + R + E * h = R + 1 + h * E by ring,Nat.add_mul_mod_self_right]
  by_contra hlt
  have heq := Nat.ModEq.eq_of_lt_of_lt (hkmod.symm.trans hkR) (by omega) hR
  omega

/-- Growth of the two classified pairs places the main index strictly above
the first index. -/
theorem main_index_gt_first {A P c k p n : ℕ}
    (hA : 1 < A) (hP : 1 < P) (hc : 1 < c)
    (hp : 0 < p) (hn : 0 < n) (hAP : 2 * A < 2 * P - 1)
    (hcp : c = yn hA p) (hk : k = 2 * yn hP n) (hkc : k < c) : n < p := by
  have hp2 : 2 ≤ p := by
    by_contra hlt
    have hp1 : p = 1 := by omega
    rw [hp1,yn_one] at hcp
    omega
  by_contra hlt
  have hpn : p ≤ n := by omega
  have hn2 : 2 ≤ n := by omega
  have h1 : c ≤ (2 * A) ^ (p - 1) := by
    rw [hcp]
    have h := ψ_succ_le_pow hA (p - 1)
    rwa [Nat.sub_add_cancel (by omega : 1 ≤ p)] at h
  have h2 : (2 * A) ^ (p - 1) ≤ (2 * A) ^ (n - 1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have h3 : (2 * A) ^ (n - 1) < (2 * P - 1) ^ (n - 1) :=
    Nat.pow_lt_pow_left hAP (by omega)
  have h4 : (2 * P - 1) ^ (n - 1) ≤ yn hP n := by
    have h := pow_le_ψ_succ hP (n - 1)
    rwa [Nat.sub_add_cancel (by omega : 1 ≤ n)] at h
  have h5 : yn hP n ≤ k := by rw [hk]; omega
  omega

/-- The source-defined Pell parameter a is Y(X+1). -/
theorem source_a_eq (ports : Fin 4 → ℤ) (x : Fin 31 → ℕ)
    (hx : ∀ i, 0 < x i)
    (hs : ∀ k, SplitCertificate59.sourceRows ports (fun i => (x i : ℤ)) k = 0) :
    x 20 = x 21 * (x 16 * x 9) + x 16 * x 9 := by
  have h3 := hs 3
  change (x 20 : ℤ) + (-1) * x 17 + (-1) * ((x 9 : ℤ) * x 16) = 0 at h3
  have hE := (source_first_registers ports x hx hs).1
  have hEZ : (x 17 : ℤ) = x 21 * (x 16 * x 9) := by exact_mod_cast hE
  have haZ : (x 20 : ℤ) = x 21 * (x 16 * x 9) + x 16 * x 9 := by
    rw [hEZ] at h3
    linear_combination h3
  exact_mod_cast haZ

/-- Source positivity separates the two Pell bases enough for the elementary
upper/lower sequence power estimates. -/
theorem source_base_separation (ports : Fin 4 → ℤ) (hβ : 0 < ports 0)
    (x : Fin 31 → ℕ) (hx : ∀ i, 0 < x i)
    (hs : ∀ k, SplitCertificate59.sourceRows ports (fun i => (x i : ℤ)) k = 0) :
    2 * (x 20 + 2) < 2 * (2 * firstQ x + 1) - 1 := by
  have hY := source_Y_ge_two ports hβ x hx hs
  have ha := source_a_eq ports x hx hs
  have hYY : 2 * (x 16 * x 9) ≤ (x 16 * x 9) ^ 2 := by nlinarith
  have hQY : 2 * (x 21 * (x 16 * x 9)) ≤ firstQ x := by
    dsimp [firstQ]
    have h := Nat.mul_le_mul_left (x 21) hYY
    nlinarith
  have hXY : x 16 * x 9 ≤ x 21 * (x 16 * x 9) := Nat.le_mul_of_pos_left _ (hx 21)
  have heq : 2 * (2 * firstQ x + 1) - 1 = 4 * firstQ x + 1 := by omega
  rw [heq]
  nlinarith

/-- The concrete outer range R≥8 and R+1<E completes the strong-rank
bootstrap from the literal positive old-z source, before signed step-down. -/
theorem source_bootstrap (ports : Fin 4 → ℤ) (hβ : 0 < ports 0)
    (x : Fin 31 → ℕ) (hx : ∀ i, 0 < x i)
    (hs : ∀ k, SplitCertificate59.sourceRows ports (fun i => (x i : ℤ)) k = 0)
    {R : ℕ} (hR : (R : ℤ) = nativeRank x) (hR8 : 8 ≤ R) (hRE : R + 1 < x 17) :
    ∃ p, 6 ≤ p ∧ x 22 = xn (by omega : 1 < x 20 + 2) p ∧
      x 19 = yn (by omega : 1 < x 20 + 2) p ∧
      (x 20 + 2) * ((x 20 + 2) ^ 2 - 1) ^ 2 < x 19 ∧
      2 * p < x 19 ∧ 2 * R < x 19 := by
  obtain ⟨p,hp,hD,hc,hpc,hRc⟩ := source_main_and_half_bounds ports hβ x hx hs
  obtain ⟨n,hn,hτ,hk⟩ := source_first_classification ports x hx hs
  have hE := (source_first_registers ports x hx hs).1
  have hEP : x 17 ∣ 2 * firstQ x := by
    rw [hE]
    exact ⟨2 * (x 16 * x 9),by dsimp [firstQ]; ring⟩
  have h12 := hs 12
  change (-1 : ℤ) + x 26 + x 13 + x 12 + (-1) * ((x 8 : ℤ) * x 19) +
    (-1) * ((x 5 : ℤ) * x 17) = 0 at h12
  have hindZ : (x 12 : ℤ) + x 13 = 1 + R + x 17 * x 5 := by
    have hR' : (R : ℤ) = (x 19 : ℤ) * x 8 - x 26 := hR
    linear_combination h12 - hR'
  have hind : x 12 + x 13 = 1 + R + x 17 * x 5 := by exact_mod_cast hindZ
  have hnlow := first_index_lower (firstQ_pos x hx) hEP hRE hk hind
  have hn5 : 5 ≤ n := by omega
  have hkc : x 12 + x 13 < x 19 := by
    have hce := (source_c_bounds ports x hx hs).1
    have hkY : x 12 + x 13 ≤ (x 12 + x 13) * (x 16 * x 9) :=
      Nat.le_mul_of_pos_right _ (Nat.mul_pos (hx 16) (hx 9))
    have hη := hx 12
    omega
  have hnp : n < p := main_index_gt_first (by omega)
    (by have := firstQ_pos x hx; omega)
    (by have h := (source_c_bounds ports x hx hs).2; omega) hp hn
    (source_base_separation ports hβ x hx hs) hc hk hkc
  have hp6 : 6 ≤ p := by omega
  refine ⟨p,hp6,hD,hc,large_of_six_le (by omega) hp6 hc,hpc,?_⟩
  rw [← hR] at hRc
  exact_mod_cast hRc

/-- The polynomial target of the inner native index row. This is distinct
from the outer degree-separated code's reduced rank. -/
def nativeTarget (ports : Fin 4 → ℤ) (x : Fin 31 → ℕ) : ℤ :=
  let q := 1 + (x 0 : ℤ) * ports 0
  ((q - 1) * (q - x 1) + x 2) * (q ^ 2 - 1) +
    (ports 2 + ports 3 * q) * x 0

/-- The literal source target row binds the inner native rank exactly. -/
theorem source_rank_eq_target (ports : Fin 4 → ℤ) (x : Fin 31 → ℕ)
    (hs : ∀ k, SplitCertificate59.sourceRows ports (fun i => (x i : ℤ)) k = 0) :
    nativeRank x = nativeTarget ports x := by
  have h0 := hs 0
  have h1 := hs 1
  have h13 := hs 13
  change (x 24 : ℤ) + ((-2) * ports 0) * x 0 + (-(ports 0 ^ 2)) * ((x 0 : ℤ) ^ 2) = 0 at h0
  change (-1 : ℤ) + (-1) * x 24 + x 16 + (-ports 0) * x 0 +
    (-ports 0) * ((x 0 : ℤ) * x 24) = 0 at h1
  change (1 : ℤ) + (-1) * x 26 + x 24 + (-1) * x 16 + x 8 * x 19 +
    (-1) * ((x 2 : ℤ) * x 24) + (-1) * x 1 + (-1) * ((x 1 : ℤ) * x 24) +
    x 1 * x 16 + (-ports 3 - ports 2 + 2 * ports 0) * x 0 +
    ports 0 * ((x 0 : ℤ) * x 24) + (-ports 0) * ((x 0 : ℤ) * x 16) +
    (-ports 0) * ((x 0 : ℤ) * x 1) + (-(ports 0 * ports 3) + ports 0 ^ 2) *
      ((x 0 : ℤ) ^ 2) = 0 at h13
  let q : ℤ := 1 + (x 0 : ℤ) * ports 0
  have hL : (x 24 : ℤ) = q ^ 2 - 1 := by dsimp [q]; linear_combination h0
  have hN : (x 16 : ℤ) = q * (1 + x 24) := by dsimp [q]; linear_combination h1
  rw [hN,hL] at h13
  dsimp [q] at h13
  dsimp [nativeRank,nativeTarget]
  linear_combination h13

/-- The old-z transport forces a positive transport gap, using only positive
source coordinates, beta>0, and the nonnegative K port. -/
theorem source_transport_positive (ports : Fin 4 → ℤ)
    (hβ : 0 < ports 0) (hK : 0 ≤ ports 1)
    (x : Fin 31 → ℕ) (hx : ∀ i, 0 < x i)
    (hs : ∀ k, SplitCertificate59.sourceRows ports (fun i => (x i : ℤ)) k = 0) :
    0 < 1 + (x 0 : ℤ) * ports 0 - x 1 - x 2 := by
  let q : ℤ := 1 + (x 0 : ℤ) * ports 0
  have hq2 : 2 ≤ q := by
    have hx0 : (1 : ℤ) ≤ x 0 := by exact_mod_cast hx 0
    dsimp [q]
    nlinarith [mul_nonneg (show 0 ≤ (x 0 : ℤ) - 1 by omega) (show 0 ≤ ports 0 - 1 by omega)]
  have h14 := hs 14
  change ports 1 + (x 10 : ℤ) + (-ports 1) * x 2 + (-1) * ((x 2 : ℤ) * x 10) +
    (-1 - ports 1) * x 1 + (-1) * ((x 1 : ℤ) * x 10) +
    (ports 0 + ports 0 * ports 1) * x 0 + ports 0 * ((x 0 : ℤ) * x 10) +
    (-ports 0) * ((x 0 : ℤ) * x 3) = 0 at h14
  have htrans : (ports 1 + x 10) * (q - x 1 - x 2) =
      x 1 + ((x 3 : ℤ) - 1) * (q - 1) := by
    dsimp [q]
    linear_combination h14
  have hF : (0 : ℤ) < x 1 := by exact_mod_cast hx 1
  have hz : (1 : ℤ) ≤ x 3 := by exact_mod_cast hx 3
  have hw : (0 : ℤ) < x 10 := by exact_mod_cast hx 10
  have hKw : 0 < ports 1 + x 10 := by omega
  have hprod : 0 < (ports 1 + x 10) * (q - x 1 - x 2) := by
    rw [htrans]
    nlinarith [mul_nonneg (show 0 ≤ (x 3 : ℤ) - 1 by omega) (show 0 ≤ q - 1 by omega)]
  exact pos_of_mul_pos_right hprod hKw.le

/-- Native rank positivity follows from the OLD positive transport coordinate
and nonnegative native mask ports, without importing the outer rank bounds. -/
theorem source_native_rank_ge_twentyfour (ports : Fin 4 → ℤ)
    (hβ : 0 < ports 0) (hK : 0 ≤ ports 1) (hMC : 0 ≤ ports 2) (hMF : 0 ≤ ports 3)
    (x : Fin 31 → ℕ) (hx : ∀ i, 0 < x i)
    (hs : ∀ k, SplitCertificate59.sourceRows ports (fun i => (x i : ℤ)) k = 0) :
    24 ≤ nativeRank x := by
  let q : ℤ := 1 + (x 0 : ℤ) * ports 0
  have hC : 0 < q - x 1 - x 2 := source_transport_positive ports hβ hK x hx hs
  have hF : (0 : ℤ) < x 1 := by exact_mod_cast hx 1
  have hα : (0 : ℤ) < x 2 := by exact_mod_cast hx 2
  have hq3 : 3 ≤ q := by omega
  have hL8 : 8 ≤ q ^ 2 - 1 := by nlinarith
  have hG : q ≤ (q - 1) * (q - x 1) + x 2 := by
    nlinarith [mul_nonneg (show 0 ≤ q - 1 by omega) (show 0 ≤ q - x 1 - 1 by omega)]
  have hGL := mul_le_mul_of_nonneg_right hG (show 0 ≤ q ^ 2 - 1 by omega)
  have hmin : (24 : ℤ) ≤ q * (q ^ 2 - 1) := by
    exact mul_le_mul hq3 hL8 (by norm_num) (by omega)
  have hmask : 0 ≤ (ports 2 + ports 3 * q) * x 0 := by positivity
  have htarget := source_rank_eq_target ports x hs
  change nativeRank x = ((q - 1) * (q - x 1) + x 2) * (q ^ 2 - 1) +
    (ports 2 + ports 3 * q) * x 0 at htarget
  linarith

/-- The literal defining rows give E=q^4*w*s. -/
theorem source_scale_eq (ports : Fin 4 → ℤ) (x : Fin 31 → ℕ)
    (hx : ∀ i, 0 < x i)
    (hs : ∀ k, SplitCertificate59.sourceRows ports (fun i => (x i : ℤ)) k = 0) :
    (x 17 : ℤ) = (1 + (x 0 : ℤ) * ports 0) ^ 4 * (x 10 * x 9) := by
  have h0 := hs 0
  have h1 := hs 1
  have h2 := hs 2
  change (x 24 : ℤ) + ((-2) * ports 0) * x 0 + (-(ports 0 ^ 2)) * ((x 0 : ℤ) ^ 2) = 0 at h0
  change (-1 : ℤ) + (-1) * x 24 + x 16 + (-ports 0) * x 0 +
    (-ports 0) * ((x 0 : ℤ) * x 24) = 0 at h1
  change (x 21 : ℤ) + (-1) * x 10 + (-ports 0) * ((x 0 : ℤ) * x 10) = 0 at h2
  let q : ℤ := 1 + (x 0 : ℤ) * ports 0
  have hL : (x 24 : ℤ) = q ^ 2 - 1 := by dsimp [q]; linear_combination h0
  have hN : (x 16 : ℤ) = q * (1 + x 24) := by dsimp [q]; linear_combination h1
  have hN3 : (x 16 : ℤ) = q ^ 3 := by rw [hN,hL]; ring
  have hX : (x 21 : ℤ) = q * x 10 := by dsimp [q]; linear_combination h2
  have hE := (source_first_registers ports x hx hs).1
  have hEZ : (x 17 : ℤ) = x 21 * (x 16 * x 9) := by exact_mod_cast hE
  rw [hX,hN3] at hEZ
  change (x 17 : ℤ) = q ^ 4 * (x 10 * x 9)
  linear_combination hEZ

/-- The standard two native mask bounds imply the strict first-window bound
for the INNER native rank. No outer reduced-rank estimate is used. -/
theorem source_window_bound (ports : Fin 4 → ℤ)
    (hβ : 0 < ports 0) (hK : 0 ≤ ports 1)
    (hMCβ : ports 2 < ports 0) (hMFβ : ports 3 < 2 * ports 0)
    (x : Fin 31 → ℕ) (hx : ∀ i, 0 < x i)
    (hs : ∀ k, SplitCertificate59.sourceRows ports (fun i => (x i : ℤ)) k = 0) :
    nativeRank x + 1 < (x 17 : ℤ) := by
  let q : ℤ := 1 + (x 0 : ℤ) * ports 0
  have hC : 0 < q - x 1 - x 2 := source_transport_positive ports hβ hK x hx hs
  have hF : (0 : ℤ) < x 1 := by exact_mod_cast hx 1
  have hα : (0 : ℤ) < x 2 := by exact_mod_cast hx 2
  have hJ : (0 : ℤ) < x 0 := by exact_mod_cast hx 0
  have hq3 : 3 ≤ q := by omega
  have hL : 0 ≤ q ^ 2 - 1 := by nlinarith
  have hF1 : 0 ≤ (x 1 : ℤ) - 1 := by omega
  have hC1 : 0 ≤ q - x 1 - x 2 - 1 := by omega
  have hJ1 : 0 ≤ (x 0 : ℤ) - 1 := by omega
  have hM : 0 ≤ ports 0 - ports 2 - 1 := by omega
  have hH : 0 ≤ 2 * ports 0 - ports 3 - 1 := by omega
  have hgap := add_nonneg (add_nonneg (add_nonneg
    (mul_nonneg (mul_nonneg (show 0 ≤ q by omega) hL) hF1) (mul_nonneg hL hC1))
    (mul_nonneg (show 0 ≤ q + 1 by omega) hJ1))
    (mul_nonneg hJ.le (add_nonneg hM (mul_nonneg (show 0 ≤ q by omega) hH)))
  have he : q ^ 4 - q ^ 3 - q - 1 - nativeRank x =
      q * (q ^ 2 - 1) * ((x 1 : ℤ) - 1) + (q ^ 2 - 1) * (q - x 1 - x 2 - 1) +
      (q + 1) * ((x 0 : ℤ) - 1) +
      (x 0 : ℤ) * ((ports 0 - ports 2 - 1) + q * (2 * ports 0 - ports 3 - 1)) := by
    rw [source_rank_eq_target ports x hs]
    dsimp [nativeTarget, q]
    ring
  rw [← he] at hgap
  have hEbound : q ^ 4 ≤ (x 17 : ℤ) := by
    rw [source_scale_eq ports x hx hs]
    exact le_mul_of_one_le_right (pow_nonneg (show 0 ≤ q by omega) 4)
      (one_le_mul_of_one_le_of_one_le (by exact_mod_cast hx 10) (by exact_mod_cast hx 9))
  have hcube : 0 < q ^ 3 := pow_pos (by omega) _
  omega

/-- The ordinary native mask interface needed for positive main bootstrap.
These coefficient inequalities are separate from authentic port calibration. -/
structure PortBox (ports : Fin 4 → ℤ) : Prop where
  beta_pos : 0 < ports 0
  K_nonneg : 0 ≤ ports 1
  MC_nonneg : 0 ≤ ports 2
  MF_nonneg : 0 ≤ ports 3
  MC_lt_beta : ports 2 < ports 0
  MF_lt_twice_beta : ports 3 < 2 * ports 0

/-- Main classification, the large strong-rank bootstrap and both strict
half-modulus bounds follow from the literal positive source and its mask box.
The transport is the authoritative OLD z row. -/
theorem source_bootstrap_of_portBox (ports : Fin 4 → ℤ) (hports : PortBox ports)
    (x : Fin 31 → ℕ) (hx : ∀ i, 0 < x i)
    (hs : ∀ k, SplitCertificate59.sourceRows ports (fun i => (x i : ℤ)) k = 0) :
    ∃ p, 6 ≤ p ∧ x 22 = xn (by omega : 1 < x 20 + 2) p ∧
      x 19 = yn (by omega : 1 < x 20 + 2) p ∧
      (x 20 + 2) * ((x 20 + 2) ^ 2 - 1) ^ 2 < x 19 ∧
      2 * p < x 19 ∧ 2 * nativeRank x < (x 19 : ℤ) := by
  have hR24 := source_native_rank_ge_twentyfour ports hports.beta_pos hports.K_nonneg
    hports.MC_nonneg hports.MF_nonneg x hx hs
  have hwindow := source_window_bound ports hports.beta_pos hports.K_nonneg
    hports.MC_lt_beta hports.MF_lt_twice_beta x hx hs
  let R := (nativeRank x).toNat
  have hR : (R : ℤ) = nativeRank x := Int.toNat_of_nonneg (by omega)
  have hR8 : 8 ≤ R := by omega
  have hRE : R + 1 < x 17 := by omega
  obtain ⟨p,hp,hD,hc,hbig,hpc,hRc⟩ := source_bootstrap ports hports.beta_pos x hx hs hR hR8 hRE
  refine ⟨p,hp,hD,hc,hbig,hpc,?_⟩
  omega

/-- The strong norm and the auxiliary norm are exact consequences of the
literal source rows. No cancellation of the discriminant is used. -/
theorem source_auxiliary_norms (ports : Fin 4 → ℤ) (x : Fin 31 → ℕ)
    (hx : ∀ i, 0 < x i)
    (hs : ∀ k, SplitCertificate59.sourceRows ports (fun i => (x i : ℤ)) k = 0) :
    (x 6 * x 19 ^ 2) ^ 2 = ((x 20 + 2) ^ 2 - 1) * (x 4 ^ 2 - 1) ∧
    ((x 6 : ℤ) * x 19 ^ 2) ^ 2 * (x 26 : ℤ) ^ 2 -
      (((x 6 : ℤ) * x 19 ^ 2) ^ 2 - 1) * (x 14 : ℤ) ^ 2 = 1 := by
  have h9 := hs 9
  have h10 := hs 10
  have h15 := hs 15
  have h17 := hs 17
  have h18 := hs 18
  have h19 := hs 19
  have h20 := hs 20
  have h21 := hs 21
  change (-3 : ℤ) + x 30 + (-4) * x 20 + (-1) * ((x 20 : ℤ) ^ 2) = 0 at h9
  change (x 23 : ℤ) + (-1) * ((x 19 : ℤ) ^ 2) = 0 at h10
  change (x 25 : ℤ) + (-1) * ((x 4 : ℤ) ^ 2) = 0 at h15
  change (x 27 : ℤ) + (x 26 : ℤ) ^ 2 + (-1) * ((x 14 : ℤ) ^ 2) = 0 at h17
  change (x 28 : ℤ) + (-1) * ((x 6 : ℤ) * x 23) = 0 at h18
  change (x 29 : ℤ) + (-1) * ((x 28 : ℤ) ^ 2) = 0 at h19
  change (x 30 : ℤ) + x 29 + (-1) * ((x 25 : ℤ) * x 30) = 0 at h20
  change (-1 : ℤ) + (-1) * ((x 27 : ℤ) * x 29) + (x 14 : ℤ) ^ 2 = 0 at h21
  have hδ : (x 30 : ℤ) = ((x 20 : ℤ) + 2) ^ 2 - 1 := by linear_combination h9
  have hC2 : (x 23 : ℤ) = (x 19 : ℤ) ^ 2 := by linear_combination h10
  have hF2 : (x 25 : ℤ) = (x 4 : ℤ) ^ 2 := by linear_combination h15
  have hI : (x 28 : ℤ) = (x 6 : ℤ) * x 19 ^ 2 := by rw [hC2] at h18; linear_combination h18
  have hB : (x 29 : ℤ) = ((x 6 : ℤ) * x 19 ^ 2) ^ 2 := by rw [hI] at h19; linear_combination h19
  have hstrongZ : ((x 6 : ℤ) * x 19 ^ 2) ^ 2 =
      (((x 20 : ℤ) + 2) ^ 2 - 1) * ((x 4 : ℤ) ^ 2 - 1) := by
    rw [hδ,hB,hF2] at h20
    linear_combination h20
  refine ⟨?_,?_⟩
  · have hA2 : 1 ≤ (x 20 + 2) ^ 2 := Nat.one_le_pow _ _ (by omega)
    have hf2 : 1 ≤ x 4 ^ 2 := Nat.one_le_pow _ _ (hx 4)
    have hz : (((x 6 * x 19 ^ 2) ^ 2 : ℕ) : ℤ) =
        ((((x 20 + 2) ^ 2 - 1) * (x 4 ^ 2 - 1) : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub hA2,Nat.cast_sub hf2]
      exact hstrongZ
    exact_mod_cast hz
  · rw [hB] at h21
    linear_combination h21 + ((x 6 : ℤ) * x 19 ^ 2) ^ 2 * h17

/-- The literal positive OLD-z source and the generic native port box recover
both exact main Pell coordinates at the INNER native rank. This is an
arithmetic theorem with parameterized coefficient ports, not native K215
calibration or an object-language consistency theorem. -/
theorem source_main_index_exact (ports : Fin 4 → ℤ) (hports : PortBox ports)
    (x : Fin 31 → ℕ) (hx : ∀ i, 0 < x i)
    (hs : ∀ k, SplitCertificate59.sourceRows ports (fun i => (x i : ℤ)) k = 0) :
    x 22 = xn (by omega : 1 < x 20 + 2) (nativeRank x).toNat ∧
      x 19 = yn (by omega : 1 < x 20 + 2) (nativeRank x).toNat := by
  obtain ⟨p,hp,hD,hc,hbig,hpc,hRc⟩ := source_bootstrap_of_portBox ports hports x hx hs
  obtain ⟨hstrong,haux⟩ := source_auxiliary_norms ports x hx hs
  have hR24 := source_native_rank_ge_twentyfour ports hports.beta_pos hports.K_nonneg
    hports.MC_nonneg hports.MF_nonneg x hx hs
  let R := (nativeRank x).toNat
  have hR : (R : ℤ) = nativeRank x := Int.toNat_of_nonneg (by omega)
  have hRpos : 0 < R := by omega
  have hRhalf : 2 * R < x 19 := by omega
  have hVj : (x 26 : ℤ) = (x 8 : ℤ) * x 19 - R := by
    dsimp [nativeRank] at hR
    linear_combination hR
  have h16 := hs 16
  change (x 26 : ℤ) + x 19 + (-1) * ((x 4 : ℤ) * x 7) = 0 at h16
  have hVo : (x 26 : ℤ) = (x 7 : ℤ) * x 4 - x 19 := by linear_combination h16
  have haux' : ((x 6 * x 19 ^ 2 : ℕ) : ℤ) ^ 2 * (x 26 : ℤ) ^ 2 -
      (((x 6 * x 19 ^ 2 : ℕ) : ℤ) ^ 2 - 1) * (x 14 : ℤ) ^ 2 = 1 := by
    simpa only [Nat.cast_mul,Nat.cast_pow] using haux
  have hpR : p = R := NativePellStepDown.source_index_of_strong (by omega) (by omega)
    hRpos hc (hx 6) (hx 4) hbig hpc hRhalf hstrong (hx 14) haux' hVj hVo
  exact ⟨by simpa only [hpR] using hD,by simpa only [hpR] using hc⟩

end DiophantineConsistency.NativePellBootstrap
