import Diophantine.Paper1978.Enumeration
import Mathlib.Data.Nat.ChineseRemainder

/-!
# Jones 1978, §3: Gödel's β-function and Lemma 3.2

`M(i) = 1 + (1+i)β` and `S(R, β, i)` is the absolutely least residue of `R` modulo `M(i)`:
`R ≡ S (mod M(i))` and `−M(i) < 2S ≤ M(i)`.  For any integers `T₀, …, T_τ` there are `R, β`
with `S(R, β, i) = Tᵢ` (`i ≤ τ`), by the Chinese Remainder Theorem, since the moduli `M(i)`
are pairwise coprime whenever `(τ+1)!` divides `β`.

> **Lemma 3.2.** For positive integers `n, x`: `x ∈ Wₙ` iff there are `u, v, R, β ≥ 0` with
> `J(u,v) = n ∧ S(R,β,0) = 0 ∧ S(R,β,u) = S(R,β,v) + x ∧`
> `(∀ i < n)[S(R,β,3i) = S(R,β,K(i)) + S(R,β,L(i)) ∧ S(R,β,3i+1) = S(R,β,K(i))·S(R,β,L(i))]`.

The least nonnegative residues `S₊(R, β, j) = R mod (1 + jβ)`, used for the
nonnegative-witness enumeration of Theorems 1 and 2, are treated alongside.
-/

namespace Jones1978

open Finset Function

/-! ### Pairwise coprime moduli `1 + jβ` -/

/-- For `τ! ∣ β`, the moduli `1 + jβ` (`1 ≤ j ≤ τ`, or any `j ≤ τ`) are pairwise coprime. -/
theorem coprime_one_add_mul {β τ j j' : ℕ} (hβ : τ.factorial ∣ β) (hj : j ≤ τ) (hj' : j' ≤ τ)
    (hne : j ≠ j') : Nat.Coprime (1 + j * β) (1 + j' * β) := by
  wlog hlt : j < j' generalizing j j'
  · exact (this hj' hj (Ne.symm hne) (by omega)).symm
  rw [Nat.Coprime]
  set g := Nat.gcd (1 + j * β) (1 + j' * β) with hg
  have hg1 : g ∣ 1 + j * β := Nat.gcd_dvd_left _ _
  have hg2 : g ∣ 1 + j' * β := Nat.gcd_dvd_right _ _
  -- `g` is coprime to `β`
  have hgβ : Nat.Coprime g β := by
    rw [Nat.Coprime]
    have h1 : Nat.gcd g β ∣ 1 + j * β := (Nat.gcd_dvd_left _ _).trans hg1
    have h2 : Nat.gcd g β ∣ j * β := Dvd.dvd.mul_left (Nat.gcd_dvd_right _ _) _
    have := Nat.dvd_sub h1 h2
    rw [Nat.add_sub_cancel] at this
    exact Nat.dvd_one.1 this
  -- `g ∣ (j' − j) β`, hence `g ∣ j' − j ∣ τ! ∣ β`
  have h3 : g ∣ (j' - j) * β := by
    have := Nat.dvd_sub hg2 hg1
    rwa [show 1 + j' * β - (1 + j * β) = (j' - j) * β by
      rw [Nat.sub_mul]; omega] at this
  have h4 : g ∣ j' - j := hgβ.dvd_of_dvd_mul_right h3
  have h5 : j' - j ∣ β := (Nat.dvd_factorial (by omega) (by omega)).trans hβ
  have h6 : g ∣ β := h4.trans h5
  have := Nat.dvd_sub hg1 (Dvd.dvd.mul_left h6 j)
  rw [Nat.add_sub_cancel] at this
  exact Nat.dvd_one.1 this

/-- Least nonnegative residues: for any `T : ℕ → ℕ` and `τ` there are `a, b` with
`a mod (1 + k b) = T k` for `1 ≤ k ≤ τ`, and with `τ! ∣ b` and `b ≥ 1`. -/
theorem exists_residues (T : ℕ → ℕ) (τ : ℕ) :
    ∃ a b : ℕ, 0 < b ∧ τ.factorial ∣ b ∧ ∀ k, 1 ≤ k → k ≤ τ → a % (1 + k * b) = T k := by
  classical
  set b := τ.factorial * (1 + ∑ k ∈ range (τ + 1), T k) with hb
  have hb0 : 0 < b := by positivity
  have hbT : ∀ k ≤ τ, T k < b := by
    intro k hk
    have h1 : T k ≤ ∑ k ∈ range (τ + 1), T k :=
      Finset.single_le_sum (f := T) (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 (by omega))
    have h2 : 1 ≤ τ.factorial := Nat.factorial_pos τ
    calc T k < 1 + ∑ k ∈ range (τ + 1), T k := by omega
      _ ≤ τ.factorial * (1 + ∑ k ∈ range (τ + 1), T k) := Nat.le_mul_of_pos_left _ h2
  have hpp : Set.Pairwise (↑(Finset.Icc 1 τ) : Set ℕ) (Nat.Coprime on fun k => 1 + k * b) := by
    intro k hk k' hk' hne
    simp only [Finset.coe_Icc, Set.mem_Icc] at hk hk'
    exact coprime_one_add_mul (dvd_mul_right _ _) hk.2 hk'.2 hne
  obtain ⟨a, ha⟩ := Nat.chineseRemainderOfFinset T (fun k => 1 + k * b) (Finset.Icc 1 τ)
    (fun k _ => by omega) hpp
  refine ⟨a, b, hb0, dvd_mul_right _ _, fun k hk1 hkτ => ?_⟩
  have h := ha k (Finset.mem_Icc.2 ⟨hk1, hkτ⟩)
  unfold Nat.ModEq at h
  rw [h]
  apply Nat.mod_eq_of_lt
  have := hbT k hkτ
  have : b ≤ k * b := Nat.le_mul_of_pos_left _ hk1
  omega

/-! ### Absolutely least residues -/

/-- The modulus `M(i) = 1 + (1+i)β`. -/
def Mg (β i : ℕ) : ℕ := 1 + (1 + i) * β

/-- `S(R, β, i)`: the absolutely least residue of `R` modulo `M(i)`. -/
def S (R β i : ℕ) : ℤ :=
  if 2 * ((R : ℤ) % (Mg β i : ℤ)) ≤ (Mg β i : ℤ) then (R : ℤ) % (Mg β i : ℤ)
  else (R : ℤ) % (Mg β i : ℤ) - Mg β i

theorem Mg_pos (β i : ℕ) : 0 < Mg β i := by unfold Mg; omega

theorem S_spec (R β i : ℕ) :
    (R : ℤ) ≡ S R β i [ZMOD Mg β i] ∧ -(Mg β i : ℤ) < 2 * S R β i ∧ 2 * S R β i ≤ Mg β i := by
  have hM : (0 : ℤ) < Mg β i := by exact_mod_cast Mg_pos β i
  have h0 : 0 ≤ (R : ℤ) % (Mg β i : ℤ) := Int.emod_nonneg _ hM.ne'
  have h1 : (R : ℤ) % (Mg β i : ℤ) < Mg β i := Int.emod_lt_of_pos _ hM
  have hmod : (R : ℤ) ≡ (R : ℤ) % (Mg β i : ℤ) [ZMOD Mg β i] := (Int.mod_modEq _ _).symm
  unfold S
  split_ifs with h
  · exact ⟨hmod, by linarith, h⟩
  · refine ⟨?_, by linarith, by linarith⟩
    have hsub : (R : ℤ) % (Mg β i : ℤ) ≡ (R : ℤ) % (Mg β i : ℤ) - Mg β i [ZMOD Mg β i] :=
      Int.modEq_iff_dvd.2 ⟨-1, by ring⟩
    exact hmod.trans hsub

/-- Uniqueness of the absolutely least residue. -/
theorem S_unique {R β i : ℕ} {T : ℤ} (h1 : (R : ℤ) ≡ T [ZMOD Mg β i])
    (h2 : -(Mg β i : ℤ) < 2 * T) (h3 : 2 * T ≤ Mg β i) : S R β i = T := by
  obtain ⟨hc, hlo, hhi⟩ := S_spec R β i
  have hM : (0 : ℤ) < Mg β i := by exact_mod_cast Mg_pos β i
  have hdvd : (Mg β i : ℤ) ∣ S R β i - T := (h1.symm.trans hc).dvd
  have habs : |S R β i - T| < Mg β i := by
    rw [abs_lt]; constructor <;> linarith
  have := Int.eq_zero_of_abs_lt_dvd hdvd habs
  linarith

/-- A suitable `β`: divisible by `(τ+1)!`, above `βmin`, and above `2|Tᵢ|` for `i ≤ τ`. -/
theorem exists_good_β (T : ℕ → ℤ) (τ βmin : ℕ) :
    ∃ β : ℕ, βmin ≤ β ∧ (τ + 1).factorial ∣ β ∧ ∀ i ≤ τ, 2 * (T i).natAbs < β := by
  classical
  refine ⟨(τ + 1).factorial * (1 + 2 * ∑ i ∈ range (τ + 1), (T i).natAbs + βmin), ?_,
    dvd_mul_right _ _, ?_⟩
  · have h2 : 1 ≤ (τ + 1).factorial := Nat.factorial_pos _
    calc βmin ≤ 1 + 2 * ∑ i ∈ range (τ + 1), (T i).natAbs + βmin := by omega
      _ ≤ _ := Nat.le_mul_of_pos_left _ h2
  · intro i hi
    have h1 : (T i).natAbs ≤ ∑ i ∈ range (τ + 1), (T i).natAbs :=
      Finset.single_le_sum (f := fun i => (T i).natAbs) (fun _ _ => Nat.zero_le _)
        (Finset.mem_range.2 (by omega))
    have h2 : 1 ≤ (τ + 1).factorial := Nat.factorial_pos _
    calc 2 * (T i).natAbs ≤ 2 * ∑ i ∈ range (τ + 1), (T i).natAbs := Nat.mul_le_mul_left _ h1
      _ < 1 + 2 * ∑ i ∈ range (τ + 1), (T i).natAbs + βmin := by omega
      _ ≤ _ := Nat.le_mul_of_pos_left _ h2

/-- Gödel's lemma for a given good `β`, with `R` above a prescribed bound. -/
theorem exists_S_eq_of_β (T : ℕ → ℤ) (τ Rmin β : ℕ) (hβ : (τ + 1).factorial ∣ β)
    (hβT : ∀ i ≤ τ, 2 * (T i).natAbs < β) :
    ∃ R : ℕ, Rmin ≤ R ∧ ∀ i ≤ τ, S R β i = T i := by
  classical
  have hpp : Set.Pairwise (↑(range (τ + 1)) : Set ℕ) (Nat.Coprime on Mg β) := by
    intro i hi i' hi' hne
    simp only [Finset.coe_range, Set.mem_Iio] at hi hi'
    show Nat.Coprime (1 + (1 + i) * β) (1 + (1 + i') * β)
    exact coprime_one_add_mul (τ := τ + 1) hβ (by omega) (by omega) (by omega)
  set r : ℕ → ℕ := fun i => (T i % (Mg β i : ℤ)).toNat with hr
  obtain ⟨R₀, hR₀⟩ := Nat.chineseRemainderOfFinset r (Mg β) (range (τ + 1))
    (fun i _ => (Mg_pos β i).ne') hpp
  -- shift `R₀` above `Rmin` by a multiple of all the moduli
  set Pr := ∏ i ∈ range (τ + 1), Mg β i with hPr
  have hPr1 : 1 ≤ Pr := Nat.one_le_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 (fun i _ => (Mg_pos β i).ne'))
  refine ⟨R₀ + Rmin * Pr, by nlinarith, fun i hi => ?_⟩
  have hM : (0 : ℤ) < Mg β i := by exact_mod_cast Mg_pos β i
  have hri : (r i : ℤ) = T i % (Mg β i : ℤ) := by
    simp only [hr]
    exact Int.toNat_of_nonneg (Int.emod_nonneg _ hM.ne')
  have hRr : (R₀ + Rmin * Pr : ℕ) ≡ r i [MOD Mg β i] := by
    have h1 : R₀ + Rmin * Pr ≡ R₀ [MOD Mg β i] := by
      have : Mg β i ∣ Rmin * Pr :=
        Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ (Finset.mem_range.2 (by omega))) _
      exact ((Nat.modEq_iff_dvd' (Nat.le_add_right _ _)).2 (by rwa [Nat.add_sub_cancel_left])).symm
    exact h1.trans (hR₀ i (Finset.mem_range.2 (by omega)))
  have hRT : ((R₀ + Rmin * Pr : ℕ) : ℤ) ≡ T i [ZMOD Mg β i] := by
    have := Int.natCast_modEq_iff.2 hRr
    rw [hri] at this
    exact this.trans (Int.mod_modEq _ _)
  apply S_unique hRT
  · have := hβT i hi
    have h1 : (2 * (T i).natAbs : ℤ) < β := by exact_mod_cast this
    have h2 : (Mg β i : ℤ) = 1 + (1 + i) * β := by unfold Mg; push_cast; ring
    have h3 : (β : ℤ) ≤ (1 + i) * β := by nlinarith
    have h5 : -|T i| ≤ T i := neg_abs_le (T i)
    have h6 : ((T i).natAbs : ℤ) = |T i| := Int.natCast_natAbs (T i)
    rw [h2]; linarith
  · have := hβT i hi
    have h1 : (2 * (T i).natAbs : ℤ) < β := by exact_mod_cast this
    have h2 : (Mg β i : ℤ) = 1 + (1 + i) * β := by unfold Mg; push_cast; ring
    have h3 : (β : ℤ) ≤ (1 + i) * β := by nlinarith
    have h5 : T i ≤ |T i| := le_abs_self (T i)
    have h6 : ((T i).natAbs : ℤ) = |T i| := Int.natCast_natAbs (T i)
    rw [h2]; linarith

/-- Gödel's lemma with `R` and `β` above prescribed bounds. -/
theorem exists_S_eq' (T : ℕ → ℤ) (τ Rmin βmin : ℕ) :
    ∃ R β : ℕ, Rmin ≤ R ∧ βmin ≤ β ∧ ∀ i ≤ τ, S R β i = T i := by
  obtain ⟨β, hβmin, hβ, hβT⟩ := exists_good_β T τ βmin
  obtain ⟨R, hR, hS⟩ := exists_S_eq_of_β T τ Rmin β hβ hβT
  exact ⟨R, β, hR, hβmin, hS⟩

/-- Any integer sequence `T₀, …, T_τ` is coded by some `R, β` (Gödel's lemma). -/
theorem exists_S_eq (T : ℕ → ℤ) (τ : ℕ) : ∃ R β : ℕ, ∀ i ≤ τ, S R β i = T i := by
  obtain ⟨R, β, _, _, hS⟩ := exists_S_eq' T τ 0 0
  exact ⟨R, β, hS⟩

/-- `M(i)` as an integer. -/
theorem Mg_cast (β i : ℕ) : (Mg β i : ℤ) = 1 + (1 + i) * β := by unfold Mg; push_cast; ring

theorem Mg_ge (β i : ℕ) : (1 + β : ℤ) ≤ Mg β i := by
  rw [Mg_cast]
  have : (0:ℤ) ≤ i * β := by positivity
  nlinarith

theorem Mg_ge_of_pos {β i : ℕ} (hi : 1 ≤ i) : (1 + 2 * β : ℤ) ≤ Mg β i := by
  rw [Mg_cast]
  have : (1 : ℤ) ≤ i := by exact_mod_cast hi
  nlinarith

theorem Mg_ge_of_ge {β i k : ℕ} (hi : k ≤ i) : (1 + (1 + k) * β : ℤ) ≤ Mg β i := by
  rw [Mg_cast]
  have : (k : ℤ) ≤ i := by exact_mod_cast hi
  nlinarith

/-- `S(R, β, i) = T` as soon as `R ≡ T` and `4T² < M(i)²`. -/
theorem S_eq_of_sq_lt {R β i : ℕ} {T : ℤ} (h1 : (R : ℤ) ≡ T [ZMOD Mg β i])
    (h2 : 4 * T ^ 2 < (Mg β i : ℤ) ^ 2) : S R β i = T := by
  have hM : (0 : ℤ) < Mg β i := by exact_mod_cast Mg_pos β i
  have h3 : |2 * T| < Mg β i := by
    apply abs_lt_of_sq_lt_sq _ hM.le
    nlinarith
  rw [abs_lt] at h3
  exact S_unique h1 (by linarith) (by linarith)

/-! ### Lemma 3.2 -/

/-- The condition (3.2). -/
def Cond32 (n x u v R β : ℕ) : Prop :=
  J u v = n ∧ S R β 0 = 0 ∧ S R β u = S R β v + x ∧
    ∀ i < n, S R β (3 * i) = S R β (K i) + S R β (L i) ∧
      S R β (3 * i + 1) = S R β (K i) * S R β (L i)

theorem K_zero : K 0 = 0 := rfl
theorem L_zero : L 0 = 0 := rfl

/-- `P_{3i} = P_{K(i)} + P_{L(i)}` also for `i = 0`. -/
theorem P_add' (i : ℕ) (X : ℕ → ℤ) : P (3 * i) X = P (K i) X + P (L i) X := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp [K_zero, L_zero, P_zero]
  · exact P_add hi X

/-- If `S(R,β,·)` satisfies the recursions up to `n` and `X_j = S(R,β,3j+2)`, then
`S(R,β,k) = P_k(X)` for all `k ≤ 3n - 1`. -/
theorem S_eq_P {n : ℕ} {S' : ℕ → ℤ} (h0 : S' 0 = 0)
    (hrec : ∀ i < n, S' (3 * i) = S' (K i) + S' (L i) ∧ S' (3 * i + 1) = S' (K i) * S' (L i)) :
    ∀ k ≤ 3 * n - 1, S' k = P k (fun j => S' (3 * j + 2)) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · rw [h0, P_zero]
    have hmod : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases hmod with h | h | h
    · -- `k = 3i` with `1 ≤ i < n`
      obtain ⟨i, rfl⟩ : ∃ i, k = 3 * i := ⟨k / 3, by omega⟩
      have hi : i < n := by omega
      have hi1 : 1 ≤ i := by omega
      rw [P_add hi1, (hrec i hi).1, ← ih (K i) (by have := K_le i; omega) (by have := K_le i; omega),
        ← ih (L i) (by have := L_le i; omega) (by have := L_le i; omega)]
    · obtain ⟨i, rfl⟩ : ∃ i, k = 3 * i + 1 := ⟨k / 3, by omega⟩
      have hi : i < n := by omega
      rw [P_mul, (hrec i hi).2, ← ih (K i) (by have := K_le i; omega) (by have := K_le i; omega),
        ← ih (L i) (by have := L_le i; omega) (by have := L_le i; omega)]
    · obtain ⟨i, rfl⟩ : ∃ i, k = 3 * i + 2 := ⟨k / 3, by omega⟩
      rw [P_var]

/-- **Lemma 3.2.** -/
theorem lemma_3_2 {n x : ℕ} (hn : 0 < n) :
    x ∈ W n ↔ ∃ u v R β, Cond32 n x u v R β := by
  constructor
  · rintro ⟨X, hX⟩
    obtain ⟨R, β, hRβ⟩ := exists_S_eq (fun k => P k X) (3 * n + 1)
    refine ⟨K n, L n, R, β, J_K_L n, ?_, ?_, fun i hi => ⟨?_, ?_⟩⟩
    · rw [hRβ 0 (by omega), P_zero]
    · rw [hRβ (K n) (by have := K_le n; omega), hRβ (L n) (by have := L_le n; omega), hX]
    · rw [hRβ (3 * i) (by omega), hRβ (K i) (by have := K_le i; omega),
        hRβ (L i) (by have := L_le i; omega), P_add']
    · rw [hRβ (3 * i + 1) (by omega), hRβ (K i) (by have := K_le i; omega),
        hRβ (L i) (by have := L_le i; omega), P_mul]
  · rintro ⟨u, v, R, β, hJ, h0, huv, hrec⟩
    obtain ⟨rfl, rfl⟩ := J_eq_iff.1 hJ
    have key := S_eq_P (n := n) h0 hrec
    refine ⟨fun j => S R β (3 * j + 2), ?_⟩
    rw [← key (K n) (by have := K_le n; omega), ← key (L n) (by have := L_le n; omega)]
    exact huv

/-! ### Least nonnegative residues and the enumeration `Ŵₙ` -/

/-- `S₊(R, β, j) = R mod (1 + jβ)`. -/
def Sp (R β j : ℕ) : ℕ := R % (1 + j * β)

theorem Sp_zero (R β : ℕ) : Sp R β 0 = 0 := by simp [Sp, Nat.mod_one]

theorem Sp_le (R β j : ℕ) : Sp R β j ≤ j * β := by
  have := Nat.mod_lt R (show 0 < 1 + j * β by omega)
  unfold Sp; omega

/-- The residue condition of Theorem 1: `v = S₊(a, b, j)` iff
`∃ e g, a = v + e + e j b ∧ v + g = j b`. -/
theorem Sp_iff (a b j v : ℕ) :
    v = Sp a b j ↔ ∃ e g : ℕ, a = v + e + e * j * b ∧ v + g = j * b := by
  constructor
  · rintro rfl
    refine ⟨a / (1 + j * b), j * b - Sp a b j, ?_, by have := Sp_le a b j; omega⟩
    have := Nat.div_add_mod a (1 + j * b)
    unfold Sp
    nlinarith [this]
  · rintro ⟨e, g, h1, h2⟩
    unfold Sp
    have : a = v + (1 + j * b) * e := by rw [h1]; ring
    rw [this, Nat.add_mul_mod_self_left]
    exact (Nat.mod_eq_of_lt (by omega)).symm

/-- The nonnegative-witness enumeration `Ŵₙ`. -/
def Wh (n : ℕ) : Set ℕ :=
  {x | ∃ X : ℕ → ℕ, P (K n) (fun i => (X i : ℤ)) = P (L n) (fun i => (X i : ℤ)) + x}

/-- The `ℕ`-valued version of `S_eq_P` for `S₊`. -/
theorem Sp_eq_P {a b n : ℕ}
    (hrec : ∀ i ≤ n, Sp a b (3 * i) = Sp a b (K i) + Sp a b (L i) ∧
      Sp a b (3 * i + 1) = Sp a b (K i) * Sp a b (L i)) :
    ∀ k ≤ 3 * n + 1, (Sp a b k : ℤ) = P k (fun j => (Sp a b (3 * j + 2) : ℤ)) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · rw [Sp_zero, P_zero]; rfl
    have hmod : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases hmod with h | h | h
    · obtain ⟨i, rfl⟩ : ∃ i, k = 3 * i := ⟨k / 3, by omega⟩
      have hi : i ≤ n := by omega
      have hi1 : 1 ≤ i := by omega
      rw [P_add hi1, (hrec i hi).1, ← ih (K i) (by have := K_le i; omega) (by have := K_le i; omega),
        ← ih (L i) (by have := L_le i; omega) (by have := L_le i; omega)]
      push_cast; ring
    · obtain ⟨i, rfl⟩ : ∃ i, k = 3 * i + 1 := ⟨k / 3, by omega⟩
      have hi : i ≤ n := by omega
      rw [P_mul, (hrec i hi).2, ← ih (K i) (by have := K_le i; omega) (by have := K_le i; omega),
        ← ih (L i) (by have := L_le i; omega) (by have := L_le i; omega)]
      push_cast; ring
    · obtain ⟨i, rfl⟩ : ∃ i, k = 3 * i + 2 := ⟨k / 3, by omega⟩
      rw [P_var]

end Jones1978
