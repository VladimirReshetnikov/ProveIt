import Diophantine.Paper1978.Combining
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Jones 1978, Lemma 2.3: the Bounded Quantifier Theorem

> **Lemma 2.3.** Let `P(y, z₁, …, zₙ)` be a polynomial (`n ≥ 1`) and `R(z)` a dominating
> function: (D) `y, z₁, …, zₙ < z ⟹ |P(y, z₁, …, zₙ)| ≤ R(z)`.  Then
> (A) `(∀ y < τ)(∃ z₁ … zₙ) P(y, z₁, …, zₙ) = 0`
> holds iff there are integers `z ≥ 1` and `r, z₁, …, zₙ ≥ 0` with
> (i) `P(r, z₁, …, zₙ)(τ + z₁ − r) ≡ 0 (mod C(r, z))`, (ii) `τ ≤ z`,
> (iii) `(2 z z! R(z))^(zⁿ) + z ≤ r`, (iv) `C(r, z) ∣ C(zᵢ, z)` for `i = 1, …, n`.

The only property of the polynomial `P` used in the proof is that it respects
congruences: `y ≡ y'`, `zᵢ ≡ zᵢ' (mod p)` imply `P(y, z) ≡ P(y', z') (mod p)`.  The theorem
is stated for an arbitrary function `P : ℕ → (Fin (m+1) → ℕ) → ℤ` with this property
(`CongPreserving`); every integer polynomial has it.  The `n = m + 1` unknowns are indexed
by `Fin (m + 1)`, and `z₁` is `zs 0`.
-/

namespace Jones1978

open Finset Function

variable {m : ℕ}

/-- `P` respects congruences in all of its arguments (as every polynomial does). -/
def CongPreserving (P : ℕ → (Fin (m + 1) → ℕ) → ℤ) : Prop :=
  ∀ (p y y' : ℕ) (z z' : Fin (m + 1) → ℕ), y ≡ y' [MOD p] → (∀ i, z i ≡ z' i [MOD p]) →
    P y z ≡ P y' z' [ZMOD p]

/-- Condition (D) at one value `z`: `|P(y, zs)| ≤ R z` whenever `y, zs < z`. -/
def DominatesAt (P : ℕ → (Fin (m + 1) → ℕ) → ℤ) (R : ℕ → ℕ) (z : ℕ) : Prop :=
  ∀ (y : ℕ) (zs : Fin (m + 1) → ℕ), y < z → (∀ i, zs i < z) → |P y zs| ≤ R z

/-- Condition (D): `R` dominates `P`. -/
def Dominates (P : ℕ → (Fin (m + 1) → ℕ) → ℤ) (R : ℕ → ℕ) : Prop :=
  ∀ z, DominatesAt P R z

/-- The conditions (i)–(iv) of the Bounded Quantifier Theorem. -/
structure BQTConds (P : ℕ → (Fin (m + 1) → ℕ) → ℤ) (R : ℕ → ℕ) (τ z r : ℕ)
    (zs : Fin (m + 1) → ℕ) : Prop where
  z_pos : 1 ≤ z
  i : (r.choose z : ℤ) ∣ P r zs * ((τ : ℤ) + zs 0 - r)
  ii : τ ≤ z
  iii : (2 * z * z.factorial * R z) ^ (z ^ (m + 1)) + z ≤ r
  iv : ∀ i, r.choose z ∣ (zs i).choose z

/-! ### Sufficiency -/

/-- The iterated Divisor Lemma: from `p₀ ∣ ∏_{j<z} (aᵢ − j)` for `k` numbers `aᵢ` we get
`p ∣ p₀` with `p₀ ≤ p^(z^k)` and every `aᵢ` congruent modulo `p` to some `aᵢ' < z`. -/
theorem chain {z : ℕ} (hz : 0 < z) : ∀ (k : ℕ) (p₀ : ℕ) (a : Fin k → ℕ),
    (∀ i, p₀ ∣ (a i).descFactorial z) →
    ∃ p, p ∣ p₀ ∧ p₀ ≤ p ^ (z ^ k) ∧ ∀ i, ∃ a' < z, a i ≡ a' [MOD p]
  | 0, p₀, _, _ => ⟨p₀, dvd_refl _, by simp, fun i => i.elim0⟩
  | k + 1, p₀, a, ha => by
    have h0 := ha 0
    rw [Nat.descFactorial_eq_prod_range] at h0
    obtain ⟨j, hj, p₁, hp₁, hp₁j, hle₁⟩ := divisor_lemma hz _ h0
    obtain ⟨p, hp, hle, hres⟩ := chain hz k p₁ (fun i => a i.succ)
      (fun i => (hp₁.trans (ha i.succ)))
    refine ⟨p, hp.trans hp₁, ?_, ?_⟩
    · calc p₀ ≤ p₁ ^ z := hle₁
        _ ≤ (p ^ (z ^ k)) ^ z := Nat.pow_le_pow_left hle z
        _ = p ^ (z ^ (k + 1)) := by rw [← pow_mul, pow_succ]
    · intro i
      refine Fin.cases ?_ (fun i => hres i) i
      -- the first number: `p₁ ∣ a 0 − j`
      rcases le_or_gt j (a 0) with hja | hja
      · refine ⟨j, hj, ?_⟩
        have : j ≡ a 0 [MOD p₁] := (Nat.modEq_iff_dvd' hja).2 hp₁j
        exact (Nat.ModEq.of_dvd hp this).symm
      · exact ⟨a 0, by omega, Nat.ModEq.refl _⟩

theorem bqt_sufficiency {P : ℕ → (Fin (m + 1) → ℕ) → ℤ} (hP : CongPreserving P) {R : ℕ → ℕ}
    {τ z r : ℕ} (hR : DominatesAt P R z) {zs : Fin (m + 1) → ℕ} (h : BQTConds P R τ z r zs) :
    ∀ y < τ, ∃ zs, P y zs = 0 := by
  intro y hy
  have hyz : y < z := lt_of_lt_of_le hy h.ii
  have hzr : z ≤ r := le_trans (Nat.le_add_left _ _) h.iii
  have hyr : y ≤ r := by omega
  -- `r − y ∣ z! C(r, z)`
  have hdvd1 : r - y ∣ z.factorial * r.choose z := by
    rw [← Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_prod_range]
    exact Finset.dvd_prod_of_mem (fun j => r - j) (Finset.mem_range.2 hyz)
  -- hence `r − y ∣ ∏_{j<z} (zᵢ − j)`
  have hdvd2 : ∀ i, r - y ∣ (zs i).descFactorial z := by
    intro i
    rw [Nat.descFactorial_eq_factorial_mul_choose]
    exact hdvd1.trans (Nat.mul_dvd_mul_left _ (h.iv i))
  obtain ⟨p, hp, hle, hres⟩ := chain h.z_pos (m + 1) (r - y) zs hdvd2
  choose zs' hzs' hcong using hres
  -- `p > 2 z z! R(z)`
  have hpB : 2 * z * z.factorial * R z < p := by
    by_contra hcon
    push Not at hcon
    have h1 : p ^ (z ^ (m + 1)) ≤ (2 * z * z.factorial * R z) ^ (z ^ (m + 1)) :=
      Nat.pow_le_pow_left hcon _
    have h2 := h.iii
    omega
  have hp0 : 0 < p := by omega
  -- the congruence (2)
  have hyr' : y ≡ r [MOD p] := (Nat.modEq_iff_dvd' hyr).2 hp
  have hPc : P y zs' ≡ P r zs [ZMOD p] := hP p y r zs' zs hyr' (fun i => (hcong i).symm)
  have hX : (z.factorial : ℤ) * P y zs' * ((τ : ℤ) + zs' 0 - y)
      ≡ (z.factorial : ℤ) * P r zs * ((τ : ℤ) + zs 0 - r) [ZMOD p] := by
    have hy' : (y : ℤ) ≡ r [ZMOD p] := Int.natCast_modEq_iff.2 hyr'
    have hz0 : ((zs' 0 : ℕ) : ℤ) ≡ zs 0 [ZMOD p] := Int.natCast_modEq_iff.2 (hcong 0).symm
    exact ((Int.ModEq.refl _).mul hPc).mul (((Int.ModEq.refl _).add hz0).sub hy')
  have hdiv : (p : ℤ) ∣ (z.factorial : ℤ) * P r zs * ((τ : ℤ) + zs 0 - r) := by
    have h1 : ((r - y : ℕ) : ℤ) ∣ (z.factorial : ℤ) * (r.choose z : ℤ) := by
      exact_mod_cast hdvd1
    have h2 : (p : ℤ) ∣ ((r - y : ℕ) : ℤ) := by exact_mod_cast hp
    calc (p : ℤ) ∣ (z.factorial : ℤ) * (r.choose z : ℤ) := h2.trans h1
      _ ∣ (z.factorial : ℤ) * (P r zs * ((τ : ℤ) + zs 0 - r)) := Int.mul_dvd_mul_left _ h.i
      _ = (z.factorial : ℤ) * P r zs * ((τ : ℤ) + zs 0 - r) := by ring
  have hdivX : (p : ℤ) ∣ (z.factorial : ℤ) * P y zs' * ((τ : ℤ) + zs' 0 - y) := by
    have h1 := hX.dvd
    have := dvd_sub hdiv h1
    simpa using this
  -- the bound (3)
  have hbound : |(z.factorial : ℤ) * P y zs' * ((τ : ℤ) + zs' 0 - y)| < p := by
    have hPy : |P y zs'| ≤ R z := hR y zs' hyz hzs'
    have hfac : (0 : ℤ) < z.factorial := by exact_mod_cast Nat.factorial_pos z
    have hlin : (0 : ℤ) < (τ : ℤ) + zs' 0 - y ∧ (τ : ℤ) + zs' 0 - y ≤ 2 * z - 1 := by
      have h1 : (y : ℤ) < τ := by exact_mod_cast hy
      have h2 : ((zs' 0 : ℕ) : ℤ) < z := by exact_mod_cast hzs' 0
      have h3 : (τ : ℤ) ≤ z := by exact_mod_cast h.ii
      constructor <;> linarith
    rw [abs_mul, abs_mul, abs_of_pos hfac, abs_of_pos hlin.1]
    have hBp : ((2 * z * z.factorial * R z : ℕ) : ℤ) < p := by exact_mod_cast hpB
    have hRz : (0 : ℤ) ≤ R z := by exact_mod_cast Nat.zero_le _
    have hz1 : (1 : ℤ) ≤ z := by exact_mod_cast h.z_pos
    push_cast at hBp
    calc (z.factorial : ℤ) * |P y zs'| * ((τ : ℤ) + zs' 0 - y)
        ≤ (z.factorial : ℤ) * R z * (2 * z - 1) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hPy hfac.le) hlin.2 hlin.1.le
          positivity
      _ ≤ 2 * z * z.factorial * R z := by nlinarith [mul_nonneg hfac.le hRz]
      _ < p := hBp
  have hX0 := Int.eq_zero_of_abs_lt_dvd hdivX hbound
  refine ⟨zs', ?_⟩
  rcases mul_eq_zero.1 hX0 with h1 | h1
  · rcases mul_eq_zero.1 h1 with h2 | h2
    · exact absurd h2 (by exact_mod_cast (Nat.factorial_pos z).ne')
    · exact h2
  · exfalso
    have h2 : (y : ℤ) < τ := by exact_mod_cast hy
    have : (0 : ℤ) ≤ ((zs' 0 : ℕ) : ℤ) := by positivity
    linarith

/-! ### Necessity -/

/-- The moduli `M y = (r+1)/(y+1) − 1` of (4). -/
def Mod (r y : ℕ) : ℕ := (r + 1) / (y + 1) - 1

theorem Mod_mul {r y : ℕ} (h : y + 1 ∣ r + 1) (hyr : y ≤ r) :
    Mod r y * (y + 1) = r - y := by
  unfold Mod
  have h1 : (r + 1) / (y + 1) * (y + 1) = r + 1 := Nat.div_mul_cancel h
  have h2 : 1 ≤ (r + 1) / (y + 1) := Nat.div_pos (by omega) (by omega)
  rw [Nat.sub_mul, h1]
  omega

theorem Mod_dvd {r y : ℕ} (h : y + 1 ∣ r + 1) (hyr : y ≤ r) : Mod r y ∣ r - y :=
  ⟨y + 1, (Mod_mul h hyr).symm⟩

/-- Each factor of (4) is `≡ −1 (mod z!)` when `(z!)² ∣ r + 1` and `y < z`. -/
theorem factorial_dvd_Mod_succ {r y z : ℕ} (hz : (z.factorial) ^ 2 ∣ r + 1) (hy : y < z) :
    z.factorial ∣ Mod r y + 1 := by
  have hy1 : y + 1 ∣ z.factorial := Nat.dvd_factorial (by omega) (by omega)
  have hzle : z ≤ r + 1 := le_trans (Nat.self_le_factorial z)
    (le_trans (Nat.le_self_pow two_ne_zero _) (Nat.le_of_dvd (by omega) hz))
  obtain ⟨c, hc⟩ := hy1
  obtain ⟨Q, hQ⟩ := hz
  have hdiv : (r + 1) / (y + 1) = z.factorial * c * Q := by
    rw [hQ, pow_two]
    rw [show z.factorial * z.factorial * Q = (y + 1) * (z.factorial * c * Q) by rw [hc]; ring]
    exact Nat.mul_div_cancel_left _ (by omega)
  have hpos : 1 ≤ (r + 1) / (y + 1) := Nat.div_pos (by omega) (by omega)
  unfold Mod
  rw [Nat.sub_add_cancel hpos, hdiv]
  exact ⟨c * Q, by ring⟩

theorem coprime_Mod_factorial {r y z : ℕ} (hz : (z.factorial) ^ 2 ∣ r + 1) (hy : y < z) :
    Nat.Coprime (Mod r y) z.factorial := by
  obtain ⟨c, hc⟩ := factorial_dvd_Mod_succ hz hy
  rw [Nat.coprime_comm, Nat.Coprime, Nat.gcd_comm]
  have : Nat.gcd (Mod r y) z.factorial ∣ 1 := by
    have h1 : Nat.gcd (Mod r y) z.factorial ∣ Mod r y + 1 :=
      (Nat.gcd_dvd_right _ _).trans ⟨c, hc⟩
    have h2 : Nat.gcd (Mod r y) z.factorial ∣ Mod r y := Nat.gcd_dvd_left _ _
    have := (Nat.dvd_sub h1 h2)
    simpa using this
  exact Nat.dvd_one.1 this

/-- The factors of (4) are pairwise coprime. -/
theorem coprime_Mod {r z y y' : ℕ} (hz : (z.factorial) ^ 2 ∣ r + 1) (hy : y < z) (hy' : y' < z)
    (hzr : z ≤ r) (hne : y ≠ y') : Nat.Coprime (Mod r y) (Mod r y') := by
  -- wlog `y' < y`
  wlog hlt : y' < y generalizing y y'
  · exact (this hy' hy (Ne.symm hne) (by omega)).symm
  have hdy : y + 1 ∣ r + 1 :=
    (Nat.dvd_factorial (by omega) (by omega)).trans ((dvd_pow_self _ (by norm_num)).trans hz)
  have hdy' : y' + 1 ∣ r + 1 :=
    (Nat.dvd_factorial (by omega) (by omega)).trans ((dvd_pow_self _ (by norm_num)).trans hz)
  have e1 := Mod_mul hdy (by omega)
  have e2 := Mod_mul hdy' (by omega)
  -- `(y'+1) M y' = (y+1) M y + (y − y')`
  have key : Mod r y' * (y' + 1) = Mod r y * (y + 1) + (y - y') := by omega
  rw [Nat.Coprime]
  set g := Nat.gcd (Mod r y) (Mod r y')
  have hg1 : g ∣ Mod r y := Nat.gcd_dvd_left _ _
  have hg2 : g ∣ Mod r y' := Nat.gcd_dvd_right _ _
  have hg3 : g ∣ y - y' := by
    have h1 : g ∣ Mod r y' * (y' + 1) := Dvd.dvd.mul_right hg2 _
    have h2 : g ∣ Mod r y * (y + 1) := Dvd.dvd.mul_right hg1 _
    have := Nat.dvd_sub h1 h2
    rw [key, Nat.add_sub_cancel_left] at this
    exact this
  have hfac : y - y' ∣ z.factorial := Nat.dvd_factorial (by omega) (by omega)
  have hcop := coprime_Mod_factorial hz hy
  have : g ∣ 1 := by
    have hgf : g ∣ z.factorial := hg3.trans hfac
    exact Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.coprime_dvd_left hg1 hcop) (by simpa using hgf)
  exact Nat.dvd_one.1 this

/-- `C(r, z) = ∏_{y<z} M y`, equation (4). -/
theorem choose_eq_prod_Mod {r z : ℕ} (hz : (z.factorial) ^ 2 ∣ r + 1) (hzr : z ≤ r) :
    r.choose z = ∏ y ∈ range z, Mod r y := by
  have h1 : z.factorial * r.choose z = z.factorial * ∏ y ∈ range z, Mod r y := by
    rw [← Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_prod_range,
      ← Finset.prod_range_add_one_eq_factorial, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro y hy
    rw [Finset.mem_range] at hy
    have hdy : y + 1 ∣ r + 1 :=
      (Nat.dvd_factorial (by omega) (by omega)).trans ((dvd_pow_self _ (by norm_num)).trans hz)
    rw [mul_comm, Mod_mul hdy (by omega)]
  exact Nat.eq_of_mul_eq_mul_left (Nat.factorial_pos z) h1

theorem Mod_pos {r y z : ℕ} (hz : (z.factorial) ^ 2 ∣ r + 1) (hy : y < z) (hzr : z ≤ r) :
    0 < Mod r y := by
  have hdy : y + 1 ∣ r + 1 :=
    (Nat.dvd_factorial (by omega) (by omega)).trans ((dvd_pow_self _ (by norm_num)).trans hz)
  have hmul := Mod_mul hdy (by omega)
  have hry : 0 < r - y := by omega
  rcases Nat.eq_zero_or_pos (Mod r y) with h0 | h0
  · rw [h0, zero_mul] at hmul; omega
  · exact h0

/-- The core of the necessity proof, for prescribed `z` (above `τ` and all witnesses) and
`r ≥ z` with `(z!)² ∣ r + 1`: conditions (i) and (iv) can be satisfied. -/
theorem bqt_necessity_core {P : ℕ → (Fin (m + 1) → ℕ) → ℤ} (hP : CongPreserving P)
    {τ z r : ℕ} (_hz1 : 1 ≤ z) (_hτz : τ ≤ z) (hzr : z ≤ r) (hzr' : (z.factorial) ^ 2 ∣ r + 1)
    (w : ℕ → Fin (m + 1) → ℕ) (hw : ∀ y < τ, P y (w y) = 0) (hwz : ∀ y < τ, ∀ i, w y i < z)
    (N : ℕ) :
    ∃ zs : Fin (m + 1) → ℕ, (r.choose z : ℤ) ∣ P r zs * ((τ : ℤ) + zs 0 - r) ∧
      (∀ i, r.choose z ∣ (zs i).choose z) ∧ ∀ i, N ≤ zs i := by
  classical
  -- the extended witnesses `zy y i` for `y < z`
  set zy : ℕ → Fin (m + 1) → ℕ := fun y i => if y < τ then w y i else y - τ with hzy
  have hzyz : ∀ y < z, ∀ i, zy y i < z := by
    intro y hy i
    simp only [hzy]
    split_ifs with h
    · exact hwz y h i
    · omega
  -- the moduli
  have hMpos : ∀ y ∈ range z, Mod r y ≠ 0 := fun y hy =>
    (Mod_pos hzr' (Finset.mem_range.1 hy) hzr).ne'
  have hpp : Set.Pairwise (↑(range z) : Set ℕ) (Nat.Coprime on Mod r) := by
    intro y hy y' hy' hne
    exact coprime_Mod hzr' (by simpa using hy) (by simpa using hy') hzr hne
  have hppZ : Set.Pairwise (↑(range z) : Set ℕ) (IsCoprime on fun y => (Mod r y : ℤ)) := by
    intro y hy y' hy' hne
    exact Nat.Coprime.isCoprime (hpp hy hy' hne)
  have hMdvd : ∀ y < z, Mod r y ∣ r - y := fun y hy =>
    Mod_dvd ((Nat.dvd_factorial (by omega) (by omega)).trans
      ((dvd_pow_self _ (by norm_num)).trans hzr')) (by omega)
  have hry : ∀ y < z, y ≡ r [MOD Mod r y] := fun y hy =>
    (Nat.modEq_iff_dvd' (by omega)).2 (hMdvd y hy)
  -- the Chinese remainder solutions, shifted above `z`
  set Pr := ∏ y ∈ range z, Mod r y with hPr
  have hzs : ∀ i : Fin (m + 1), ∃ zi, z ≤ zi ∧ N ≤ zi ∧ ∀ y < z, zi ≡ zy y i [MOD Mod r y] := by
    intro i
    obtain ⟨k, hk⟩ := Nat.chineseRemainderOfFinset (fun y => zy y i) (Mod r) (range z) hMpos hpp
    have hPrpos : 0 < Pr := Finset.prod_pos (fun y hy => Nat.pos_of_ne_zero (hMpos y hy))
    refine ⟨k + (z + N) * Pr, by nlinarith [Nat.zero_le k], by nlinarith [Nat.zero_le k], ?_⟩
    intro y hy
    have h1 : k ≡ k + (z + N) * Pr [MOD Mod r y] := by
      rw [Nat.modEq_iff_dvd' (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
      exact Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ (Finset.mem_range.2 hy)) _
    exact h1.symm.trans (hk y (Finset.mem_range.2 hy))
  choose zs hzsz hzsN hzsc using hzs
  refine ⟨zs, ?_, ?_, hzsN⟩
  · -- (i)
    rw [choose_eq_prod_Mod hzr' hzr]
    push_cast
    apply Finset.prod_dvd_of_coprime hppZ
    intro y hy
    rw [Finset.mem_range] at hy
    have hc : P r zs * ((τ : ℤ) + zs 0 - r) ≡ P y (zy y) * ((τ : ℤ) + zy y 0 - y) [ZMOD Mod r y] := by
      have h1 : P r zs ≡ P y (zy y) [ZMOD Mod r y] :=
        hP _ r y zs (zy y) (hry y hy).symm (fun i => (hzsc i y hy))
      have h2 : ((zs 0 : ℕ) : ℤ) ≡ zy y 0 [ZMOD Mod r y] := Int.natCast_modEq_iff.2 (hzsc 0 y hy)
      have h3 : (r : ℤ) ≡ y [ZMOD Mod r y] := Int.natCast_modEq_iff.2 (hry y hy).symm
      exact h1.mul (((Int.ModEq.refl _).add h2).sub h3)
    have h0 : P y (zy y) * ((τ : ℤ) + zy y 0 - y) = 0 := by
      by_cases hyτ : y < τ
      · have : zy y = w y := by funext i; simp [hzy, hyτ]
        rw [this, hw y hyτ]; ring
      · have : zy y 0 = y - τ := by simp [hzy, hyτ]
        rw [this]
        push Not at hyτ
        rw [Nat.cast_sub hyτ]; ring
    rw [h0] at hc
    exact (Int.modEq_zero_iff_dvd).1 hc
  · -- (iv)
    intro i
    rw [choose_eq_prod_Mod hzr' hzr]
    have : ((∏ y ∈ range z, Mod r y : ℕ) : ℤ) ∣ ((zs i).choose z : ℤ) := by
      push_cast
      apply Finset.prod_dvd_of_coprime hppZ
      intro y hy
      rw [Finset.mem_range] at hy
      have hcop := coprime_Mod_factorial hzr' hy
      have h1 : Mod r y ∣ (zs i).choose z := by
        apply Nat.Coprime.dvd_of_dvd_mul_left hcop
        rw [← Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_prod_range]
        have hyi : zy y i < z := hzyz y hy i
        have hle : zy y i ≤ zs i := le_trans hyi.le (hzsz i)
        calc Mod r y ∣ zs i - zy y i := (Nat.modEq_iff_dvd' hle).1 (hzsc i y hy).symm
          _ ∣ ∏ j ∈ range z, (zs i - j) :=
            Finset.dvd_prod_of_mem (fun j => zs i - j) (Finset.mem_range.2 hyi)
      exact_mod_cast h1
    exact_mod_cast this

theorem bqt_necessity {P : ℕ → (Fin (m + 1) → ℕ) → ℤ} (hP : CongPreserving P) (R : ℕ → ℕ)
    (τ : ℕ) (hA : ∀ y < τ, ∃ zs, P y zs = 0) :
    ∃ z r zs, BQTConds P R τ z r zs := by
  classical
  -- witnesses for `y < τ`
  have hw : ∀ y, ∃ zs : Fin (m + 1) → ℕ, y < τ → P y zs = 0 := by
    intro y
    by_cases hy : y < τ
    · obtain ⟨zs, hzs⟩ := hA y hy; exact ⟨zs, fun _ => hzs⟩
    · exact ⟨fun _ => 0, fun h => absurd h hy⟩
  choose w hw using hw
  -- `z` exceeds τ and all witnesses
  set z := τ + 1 + ∑ y ∈ range τ, ∑ i, w y i with hz
  have hz1 : 1 ≤ z := by omega
  have hτz : τ ≤ z := by omega
  have hwz : ∀ y < τ, ∀ i, w y i < z := by
    intro y hy i
    have h1 : w y i ≤ ∑ i, w y i := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have h2 : ∑ i, w y i ≤ ∑ y ∈ range τ, ∑ i, w y i :=
      Finset.single_le_sum (f := fun y => ∑ i, w y i) (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 hy)
    omega
  -- `r`
  set B := 2 * z * z.factorial * R z with hB
  set r := z.factorial ^ 2 * (B ^ (z ^ (m + 1)) + z + 1) - 1 with hr
  have hfac1 : 1 ≤ z.factorial ^ 2 := Nat.one_le_pow _ _ (Nat.factorial_pos z)
  have hr1 : r + 1 = z.factorial ^ 2 * (B ^ (z ^ (m + 1)) + z + 1) := by
    rw [hr]
    have : 1 ≤ z.factorial ^ 2 * (B ^ (z ^ (m + 1)) + z + 1) :=
      Nat.one_le_iff_ne_zero.2 (by positivity)
    omega
  have hzr : (z.factorial) ^ 2 ∣ r + 1 := ⟨_, hr1⟩
  have hiii : B ^ (z ^ (m + 1)) + z ≤ r := by
    have : B ^ (z ^ (m + 1)) + z + 1 ≤ z.factorial ^ 2 * (B ^ (z ^ (m + 1)) + z + 1) :=
      Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hzr' : z ≤ r := le_trans (Nat.le_add_left _ _) hiii
  obtain ⟨zs, hi, hiv, -⟩ := bqt_necessity_core hP hz1 hτz hzr' hzr w hw hwz 0
  exact ⟨z, r, zs, ⟨hz1, hi, hτz, hiii, hiv⟩⟩

/-- **The Bounded Quantifier Theorem** (Lemma 2.3). -/
theorem bqt {P : ℕ → (Fin (m + 1) → ℕ) → ℤ} (hP : CongPreserving P) {R : ℕ → ℕ}
    (hR : Dominates P R) (τ : ℕ) :
    (∀ y < τ, ∃ zs, P y zs = 0) ↔ ∃ z r zs, BQTConds P R τ z r zs :=
  ⟨bqt_necessity hP R τ, fun ⟨z, _, _, h⟩ => bqt_sufficiency hP (hR z) h⟩

end Jones1978
