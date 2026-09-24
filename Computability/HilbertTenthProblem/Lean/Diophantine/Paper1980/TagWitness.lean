import Diophantine.Paper1980.TagHistory
import Diophantine.Paper1980.TagAssemble
import Diophantine.Paper1980.TagSound91

/-!
# The canonical witness of an accepting tag computation

`EXPLORATION_COMPILED_INITIAL_TAG_BOUND.md`, §5 (and `EXPLORATION_REORDERED_STARTUP_TAG.md`,
§4): from an actual run of the tag system that halts at the single-symbol word `0`, with
the startup promises, the nine conceptual fields are built row by row

    S₁ᵢ = sᵢ,  Qᵢ = sᵢ · rep ℓᵢ,  M₁ᵢ = sᵢ · 3^ℓᵢ,  Lᵢ = 3^ℓᵢ,
    Eᵢ = eᵢ,  GNᵢ = nᵢ + rep β · 3^(m−β),  Tcᵢ = (nᵢ − sᵢ + ε M₁ᵢ)/3,

and the outer equations hold: the geometry by the powers of three, the length equation by
the telescoping of the markers `3^(m i + ℓᵢ)`, and the content equation by the step
relation `3^β nᵢ₊₁ = nᵢ − dᵢ + U M₁ᵢ`.  Feeding these to `assemble91` gives a solution of
the 91-operation system (`witness91`), so an accepting computation is certified by the
arithmetic.
-/

namespace Jones1980

open Ternary TagSys Finset

/-! ### Parities and congruence of row sums -/

namespace Ternary

theorem pow_three_mod_two (k : ℕ) : 3 ^ k % 2 = 1 := by
  induction k with
  | zero => norm_num
  | succ k ih => rw [pow_succ, Nat.mul_mod, ih]

theorem rep_parity : ∀ n, rep n % 2 = n % 2
  | 0 => by simp [rep_zero]
  | n + 1 => by
    have h := rep_parity n
    have h3 := pow_three_mod_two n
    rw [rep_succ]
    omega

theorem rowsum_parity (f : ℕ → ℕ) (m : ℕ) : ∀ t, rowsum f m t % 2 = (∑ i ∈ range t, f i) % 2
  | 0 => by simp [rowsum_zero]
  | t + 1 => by
    have ih := rowsum_parity f m t
    have hmul : f t * 3 ^ (m * t) % 2 = f t % 2 := by
      rw [Nat.mul_mod, pow_three_mod_two, mul_one, Nat.mod_mod]
    rw [rowsum_succ, sum_range_succ, Nat.add_mod, ih, hmul, ← Nat.add_mod]

theorem rowsum_const (c m t : ℕ) : rowsum (fun _ => c) m t = c * heads m t := by
  rw [heads_eq_rowsum, ← rowsum_mul]
  simp

theorem rowsum_congr {f g : ℕ → ℕ} {m t : ℕ} (h : ∀ i, i < t → f i = g i) :
    rowsum f m t = rowsum g m t :=
  sum_congr rfl fun i hi => by rw [h i (mem_range.1 hi)]

end Ternary

/-! ### The rows of the nine fields -/

variable (TS : TagSys) (W₀ : List Bool)

/-- The marker row `3^ℓᵢ`. -/
def fL (i : ℕ) : ℕ := 3 ^ hlen TS W₀ i

/-- The projector row `sᵢ · rep ℓᵢ`. -/
def fQ (i : ℕ) : ℕ := if hsel TS W₀ i = 1 then rep (hlen TS W₀ i) else 0

/-- The selected marker row `sᵢ · 3^ℓᵢ`. -/
def fM1 (i : ℕ) : ℕ := if hsel TS W₀ i = 1 then 3 ^ hlen TS W₀ i else 0

/-- The guarded content row. -/
def fGN (m i : ℕ) : ℕ := hcon TS W₀ i + rep TS.β * 3 ^ (m - TS.β)

/-- The content-adapter row. -/
def fTc (i : ℕ) : ℕ :=
  (hcon TS W₀ i - hsel TS W₀ i + (content TS.u % 3) * fM1 TS W₀ i) / 3

/-- The marker of row `i` in its global position. -/
def gmark (m i : ℕ) : ℕ := 3 ^ (m * i + hlen TS W₀ i)

variable {TS W₀}

theorem fM1_eq (i : ℕ) : fM1 TS W₀ i = 2 * fQ TS W₀ i + hsel TS W₀ i := by
  unfold fM1 fQ
  split_ifs with h
  · have := two_mul_rep_add_one (hlen TS W₀ i); omega
  · have := hsel_le_one (TS := TS) (W₀ := W₀) i; omega

theorem fM1_le_fL (i : ℕ) : fM1 TS W₀ i ≤ fL TS W₀ i := by
  unfold fM1 fL; split_ifs
  · exact le_refl _
  · exact Nat.zero_le _

theorem fM1_bool3 (i : ℕ) : Bool3 (fM1 TS W₀ i) := by
  unfold fM1; split_ifs
  · exact bool3_pow _
  · exact bool3_zero

theorem fQ_bool3 (i : ℕ) : Bool3 (fQ TS W₀ i) := by
  unfold fQ; split_ifs
  · exact bool3_rep _
  · exact bool3_zero

theorem fQ_lt (i : ℕ) : fQ TS W₀ i < 3 ^ hlen TS W₀ i := by
  unfold fQ; split_ifs
  · exact rep_lt _
  · positivity

theorem fL_bool3 (i : ℕ) : Bool3 (fL TS W₀ i) := bool3_pow _

theorem fM0_bool3 (i : ℕ) : Bool3 (fL TS W₀ i - fM1 TS W₀ i) := by
  unfold fM1 fL; split_ifs
  · simp only [Nat.sub_self]; exact bool3_zero
  · simp only [Nat.sub_zero]; exact bool3_pow _

/-- The marker rows as a row sum. -/
theorem rowsum_fL (m t : ℕ) : rowsum (fL TS W₀) m t = ∑ i ∈ range t, gmark TS W₀ m i := by
  unfold rowsum fL gmark
  exact sum_congr rfl fun i _ => by rw [← pow_add]; congr 1; ring

/-! ### The two row identities -/

/-- The length step in the shifted form used by the length equation. -/
theorem length_row {m : ℕ} (hβ : 1 ≤ TS.β) {i : ℕ} (hi : TS.β ≤ hlen TS W₀ i) (hm : TS.β ≤ m) :
    3 ^ (m - TS.β + 1) * (fL TS W₀ i - fM1 TS W₀ i) +
        3 ^ (m - TS.β + TS.u.length) * fM1 TS W₀ i = 3 ^ (m + hlen TS W₀ (i + 1)) := by
  have hstep := hlen_step hβ (W₀ := W₀) hi
  unfold fL fM1
  split_ifs with h
  · rw [if_pos h] at hstep
    simp only [Nat.sub_self, mul_zero, zero_add, ← pow_add]
    congr 1
    omega
  · rw [if_neg h] at hstep
    simp only [Nat.sub_zero, mul_zero, add_zero, ← pow_add]
    congr 1
    omega

/-- The content step in the form used by the content equation. -/
theorem content_row (hβ : 1 ≤ TS.β) {i : ℕ} (hi : TS.β ≤ hlen TS W₀ i) :
    hcon TS W₀ i - hdel TS W₀ i + content TS.u * fM1 TS W₀ i =
      3 ^ TS.β * hcon TS W₀ (i + 1) := by
  have hstep := hcon_step hβ (W₀ := W₀) hi
  unfold fM1
  split_ifs with h
  · rw [if_pos h] at hstep; rw [hstep]; ring
  · rw [if_neg h] at hstep; rw [hstep]; ring

/-- `3 Tcᵢ + sᵢ = nᵢ + ε M₁ᵢ`. -/
theorem fTc_eq (hβ : 1 ≤ TS.β) {i : ℕ} (hi : 1 ≤ hlen TS W₀ i) :
    3 * fTc TS W₀ i + hsel TS W₀ i =
      hcon TS W₀ i + (content TS.u % 3) * fM1 TS W₀ i := by
  have hle := hsel_le_hcon (TS := TS) (W₀ := W₀) hβ i
  have hdvd : 3 ∣ hcon TS W₀ i - hsel TS W₀ i + (content TS.u % 3) * fM1 TS W₀ i := by
    refine Nat.dvd_add (three_dvd_hcon_sub_hsel i) ?_
    refine Dvd.dvd.mul_left ?_ _
    unfold fM1
    split_ifs with h
    · exact dvd_pow_self 3 (by omega)
    · exact dvd_zero 3
  unfold fTc
  obtain ⟨c, hc⟩ := hdvd
  rw [hc, Nat.mul_div_cancel_left _ (by norm_num)]
  omega

/-! ### The halted tail and the two summed identities -/

theorem run_eq_of_ge {t : ℕ} (hβ : 2 ≤ TS.β) (hterm : run TS W₀ t = [false]) :
    ∀ k, run TS W₀ (t + k) = [false] := by
  intro k
  induction k with
  | zero => simpa using hterm
  | succ k ih =>
    rw [show t + (k + 1) = (t + k) + 1 by ring, run_succ, ih]
    exact TS.step_of_short (by show ([false] : List Bool).length < TS.β; simp; omega)

theorem hlen_of_ge {t : ℕ} (hβ : 2 ≤ TS.β) (hterm : run TS W₀ t = [false]) {i : ℕ}
    (hi : t ≤ i) : hlen TS W₀ i = 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hi
  unfold hlen; rw [run_eq_of_ge hβ hterm k]; simp

theorem hcon_of_ge {t : ℕ} (hβ : 2 ≤ TS.β) (hterm : run TS W₀ t = [false]) {i : ℕ}
    (hi : t ≤ i) : hcon TS W₀ i = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hi
  unfold hcon; rw [run_eq_of_ge hβ hterm k]
  simp [content_cons, content_nil, bit]

/-- The telescoping of the markers: the length equation. -/
theorem length_sum {m t : ℕ} (hβ : 1 ≤ TS.β) (hm : TS.β ≤ m)
    (hlong : ∀ i, i < t → TS.β ≤ hlen TS W₀ i) :
    rowsum (fL TS W₀) m t + gmark TS W₀ m t =
      gmark TS W₀ m 0 +
        (3 ^ (m - TS.β + 1) * rowsum (fun i => fL TS W₀ i - fM1 TS W₀ i) m t +
          3 ^ (m - TS.β + TS.u.length) * rowsum (fM1 TS W₀) m t) := by
  have key : 3 ^ (m - TS.β + 1) * rowsum (fun i => fL TS W₀ i - fM1 TS W₀ i) m t +
      3 ^ (m - TS.β + TS.u.length) * rowsum (fM1 TS W₀) m t
      = ∑ i ∈ range t, gmark TS W₀ m (i + 1) := by
    rw [← rowsum_mul, ← rowsum_mul, ← rowsum_add]
    unfold rowsum gmark
    refine sum_congr rfl fun i hi => ?_
    rw [mem_range] at hi
    show (3 ^ (m - TS.β + 1) * (fL TS W₀ i - fM1 TS W₀ i) +
      3 ^ (m - TS.β + TS.u.length) * fM1 TS W₀ i) * 3 ^ (m * i) = _
    rw [length_row hβ (hlong i hi) hm, ← pow_add]
    congr 1
    ring
  rw [key, rowsum_fL, ← sum_range_succ, sum_range_succ' (gmark TS W₀ m) t]
  exact Nat.add_comm _ _

/-- The content transport, summed over the rows. -/
theorem content_sum {m t : ℕ} (hβ : 1 ≤ TS.β)
    (hlong : ∀ i, i < t → TS.β ≤ hlen TS W₀ i) (hterm : hcon TS W₀ t = 0) :
    3 ^ TS.β * rowsum (fun i => hcon TS W₀ (i + 1)) m t +
        (3 * rowsum (hpre TS W₀) m t + rowsum (hsel TS W₀) m t) =
      rowsum (hcon TS W₀) m t + content TS.u * rowsum (fM1 TS W₀) m t := by
  have hx : rowsum (fun i => hcon TS W₀ i - hdel TS W₀ i + content TS.u * fM1 TS W₀ i) m t =
      3 ^ TS.β * rowsum (fun i => hcon TS W₀ (i + 1)) m t := by
    rw [← rowsum_mul]
    exact rowsum_congr fun i hi => content_row hβ (hlong i hi)
  rw [← hx, ← rowsum_mul 3 (hpre TS W₀) m t, ← rowsum_mul (content TS.u) (fM1 TS W₀) m t,
    ← rowsum_add, ← rowsum_add, ← rowsum_add]
  refine rowsum_congr fun i _ => ?_
  have h1 := hdel_eq (TS := TS) (W₀ := W₀) hβ i
  have h2 := hdel_le (TS := TS) (W₀ := W₀) i
  omega

/-- The content word is the initial content plus the shifted tail. -/
theorem content_shift {m t : ℕ} (hterm : hcon TS W₀ t = 0) :
    hcon TS W₀ 0 + 3 ^ m * rowsum (fun i => hcon TS W₀ (i + 1)) m t =
      rowsum (hcon TS W₀) m t := by
  have h1 := rowsum_succ' (hcon TS W₀) m t
  have h2 := rowsum_succ (hcon TS W₀) m t
  rw [hterm, zero_mul, add_zero] at h2
  omega

/-! ### The parity of the packed word -/

namespace Ternary

/-- One Horner step is parity-neutral when the radix is odd. -/
theorem horner_modEq {q : ℕ} (hq : q % 2 = 1) (a b : ℕ) : a + q * b ≡ a + b [MOD 2] := by
  have hq' : q ≡ 1 [MOD 2] := by unfold Nat.ModEq; omega
  have h := Nat.ModEq.mul_right b hq'
  simpa using Nat.ModEq.add_left a h

end Ternary

/-- The parity of the nine-field Horner word. -/
theorem packed_modEq {q f0 f1 f2 f3 f4 f5 f6 f7 f8 : ℕ} (hq : q % 2 = 1) :
    f0 + q * (f1 + q * (f2 + q * (f3 + q * (f4 + q * (f5 + q * (f6 + q * (f7 + q * f8))))))) ≡
      f0 + f1 + f2 + f3 + f4 + f5 + f6 + f7 + f8 [MOD 2] := by
  have k := horner_modEq hq
  have h8 := k f7 f8
  have h7 := (k f6 (f7 + q * f8)).trans (Nat.ModEq.add_left f6 h8)
  have h6 := (k f5 _).trans (Nat.ModEq.add_left f5 h7)
  have h5 := (k f4 _).trans (Nat.ModEq.add_left f4 h6)
  have h4 := (k f3 _).trans (Nat.ModEq.add_left f3 h5)
  have h3 := (k f2 _).trans (Nat.ModEq.add_left f2 h4)
  have h2 := (k f1 _).trans (Nat.ModEq.add_left f1 h3)
  have h1 := (k f0 _).trans (Nat.ModEq.add_left f0 h2)
  calc f0 + q * (f1 + q * (f2 + q * (f3 + q * (f4 + q * (f5 + q * (f6 + q * (f7 + q * f8)))))))
      ≡ f0 + (f1 + (f2 + (f3 + (f4 + (f5 + (f6 + (f7 + f8))))))) [MOD 2] := h1
    _ = f0 + f1 + f2 + f3 + f4 + f5 + f6 + f7 + f8 := by ring

/-! ### The canonical witness -/

namespace Ternary

theorem rowsum_mod_three {f : ℕ → ℕ} {m t : ℕ} (hm : 1 ≤ m) (ht : 1 ≤ t) :
    rowsum f m t % 3 = f 0 % 3 := by
  obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  rw [rowsum_succ' f m t']
  obtain ⟨c, hc⟩ : (3 : ℕ) ∣ 3 ^ m := dvd_pow_self 3 (by omega)
  rw [hc, mul_assoc]
  omega

end Ternary

theorem bool3_of_le_one {X : ℕ} (h : X ≤ 1) : Bool3 X := by
  interval_cases X
  · exact bool3_zero
  · have h1 : (1 : ℕ) = 3 ^ 0 := by norm_num
    rw [h1]; exact bool3_pow 0

theorem sum_modEq_of_pointwise {t : ℕ} {f g : ℕ → ℕ} (h : ∀ i, i < t → f i ≡ g i [MOD 2]) :
    (∑ i ∈ range t, f i) ≡ (∑ i ∈ range t, g i) [MOD 2] := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [sum_range_succ, sum_range_succ]
    exact Nat.ModEq.add (ih fun i hi => h i (by omega)) (h t (by omega))

set_option maxHeartbeats 1600000 in
/-- **Completeness** of the tag certificate: an accepting computation that halts at the
single-symbol word `0`, with the startup promises and an even packed index, gives a
solution of the 91-operation system. -/
theorem witness91 {T : Tag91} {TS : TagSys} {W₀ : List Bool} {t m γ : ℕ}
    (hT : T.Ok) (hM : Matches T TS) (hCγ : T.C = 3 ^ γ)
    (hβ : 2 ≤ TS.β) (ha : 2 ≤ TS.u.length) (hβγ : TS.β ≤ γ)
    (ht : 1 ≤ t)
    (hlong : ∀ i, i < t → TS.β ≤ hlen TS W₀ i)
    (hterm : run TS W₀ t = [false])
    (hzero : hsel TS W₀ 0 = 0)
    (hwide : ∀ i, i ≤ t → hlen TS W₀ i + γ ≤ m)
    (hQpos : 0 < rowsum (fQ TS W₀) m t)
    (hS1pos : 0 < rowsum (hsel TS W₀) m t)
    (hEpos : 0 < rowsum (hpre TS W₀) m t)
    (hTcpos : 0 < rowsum (fTc TS W₀) m t)
    (hpar : 2 ∣ (∑ i ∈ range t, hcon TS W₀ i) + m * t) :
    Solvable91 T (content W₀) (3 ^ W₀.length) := by
  have hβ1 : 1 ≤ TS.β := by omega
  have ha1 : 1 ≤ TS.u.length := by omega
  -- the fixed constants as powers of three
  have hKhalf : T.Khalf = 3 ^ (TS.β - 1) := by
    have h := hM.β_eq
    have h2 : 3 * 3 ^ (TS.β - 1) = 3 ^ TS.β := by
      rw [← pow_succ', Nat.sub_add_cancel hβ1]
    omega
  have hBB : T.B = 3 ^ (TS.u.length - 1) := by
    have h := hM.B_eq
    have h2 : 3 * 3 ^ (TS.u.length - 1) = 3 ^ TS.u.length := by
      rw [← pow_succ', Nat.sub_add_cancel ha1]
    omega
  have hcc : T.cc = rep (TS.β - 1) := by
    have h := hT.cc_eq
    have h2 := two_mul_rep_add_one (TS.β - 1)
    rw [hKhalf] at h
    omega
  have hepsilon : T.ε = content TS.u % 3 := by
    have h := hM.U_eq
    have h2 := hT.ε_lt
    omega
  have hjg : T.jg = 3 ^ (γ - TS.β) * rep TS.β := by
    have h := hT.jg_eq
    have hdivCK : T.C / (3 * T.Khalf) = 3 ^ (γ - TS.β) := by
      rw [hM.β_eq, hCγ, Nat.pow_div hβγ (by norm_num)]
    rw [hdivCK, hCγ] at h
    have h2 : (3 : ℕ) ^ γ = 3 ^ (γ - TS.β) * 3 ^ TS.β := by
      rw [← pow_add, Nat.sub_add_cancel hβγ]
    have h3 := two_mul_rep_add_one TS.β
    rw [h2, ← h3] at h
    have h4 : 3 ^ (γ - TS.β) * (2 * rep TS.β + 1)
        = 2 * (3 ^ (γ - TS.β) * rep TS.β) + 3 ^ (γ - TS.β) := by ring
    rw [h4] at h
    omega
  -- widths
  have hlent : hlen TS W₀ t = 1 := hlen_of_ge hβ hterm le_rfl
  have hγm : 1 + γ ≤ m := by have := hwide t le_rfl; omega
  have hlen_all : ∀ i, hlen TS W₀ i + γ ≤ m := by
    intro i
    rcases Nat.lt_or_ge t i with h | h
    · rw [hlen_of_ge hβ hterm h.le]; omega
    · exact hwide i h
  have hm1 : 1 ≤ m := by omega
  have hβm : TS.β ≤ m := by omega
  have hγle : γ ≤ m := by omega
  have hlenm : ∀ i, hlen TS W₀ i < m := fun i => by have := hlen_all i; omega
  have hconlt : ∀ i, hcon TS W₀ i < 3 ^ (m - TS.β) := fun i =>
    lt_of_lt_of_le (hcon_lt i) (Nat.pow_le_pow_right (by norm_num) (by have := hlen_all i; omega))
  have hlen0 : hlen TS W₀ 0 = W₀.length := by unfold hlen; rw [run_zero]
  have hcon0 : hcon TS W₀ 0 = content W₀ := by unfold hcon; rw [run_zero]
  have hcont : hcon TS W₀ t = 0 := hcon_of_ge hβ hterm le_rfl
  have hone_lt : (1 : ℕ) < 3 ^ m := by
    calc (1 : ℕ) < 3 ^ 1 := by norm_num
      _ ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) hm1
  -- the row bounds
  have hrow_sel : ∀ i, hsel TS W₀ i < 3 ^ m := fun i =>
    lt_of_le_of_lt (hsel_le_one i) hone_lt
  have hrow_S0 : ∀ i, 1 - hsel TS W₀ i < 3 ^ m := fun i =>
    lt_of_le_of_lt (Nat.sub_le _ _) hone_lt
  have hrow_L : ∀ i, fL TS W₀ i < 3 ^ m := fun i => by
    unfold fL; exact Nat.pow_lt_pow_right (by norm_num) (hlenm i)
  have hrow_M1 : ∀ i, fM1 TS W₀ i < 3 ^ m := fun i =>
    lt_of_le_of_lt (fM1_le_fL i) (hrow_L i)
  have hrow_M0 : ∀ i, fL TS W₀ i - fM1 TS W₀ i < 3 ^ m := fun i =>
    lt_of_le_of_lt (Nat.sub_le _ _) (hrow_L i)
  have hrow_Q : ∀ i, fQ TS W₀ i < 3 ^ (m - γ) := fun i =>
    lt_of_lt_of_le (fQ_lt i) (Nat.pow_le_pow_right (by norm_num) (by have := hlen_all i; omega))
  have hrow_Qm : ∀ i, fQ TS W₀ i < 3 ^ m := fun i =>
    lt_of_lt_of_le (hrow_Q i) (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hrow_G : ∀ i, fQ TS W₀ i + 3 ^ (m - γ) * 1 < 3 ^ m := by
    intro i
    have h1 := hrow_Q i
    have h2 : 3 ^ (m - γ) * 3 ≤ 3 ^ m := by
      rw [← pow_succ]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hcc_pre : ∀ i, hpre TS W₀ i ≤ T.cc := fun i => by
    rw [hcc]; exact (hpre_bool3 i).le_rep (hpre_lt hβ1 i)
  have hcc_lt : T.cc < 3 ^ m := by
    rw [hcc]
    exact lt_of_lt_of_le (rep_lt _) (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hrow_E : ∀ i, hpre TS W₀ i < 3 ^ m := fun i => lt_of_le_of_lt (hcc_pre i) hcc_lt
  have hrow_Eb : ∀ i, T.cc - hpre TS W₀ i < 3 ^ m := fun i =>
    lt_of_le_of_lt (Nat.sub_le _ _) hcc_lt
  have hrow_GN : ∀ i, fGN TS W₀ m i < 3 ^ m := by
    intro i
    unfold fGN
    have h1 := hconlt i
    have h3 := two_mul_rep_add_one TS.β
    have h4 : (rep TS.β + 1) * 3 ^ (m - TS.β) ≤ 3 ^ TS.β * 3 ^ (m - TS.β) :=
      Nat.mul_le_mul_right _ (by omega)
    rw [← pow_add, Nat.add_sub_cancel' hβm] at h4
    nlinarith [h4]
  -- the field identities
  have hHrow : heads m t = rowsum (fun _ => 1) m t := heads_eq_rowsum m t
  have hM1eq : rowsum (fM1 TS W₀) m t
      = 2 * rowsum (fQ TS W₀) m t + rowsum (hsel TS W₀) m t := by
    rw [← rowsum_mul 2 (fQ TS W₀) m t, ← rowsum_add]
    exact rowsum_congr fun i _ => fM1_eq i
  have hS1H : rowsum (hsel TS W₀) m t ≤ heads m t := by
    rw [hHrow]; exact rowsum_le (fun i => hsel_le_one i) t
  have hM1L : 2 * rowsum (fQ TS W₀) m t + rowsum (hsel TS W₀) m t ≤ rowsum (fL TS W₀) m t := by
    rw [← hM1eq]; exact rowsum_le (fun i => fM1_le_fL i) t
  have hccH : T.cc * heads m t = rowsum (fun _ => T.cc) m t := (rowsum_const _ _ _).symm
  have hEcc : rowsum (hpre TS W₀) m t ≤ T.cc * heads m t := by
    rw [hccH]; exact rowsum_le hcc_pre t
  have hS0row : heads m t - rowsum (hsel TS W₀) m t
      = rowsum (fun i => 1 - hsel TS W₀ i) m t := by
    rw [rowsum_sub (fun i => hsel_le_one i) m t, hHrow]
  have hM0row : rowsum (fL TS W₀) m t - (2 * rowsum (fQ TS W₀) m t + rowsum (hsel TS W₀) m t)
      = rowsum (fun i => fL TS W₀ i - fM1 TS W₀ i) m t := by
    rw [← hM1eq, rowsum_sub (fun i => fM1_le_fL i) m t]
  have hEbrow : T.cc * heads m t - rowsum (hpre TS W₀) m t
      = rowsum (fun i => T.cc - hpre TS W₀ i) m t := by
    rw [rowsum_sub hcc_pre m t, hccH]
  have hGrow : rowsum (fQ TS W₀) m t + 3 ^ (m - γ) * heads m t
      = rowsum (fun i => fQ TS W₀ i + 3 ^ (m - γ) * 1) m t := by
    rw [← rowsum_const (3 ^ (m - γ)) m t, ← rowsum_add]
    exact rowsum_congr fun i _ => by rw [mul_one]
  have hGNsum : rowsum (fGN TS W₀ m) m t
      = rowsum (hcon TS W₀) m t + rep TS.β * 3 ^ (m - TS.β) * heads m t := by
    rw [← rowsum_const (rep TS.β * 3 ^ (m - TS.β)) m t, ← rowsum_add]
    exact rowsum_congr fun i _ => rfl
  -- the geometry
  have E0 : T.Khalf * 3 ^ (m - TS.β + 1) = 3 ^ m := by
    rw [hKhalf, ← pow_add]; congr 1; omega
  have E3 : 3 ^ m * heads m t + 1 = heads m t + 3 ^ (m * t) := by
    have h := heads_mul_sub_one m t
    have h1 : heads m t * (3 ^ m - 1) = heads m t * 3 ^ m - heads m t := by
      rw [Nat.mul_sub, mul_one]
    have h2 : heads m t ≤ heads m t * 3 ^ m := Nat.le_mul_of_pos_right _ (by positivity)
    have h3 : heads m t * 3 ^ m = 3 ^ m * heads m t := mul_comm _ _
    omega
  have E4 : 3 ^ m * heads m t = T.C * (3 ^ (m - γ) * heads m t) := by
    rw [hCγ, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hγle]
  have E5 : 3 ^ m * 3 ^ (m * (t - 1)) = 3 ^ (m * t) := by
    rw [← pow_add]; congr 1
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  -- the length equation
  have hgmark0 : gmark TS W₀ m 0 = 3 ^ W₀.length := by
    unfold gmark; rw [hlen0]; congr 1; omega
  have hgmarkt : gmark TS W₀ m t = 3 * 3 ^ (m * t) := by
    unfold gmark; rw [hlent, ← pow_succ']
  have hDB : 3 ^ (m - TS.β + 1) * T.B = 3 ^ (m - TS.β + TS.u.length) := by
    rw [hBB, ← pow_add]; congr 1; omega
  have E2N : rowsum (fL TS W₀) m t + 3 * 3 ^ (m * t)
      = 3 ^ W₀.length + (3 ^ (m - TS.β + 1) *
          (rowsum (fL TS W₀) m t - (2 * rowsum (fQ TS W₀) m t + rowsum (hsel TS W₀) m t))
        + 3 ^ (m - TS.β + TS.u.length) *
          (2 * rowsum (fQ TS W₀) m t + rowsum (hsel TS W₀) m t)) := by
    rw [hM0row, ← hM1eq, ← hgmark0, ← hgmarkt]
    exact length_sum hβ1 hβm hlong
  have E2 : ((3 : ℤ) ^ (m - TS.β + 1)) * ((rowsum (fL TS W₀) m t : ℤ) + ((T.B : ℤ) - 1) *
        (2 * (rowsum (fQ TS W₀) m t : ℤ) + (rowsum (hsel TS W₀) m t : ℤ)))
      = (rowsum (fL TS W₀) m t : ℤ) - ((3 : ℤ) ^ W₀.length) + 3 * ((3 : ℤ) ^ (m * t)) := by
    have hZ : ((rowsum (fL TS W₀) m t : ℤ)) + 3 * ((3 : ℤ) ^ (m * t))
        = ((3 : ℤ) ^ W₀.length) + (((3 : ℤ) ^ (m - TS.β + 1)) *
            ((rowsum (fL TS W₀) m t : ℤ) -
              (2 * (rowsum (fQ TS W₀) m t : ℤ) + (rowsum (hsel TS W₀) m t : ℤ)))
          + ((3 : ℤ) ^ (m - TS.β + TS.u.length)) *
            (2 * (rowsum (fQ TS W₀) m t : ℤ) + (rowsum (hsel TS W₀) m t : ℤ))) := by
      have h := E2N
      zify [hM1L] at h
      push_cast at h ⊢
      linarith [h]
    have hDBZ : ((3 : ℤ) ^ (m - TS.β + 1)) * (T.B : ℤ) = (3 : ℤ) ^ (m - TS.β + TS.u.length) := by
      have := hDB
      zify at this
      push_cast at this ⊢
      linarith [this]
    linear_combination -hZ +
      (2 * (rowsum (fQ TS W₀) m t : ℤ) + (rowsum (hsel TS W₀) m t : ℤ)) * hDBZ
  -- the content equation
  have hTcsum : 3 * rowsum (fTc TS W₀) m t + rowsum (hsel TS W₀) m t
      = rowsum (hcon TS W₀) m t + content TS.u % 3 * rowsum (fM1 TS W₀) m t := by
    rw [← rowsum_mul 3 (fTc TS W₀) m t, ← rowsum_mul (content TS.u % 3) (fM1 TS W₀) m t,
      ← rowsum_add, ← rowsum_add]
    exact rowsum_congr fun i hi => fTc_eq hβ1 (by have := hlong i hi; omega)
  have hcsum := content_sum (TS := TS) (W₀ := W₀) (m := m) (t := t) hβ1 hlong hcont
  have hshift := content_shift (TS := TS) (W₀ := W₀) (m := m) (t := t) hcont
  have hTN : (T.N (rowsum (fQ TS W₀) m t) (rowsum (hsel TS W₀) m t)
        (rowsum (fTc TS W₀) m t) : ℤ) = (rowsum (hcon TS W₀) m t : ℤ) := by
    have hM1Z : ((rowsum (fM1 TS W₀) m t : ℕ) : ℤ)
        = 2 * (rowsum (fQ TS W₀) m t : ℤ) + (rowsum (hsel TS W₀) m t : ℤ) := by
      have := hM1eq; zify at this; push_cast at this ⊢; linarith [this]
    have hTcZ : 3 * (rowsum (fTc TS W₀) m t : ℤ) + (rowsum (hsel TS W₀) m t : ℤ)
        = (rowsum (hcon TS W₀) m t : ℤ)
          + ((content TS.u % 3 : ℕ) : ℤ) * ((rowsum (fM1 TS W₀) m t : ℕ) : ℤ) := by
      have := hTcsum; zify at this; push_cast at this ⊢; linarith [this]
    have hεlt := hT.ε_lt
    unfold Tag91.N
    rcases (by omega : T.ε = 0 ∨ T.ε = 1) with h0 | h0
    · rw [if_pos h0]
      have hep : ((content TS.u % 3 : ℕ) : ℤ) = 0 := by rw [← hepsilon, h0]; norm_num
      rw [hep] at hTcZ
      push_cast
      linarith [hTcZ]
    · rw [if_neg (by omega)]
      have hep : ((content TS.u % 3 : ℕ) : ℤ) = 1 := by rw [← hepsilon, h0]; norm_num
      rw [hep, one_mul, hM1Z] at hTcZ
      push_cast
      linarith [hTcZ]
  have E1 : ((3 : ℤ) ^ (m - TS.β + 1)) * ((rowsum (fTc TS W₀) m t : ℤ)
        - (rowsum (hpre TS W₀) m t : ℤ) + (T.Uthird : ℤ) *
          (2 * (rowsum (fQ TS W₀) m t : ℤ) + (rowsum (hsel TS W₀) m t : ℤ)))
      = T.N (rowsum (fQ TS W₀) m t) (rowsum (hsel TS W₀) m t) (rowsum (fTc TS W₀) m t)
        - (content W₀ : ℤ) := by
    have hM1Z : ((rowsum (fM1 TS W₀) m t : ℕ) : ℤ)
        = 2 * (rowsum (fQ TS W₀) m t : ℤ) + (rowsum (hsel TS W₀) m t : ℤ) := by
      have := hM1eq; zify at this; push_cast at this ⊢; linarith [this]
    have hTcZ : 3 * (rowsum (fTc TS W₀) m t : ℤ) + (rowsum (hsel TS W₀) m t : ℤ)
        = (rowsum (hcon TS W₀) m t : ℤ)
          + ((content TS.u % 3 : ℕ) : ℤ) * ((rowsum (fM1 TS W₀) m t : ℕ) : ℤ) := by
      have := hTcsum; zify at this; push_cast at this ⊢; linarith [this]
    have hcsumZ : ((3 : ℤ) ^ TS.β) * ((rowsum (fun i => hcon TS W₀ (i + 1)) m t : ℕ) : ℤ)
          + (3 * (rowsum (hpre TS W₀) m t : ℤ) + (rowsum (hsel TS W₀) m t : ℤ))
        = (rowsum (hcon TS W₀) m t : ℤ)
          + (content TS.u : ℤ) * ((rowsum (fM1 TS W₀) m t : ℕ) : ℤ) := by
      have := hcsum; zify at this; push_cast at this ⊢; linarith [this]
    have hshiftZ : (content W₀ : ℤ)
          + ((3 : ℤ) ^ m) * ((rowsum (fun i => hcon TS W₀ (i + 1)) m t : ℕ) : ℤ)
        = (rowsum (hcon TS W₀) m t : ℤ) := by
      have := hshift; rw [hcon0] at this; zify at this; push_cast at this ⊢; linarith [this]
    have hUZ : 3 * (T.Uthird : ℤ) + ((content TS.u % 3 : ℕ) : ℤ) = (content TS.u : ℤ) := by
      have h := hM.U_eq
      rw [← hepsilon]
      zify at h; push_cast at h ⊢; linarith [h]
    have hDKZ : ((3 : ℤ) ^ (m - TS.β + 1)) * ((3 : ℤ) ^ TS.β) = 3 * ((3 : ℤ) ^ m) := by
      rw [← pow_add, ← pow_succ']
      congr 1
      omega
    rw [hTN]
    have key : (3 : ℤ) * (((3 : ℤ) ^ (m - TS.β + 1)) * ((rowsum (fTc TS W₀) m t : ℤ)
          - (rowsum (hpre TS W₀) m t : ℤ) + (T.Uthird : ℤ) *
            (2 * (rowsum (fQ TS W₀) m t : ℤ) + (rowsum (hsel TS W₀) m t : ℤ))))
        = 3 * ((rowsum (hcon TS W₀) m t : ℤ) - (content W₀ : ℤ)) := by
      rw [← hM1Z]
      linear_combination ((3 : ℤ) ^ (m - TS.β + 1)) * hTcZ
        + ((3 : ℤ) ^ (m - TS.β + 1)) * ((rowsum (fM1 TS W₀) m t : ℕ) : ℤ) * hUZ
        - ((3 : ℤ) ^ (m - TS.β + 1)) * hcsumZ
        + ((rowsum (fun i => hcon TS W₀ (i + 1)) m t : ℕ) : ℤ) * hDKZ
        + 3 * hshiftZ
    exact mul_left_cancel₀ (by norm_num : (3 : ℤ) ≠ 0) key
  -- the guarded content
  have hGNZ : ((rowsum (fGN TS W₀ m) m t : ℕ) : ℤ)
      = T.N (rowsum (fQ TS W₀) m t) (rowsum (hsel TS W₀) m t) (rowsum (fTc TS W₀) m t)
        + (T.jg : ℤ) * ((3 ^ (m - γ) * heads m t : ℕ) : ℤ) := by
    have hjgN : T.jg * (3 ^ (m - γ) * heads m t) = rep TS.β * 3 ^ (m - TS.β) * heads m t := by
      rw [hjg]
      have h : (3 : ℕ) ^ (γ - TS.β) * 3 ^ (m - γ) = 3 ^ (m - TS.β) := by
        rw [← pow_add]; congr 1; omega
      calc 3 ^ (γ - TS.β) * rep TS.β * (3 ^ (m - γ) * heads m t)
          = 3 ^ (γ - TS.β) * 3 ^ (m - γ) * rep TS.β * heads m t := by ring
        _ = 3 ^ (m - TS.β) * rep TS.β * heads m t := by rw [h]
        _ = rep TS.β * 3 ^ (m - TS.β) * heads m t := by ring
    rw [hTN, hGNsum]
    have := hjgN
    zify at this ⊢
    push_cast at this ⊢
    linarith [this]
  -- Booleanity
  have hb0 : Bool3 (heads m t - rowsum (hsel TS W₀) m t) := by
    rw [hS0row]
    exact bool3_rowsum (fun i => bool3_of_le_one (by have := hsel_le_one (TS := TS) (W₀ := W₀) i; omega))
      hrow_S0 t
  have hb1 : Bool3 (rowsum (hsel TS W₀) m t) :=
    bool3_rowsum (fun i => bool3_of_le_one (hsel_le_one i)) hrow_sel t
  have hb2 : Bool3 (rowsum (fQ TS W₀) m t) := bool3_rowsum (fun i => fQ_bool3 i) hrow_Qm t
  have hb3 : Bool3 (rowsum (fQ TS W₀) m t + 3 ^ (m - γ) * heads m t) := by
    rw [hGrow]
    exact bool3_rowsum
      (fun i => bool3_chunk_cons (fQ_bool3 i) (hrow_Q i) (bool3_of_le_one (le_refl 1))) hrow_G t
  have hb4 : Bool3 (rowsum (fL TS W₀) m t -
      (2 * rowsum (fQ TS W₀) m t + rowsum (hsel TS W₀) m t)) := by
    rw [hM0row]
    exact bool3_rowsum (fun i => fM0_bool3 i) hrow_M0 t
  have hb5 : Bool3 (2 * rowsum (fQ TS W₀) m t + rowsum (hsel TS W₀) m t) := by
    rw [← hM1eq]
    exact bool3_rowsum (fun i => fM1_bool3 i) hrow_M1 t
  have hb6 : Bool3 (T.cc * heads m t - rowsum (hpre TS W₀) m t) := by
    rw [hEbrow]
    refine bool3_rowsum (fun i => ?_) hrow_Eb t
    rw [hcc]
    exact rep_sub_bool3 (hpre_bool3 i) (hpre_lt hβ1 i)
  have hb7 : Bool3 (rowsum (hpre TS W₀) m t) := bool3_rowsum (fun i => hpre_bool3 i) hrow_E t
  have hb8 : Bool3 (rowsum (fGN TS W₀ m) m t) := by
    refine bool3_rowsum (fun i => ?_) hrow_GN t
    unfold fGN
    have h : rep TS.β * 3 ^ (m - TS.β) = 3 ^ (m - TS.β) * rep TS.β := mul_comm _ _
    rw [h]
    exact bool3_chunk_cons (hcon_bool3 i) (hconlt i) (bool3_rep _)
  -- the bounds
  have hl0 : heads m t - rowsum (hsel TS W₀) m t < 3 ^ (m * t) := by
    rw [hS0row]; exact rowsum_lt hrow_S0 t
  have hl1 : rowsum (hsel TS W₀) m t < 3 ^ (m * t) := rowsum_lt hrow_sel t
  have hl2 : rowsum (fQ TS W₀) m t < 3 ^ (m * t) := rowsum_lt hrow_Qm t
  have hl3 : rowsum (fQ TS W₀) m t + 3 ^ (m - γ) * heads m t < 3 ^ (m * t) := by
    rw [hGrow]; exact rowsum_lt hrow_G t
  have hl4 : rowsum (fL TS W₀) m t -
      (2 * rowsum (fQ TS W₀) m t + rowsum (hsel TS W₀) m t) < 3 ^ (m * t) := by
    rw [hM0row]; exact rowsum_lt hrow_M0 t
  have hl5 : 2 * rowsum (fQ TS W₀) m t + rowsum (hsel TS W₀) m t < 3 ^ (m * t) := by
    rw [← hM1eq]; exact rowsum_lt hrow_M1 t
  have hl6 : T.cc * heads m t - rowsum (hpre TS W₀) m t < 3 ^ (m * t) := by
    rw [hEbrow]; exact rowsum_lt hrow_Eb t
  have hl7 : rowsum (hpre TS W₀) m t < 3 ^ (m * t) := rowsum_lt hrow_E t
  have hl8 : rowsum (fGN TS W₀ m) m t < 3 ^ (m * t) := rowsum_lt hrow_GN t
  -- the unit digit
  have hunit : (heads m t - rowsum (hsel TS W₀) m t) % 3 = 1 := by
    rw [hS0row, rowsum_mod_three hm1 ht, hzero]
  -- positivity of the geometry
  have hHpos : 0 < heads m t := by
    rw [hHrow]
    have h := rowsum_succ' (fun _ => (1 : ℕ)) m (t - 1)
    rw [show t - 1 + 1 = t by omega] at h
    omega
  have hLpos : 0 < rowsum (fL TS W₀) m t := by
    have := hM1L
    have h2 : 0 < 2 * rowsum (fQ TS W₀) m t + rowsum (hsel TS W₀) m t := by omega
    omega
  -- the parity of the packed word
  have hsum9 : ∀ i, i < t → (1 - hsel TS W₀ i) + hsel TS W₀ i + fQ TS W₀ i
      + (fQ TS W₀ i + 3 ^ (m - γ) * 1) + (fL TS W₀ i - fM1 TS W₀ i) + fM1 TS W₀ i
      + (T.cc - hpre TS W₀ i) + hpre TS W₀ i + fGN TS W₀ m i ≡ hcon TS W₀ i [MOD 2] := by
    intro i _
    have e1 := hsel_le_one (TS := TS) (W₀ := W₀) i
    have e2 := fM1_le_fL (TS := TS) (W₀ := W₀) i
    have e3 := hcc_pre i
    have e4 : fL TS W₀ i % 2 = 1 := by unfold fL; exact pow_three_mod_two _
    have e5 : (3 : ℕ) ^ (m - γ) % 2 = 1 := pow_three_mod_two _
    have e6 : rep TS.β * 3 ^ (m - TS.β) % 2 = rep TS.β % 2 := by
      rw [Nat.mul_mod, pow_three_mod_two, mul_one, Nat.mod_mod]
    have e7 : rep TS.β = 3 * T.cc + 1 := by
      rw [hcc]
      have h := rep_succ_three (TS.β - 1)
      rw [Nat.sub_add_cancel hβ1] at h
      omega
    unfold Nat.ModEq fGN
    omega
  have hqodd : (3 : ℕ) ^ (m * t) % 2 = 1 := pow_three_mod_two _
  have hparP : 2 ∣ (heads m t - rowsum (hsel TS W₀) m t) + 3 ^ (m * t) *
      (rowsum (hsel TS W₀) m t + 3 ^ (m * t) * (rowsum (fQ TS W₀) m t + 3 ^ (m * t) *
        ((rowsum (fQ TS W₀) m t + 3 ^ (m - γ) * heads m t) + 3 ^ (m * t) *
          ((rowsum (fL TS W₀) m t -
              (2 * rowsum (fQ TS W₀) m t + rowsum (hsel TS W₀) m t)) + 3 ^ (m * t) *
            ((2 * rowsum (fQ TS W₀) m t + rowsum (hsel TS W₀) m t) + 3 ^ (m * t) *
              ((T.cc * heads m t - rowsum (hpre TS W₀) m t) + 3 ^ (m * t) *
                (rowsum (hpre TS W₀) m t + 3 ^ (m * t) * rowsum (fGN TS W₀ m) m t)))))))
      + rep (9 * (m * t)) := by
    have hstep := packed_modEq (q := 3 ^ (m * t)) hqodd
      (f0 := heads m t - rowsum (hsel TS W₀) m t) (f1 := rowsum (hsel TS W₀) m t)
      (f2 := rowsum (fQ TS W₀) m t)
      (f3 := rowsum (fQ TS W₀) m t + 3 ^ (m - γ) * heads m t)
      (f4 := rowsum (fL TS W₀) m t -
        (2 * rowsum (fQ TS W₀) m t + rowsum (hsel TS W₀) m t))
      (f5 := 2 * rowsum (fQ TS W₀) m t + rowsum (hsel TS W₀) m t)
      (f6 := T.cc * heads m t - rowsum (hpre TS W₀) m t) (f7 := rowsum (hpre TS W₀) m t)
      (f8 := rowsum (fGN TS W₀ m) m t)
    have p0 : heads m t - rowsum (hsel TS W₀) m t
        ≡ ∑ i ∈ range t, (1 - hsel TS W₀ i) [MOD 2] := by
      rw [hS0row]; exact rowsum_parity _ _ _
    have p1 : rowsum (hsel TS W₀) m t ≡ ∑ i ∈ range t, hsel TS W₀ i [MOD 2] :=
      rowsum_parity _ _ _
    have p2 : rowsum (fQ TS W₀) m t ≡ ∑ i ∈ range t, fQ TS W₀ i [MOD 2] := rowsum_parity _ _ _
    have p3 : rowsum (fQ TS W₀) m t + 3 ^ (m - γ) * heads m t
        ≡ ∑ i ∈ range t, (fQ TS W₀ i + 3 ^ (m - γ) * 1) [MOD 2] := by
      rw [hGrow]; exact rowsum_parity _ _ _
    have p4 : rowsum (fL TS W₀) m t - (2 * rowsum (fQ TS W₀) m t + rowsum (hsel TS W₀) m t)
        ≡ ∑ i ∈ range t, (fL TS W₀ i - fM1 TS W₀ i) [MOD 2] := by
      rw [hM0row]; exact rowsum_parity _ _ _
    have p5 : 2 * rowsum (fQ TS W₀) m t + rowsum (hsel TS W₀) m t
        ≡ ∑ i ∈ range t, fM1 TS W₀ i [MOD 2] := by
      rw [← hM1eq]; exact rowsum_parity _ _ _
    have p6 : T.cc * heads m t - rowsum (hpre TS W₀) m t
        ≡ ∑ i ∈ range t, (T.cc - hpre TS W₀ i) [MOD 2] := by
      rw [hEbrow]; exact rowsum_parity _ _ _
    have p7 : rowsum (hpre TS W₀) m t ≡ ∑ i ∈ range t, hpre TS W₀ i [MOD 2] :=
      rowsum_parity _ _ _
    have p8 : rowsum (fGN TS W₀ m) m t ≡ ∑ i ∈ range t, fGN TS W₀ m i [MOD 2] :=
      rowsum_parity _ _ _
    have hcomb := ((((((((p0.add p1).add p2).add p3).add p4).add p5).add p6).add p7).add p8)
    have hsplit : (∑ i ∈ range t, (1 - hsel TS W₀ i)) + (∑ i ∈ range t, hsel TS W₀ i)
          + (∑ i ∈ range t, fQ TS W₀ i)
          + (∑ i ∈ range t, (fQ TS W₀ i + 3 ^ (m - γ) * 1))
          + (∑ i ∈ range t, (fL TS W₀ i - fM1 TS W₀ i)) + (∑ i ∈ range t, fM1 TS W₀ i)
          + (∑ i ∈ range t, (T.cc - hpre TS W₀ i)) + (∑ i ∈ range t, hpre TS W₀ i)
          + (∑ i ∈ range t, fGN TS W₀ m i)
        = ∑ i ∈ range t, ((1 - hsel TS W₀ i) + hsel TS W₀ i + fQ TS W₀ i
          + (fQ TS W₀ i + 3 ^ (m - γ) * 1) + (fL TS W₀ i - fM1 TS W₀ i) + fM1 TS W₀ i
          + (T.cc - hpre TS W₀ i) + hpre TS W₀ i + fGN TS W₀ m i) := by
      simp only [← sum_add_distrib]
    have hsum' := sum_modEq_of_pointwise hsum9
    rw [← hsplit] at hsum'
    have hfin := hcomb.trans hsum'
    have hrep : rep (9 * (m * t)) ≡ m * t [MOD 2] := by
      unfold Nat.ModEq
      rw [rep_parity]
      omega
    have htot := (hstep.trans hfin).add hrep
    have h0 : (∑ i ∈ range t, hcon TS W₀ i) + m * t ≡ 0 [MOD 2] :=
      (Nat.modEq_zero_iff_dvd).2 hpar
    exact (Nat.modEq_zero_iff_dvd).1 (htot.trans h0)
  -- assemble
  exact assemble91 (T := T) (Ninit := content W₀) (Linit := 3 ^ W₀.length)
    (Q := rowsum (fQ TS W₀) m t) (S1 := rowsum (hsel TS W₀) m t)
    (Tc := rowsum (fTc TS W₀) m t) (E := rowsum (hpre TS W₀) m t) (H := heads m t)
    (R := 3 ^ m) (L := rowsum (fL TS W₀) m t) (q := 3 ^ (m * t)) (v := 3 ^ (m * (t - 1)))
    (D := 3 ^ (m - TS.β + 1)) (Z := 3 ^ (m - γ) * heads m t) (e := m * t)
    rfl (Nat.mul_pos hm1 ht) hQpos hS1pos hTcpos hEpos hHpos (by positivity) hLpos
    (by positivity)
    (by positivity) (by positivity) E0 E1 E2 E3 E4 E5 hS1H hM1L hEcc hGNZ
    hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hl0 hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hunit hparP

/-! ### The halting equivalence -/

/-- The encoded-instance contract follows from the startup promises. -/
theorem input91_of_run {T : Tag91} {TS : TagSys} {W₀ : List Bool} {γ : ℕ}
    (hM : Matches T TS) (hβ : 2 ≤ TS.β) (hCγ : T.C = 3 ^ γ)
    (hβW : TS.β ≤ W₀.length) (hbound : 2 * TS.β + W₀.length < γ) :
    Input91 T (content W₀) (3 ^ W₀.length) := by
  refine ⟨⟨W₀.length, TS.β, hβ, ?_, hβW, rfl⟩, content_bool3 W₀, content_lt W₀, ?_⟩
  · have h := hM.β_eq
    have h2 : 3 * 3 ^ (TS.β - 1) = 3 ^ TS.β := by
      rw [← pow_succ', Nat.sub_add_cancel (by omega)]
    omega
  · rw [hM.β_eq, hCγ]
    calc (3 ^ TS.β) ^ 2 * 3 ^ W₀.length = 3 ^ (2 * TS.β + W₀.length) := by
          rw [← pow_mul, ← pow_add, Nat.mul_comm TS.β 2]
      _ < 3 ^ γ := Nat.pow_lt_pow_right (by norm_num) hbound

/-- **The tag certificate is correct**: on the completeness domain the 91-operation system
is solvable exactly when the tag machine halts. -/
theorem tag_equiv91 {T : Tag91} {TS : TagSys} {W₀ : List Bool} {t m γ : ℕ}
    (hT : T.Ok) (hM : Matches T TS) (hCγ : T.C = 3 ^ γ)
    (hβ : 2 ≤ TS.β) (ha : 2 ≤ TS.u.length) (hβγ : TS.β ≤ γ)
    (hbound : 2 * TS.β + W₀.length < γ)
    (ht : 1 ≤ t)
    (hlong : ∀ i, i < t → TS.β ≤ hlen TS W₀ i)
    (hterm : run TS W₀ t = [false])
    (hzero : hsel TS W₀ 0 = 0)
    (hwide : ∀ i, i ≤ t → hlen TS W₀ i + γ ≤ m)
    (hQpos : 0 < rowsum (fQ TS W₀) m t)
    (hS1pos : 0 < rowsum (hsel TS W₀) m t)
    (hEpos : 0 < rowsum (hpre TS W₀) m t)
    (hTcpos : 0 < rowsum (fTc TS W₀) m t)
    (hpar : 2 ∣ (∑ i ∈ range t, hcon TS W₀ i) + m * t) :
    Solvable91 T (content W₀) (3 ^ W₀.length) ↔ TS.Halts W₀ := by
  have hβW : TS.β ≤ W₀.length := by
    have h := hlong 0 (by omega)
    rwa [show hlen TS W₀ 0 = W₀.length by unfold hlen; rw [run_zero]] at h
  refine ⟨fun hsol => sound91 hT hM (input91_of_run hM hβ hCγ hβW hbound) rfl rfl hsol,
    fun _ => witness91 hT hM hCγ hβ ha hβγ ht hlong hterm hzero hwide hQpos hS1pos hEpos
      hTcpos hpar⟩

end Jones1980
