import Diophantine.Paper1980.TagPad91
import Diophantine.Paper1980.Controller100

/-!
# The 91-operation tag certificate on its completeness domain

`EXPLORATION_PRODUCT_COORDINATE_TAG.md`, opening: *"The theorem assumes beta>=2 and appendant
length a>=2.  Its admitted input domain is K^2 Li<C.  Soundness proves actual eventual halting
on this domain; completeness has the previous first-zero, positive-startup and single-zero
terminal promises."*

`TagPromise` collects those promises for an input word `W₀`:

* *first zero*: the first symbol is `0`;
* *positive startup*: the initial deleted prefix has a nonzero bit beyond the head;
* *single-zero terminal*: if the run halts, the first short word is exactly `0`, and some `1`
  is read before it.

`tag_iff91` is the complete equivalence: on the admitted domain, the certificate is solvable
at the encoded input exactly when the tag system halts.  The width, the positivity of the four
startup coordinates and the index parity are no longer hypotheses: the width is chosen odd and
large, positivity comes from the promises (`EXPLORATION_POSITIVE_STARTUP_TAG.md`, §3), and when
the canonical index is odd the wrapped zero-edge padding of `witness91_gen` flips it.
-/

namespace Jones1980

open Ternary TagSys Finset

/-- The completeness promises of the tag certificate. -/
structure TagPromise (TS : TagSys) (W₀ : List Bool) : Prop where
  /-- The first symbol is `0`. -/
  first_zero : hsel TS W₀ 0 = 0
  /-- The initial deleted prefix has a nonzero bit beyond the head. -/
  startup : 1 ≤ hpre TS W₀ 0
  /-- A genuine halt is at the single word `0`, after reading some `1`. -/
  terminal : ∀ n, TS.Short (run TS W₀ n) → (∀ k, k < n → ¬ TS.Short (run TS W₀ k)) →
    run TS W₀ n = [false] ∧ ∃ i, i < n ∧ hsel TS W₀ i = 1

theorem rowsum_pos_at {f : ℕ → ℕ} {m t b : ℕ} (hb : b < t) (hf : 0 < f b) :
    0 < rowsum f m t := by
  have h := Finset.single_le_sum (f := fun i => f i * 3 ^ (m * i)) (fun _ _ => Nat.zero_le _)
    (Finset.mem_range.2 hb)
  have : 0 < f b * 3 ^ (m * b) := Nat.mul_pos hf (by positivity)
  unfold rowsum
  exact lt_of_lt_of_le this h

/-- The wrapped padding word `3 Σ_{i<m} b^i` as a sum of distinct powers of three. -/
theorem pad_eq {m g : ℕ} (hg : 1 ≤ g) :
    3 * ∑ i ∈ range m, (3 ^ g) ^ i = ∑ e ∈ (range m).image (fun i => 1 + i * g), 3 ^ e := by
  rw [Finset.sum_image (fun i _ j _ h => by
    have : i * g = j * g := by omega
    exact Nat.eq_of_mul_eq_mul_right hg this), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← pow_mul, pow_add, pow_one, Nat.mul_comm g i]

theorem pad_parity (m g : ℕ) : (3 * ∑ i ∈ range m, (3 ^ g) ^ i) % 2 = m % 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, Nat.mul_add, Nat.add_mod, ih]
    have : 3 * (3 ^ g) ^ m % 2 = 1 := by
      rw [← pow_mul, ← pow_succ']; exact pow_three_mod_two _
    rw [this]
    omega

set_option maxHeartbeats 1600000 in
/-- **The tag certificate is correct on its completeness domain.** -/
theorem tag_iff91 {T : Tag91} {TS : TagSys} {W₀ : List Bool} {γ : ℕ}
    (hT : T.Ok) (hM : Matches T TS) (hCγ : T.C = 3 ^ γ)
    (hβ : 2 ≤ TS.β) (ha : 2 ≤ TS.u.length) (hβW : TS.β ≤ W₀.length)
    (hbound : 2 * TS.β + W₀.length < γ) (hP : TagPromise TS W₀) :
    Solvable91 T (content W₀) (3 ^ W₀.length) ↔ TS.Halts W₀ := by
  classical
  refine ⟨fun hsol => sound91 hT hM (input91_of_run hM hβ hCγ hβW hbound) rfl rfl hsol,
    fun hh => ?_⟩
  -- the first halt
  have hex : ∃ n, TS.Short (run TS W₀ n) := hh
  set t := Nat.find hex with ht_def
  have hshort : TS.Short (run TS W₀ t) := Nat.find_spec hex
  have hmin : ∀ k, k < t → ¬ TS.Short (run TS W₀ k) := fun k hk => Nat.find_min hex hk
  obtain ⟨hterm, i1, hi1t, hi1⟩ := hP.terminal t hshort hmin
  have ht : 1 ≤ t := by
    by_contra h0
    have : t = 0 := by omega
    rw [this] at hshort
    exact absurd hshort (by unfold TagSys.Short; rw [run_zero]; omega)
  have hlong : ∀ i, i < t → TS.β ≤ hlen TS W₀ i := fun i hi => by
    have := hmin i hi
    unfold TagSys.Short at this
    unfold hlen
    omega
  have hβγ : TS.β ≤ γ := by omega
  -- an odd width wider than every row
  set M0 := γ + (∑ i ∈ range (t + 1), hlen TS W₀ i) + 2 * TS.β + 1 with hM0
  set m := 2 * M0 + 1 with hm
  have hwide : ∀ i, i ≤ t → hlen TS W₀ i + γ ≤ m := fun i hi => by
    have := Finset.single_le_sum (f := hlen TS W₀) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.2 (show i < t + 1 by omega))
    omega
  have hmodd : m % 2 = 1 := by omega
  -- the startup positivity
  have hQpos : 0 < rowsum (fQ TS W₀) m t := by
    refine rowsum_pos_at hi1t ?_
    unfold fQ
    rw [if_pos hi1]
    have := hlong i1 hi1t
    have h2 := rep_succ_three (hlen TS W₀ i1 - 1)
    rw [Nat.sub_add_cancel (by omega)] at h2
    omega
  have hS1pos : 0 < rowsum (hsel TS W₀) m t := rowsum_pos_at hi1t (by omega)
  have hEpos : 0 < rowsum (hpre TS W₀) m t := rowsum_pos_at (b := 0) (by omega) hP.startup
  have hTcpos : 0 < rowsum (fTc TS W₀) m t := by
    refine rowsum_pos_at (b := 0) (by omega) ?_
    have hd := hdel_eq (TS := TS) (W₀ := W₀) (by omega) 0
    have hdl := hdel_le (TS := TS) (W₀ := W₀) 0
    have hst := hP.startup
    have hz := hP.first_zero
    have hM1 : fM1 TS W₀ 0 = 0 := by unfold fM1; rw [hz]; simp
    unfold fTc
    rw [hM1, hz]
    omega
  -- the index parity, padded if necessary
  by_cases hpar : 2 ∣ (∑ i ∈ range t, hcon TS W₀ i) + m * t
  · exact witness91_gen (Tt := t) (Y := 0) hT hM hCγ hβ ha hβγ ht le_rfl hlong hterm
      hP.first_zero hwide hQpos hS1pos hEpos hTcpos bool3_zero (by positivity) (by ring)
      (by simpa using hpar)
  · -- the wrapped zero-edge padding
    have hg : 2 ≤ m - TS.β + 1 := by omega
    set g := m - TS.β + 1 with hg_def
    set d := m - (TS.β - 1) with hd_def
    have hgd : g = d := by omega
    set Y := 3 * ∑ i ∈ range m, (3 ^ g) ^ i with hY_def
    have hYeq := pad_eq (m := m) (g := g) (by omega)
    have hYb : Bool3 Y := by rw [hY_def, hYeq]; exact Ternary.bool3_sum_pow _
    have hYlt : Y < 3 ^ (m * (t + d - t)) := by
      rw [hY_def, hYeq, show t + d - t = d by omega]
      have hsub : (range m).image (fun i => 1 + i * g) ⊆ range (m * d) := by
        intro e he
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 he
        rw [Finset.mem_range] at hi ⊢
        rw [← hgd]
        have : (i + 1) * g ≤ m * g := Nat.mul_le_mul_right _ hi
        nlinarith
      exact lt_of_le_of_lt (Finset.sum_le_sum_of_subset hsub) (Controller.sum_pow_lt _)
    have hflow : 3 ^ (m - TS.β + 1) * (3 ^ (m * t) * Y) + 3 * 3 ^ (m * t)
        = 3 ^ (m * t) * Y + 3 * 3 ^ (m * (t + d)) := by
      obtain ⟨G, hG⟩ : ∃ G : ℕ, G = 3 ^ g := ⟨_, rfl⟩
      have hYG : (Y : ℤ) = 3 * ∑ i ∈ range m, (G : ℤ) ^ i := by
        rw [hY_def, ← hG]; push_cast; ring
      have hgeom : (∑ i ∈ range m, (G : ℤ) ^ i) * ((G : ℤ) - 1) = (G : ℤ) ^ m - 1 :=
        geom_sum_mul _ _
      have hpow : (G : ℕ) ^ m = 3 ^ (m * d) := by
        rw [hG, ← pow_mul, hgd, Nat.mul_comm]
      have hpowZ : (G : ℤ) ^ m = (3 : ℤ) ^ (m * d) := by exact_mod_cast hpow
      have hq : (3 : ℤ) ^ (m * (t + d)) = (3 : ℤ) ^ (m * t) * (3 : ℤ) ^ (m * d) := by
        rw [Nat.mul_add, pow_add]
      rw [show 3 ^ (m - TS.β + 1) = G from hG.symm]
      zify
      rw [hq, ← hpowZ, hYG]
      linear_combination (3 : ℤ) * (3 : ℤ) ^ (m * t) * hgeom
    have hpar' : 2 ∣ (∑ i ∈ range t, hcon TS W₀ i) + (t + d - t) + Y + m * (t + d) := by
      have hYp := pad_parity m g
      rw [← hY_def] at hYp
      rw [show t + d - t = d by omega, Nat.dvd_iff_mod_eq_zero]
      have hmd : m * (t + d) % 2 = (m * t + d) % 2 := by
        rw [Nat.mul_add, Nat.add_mod, Nat.add_mod (m * t) d, Nat.mul_mod m d, hmodd, one_mul,
          Nat.mod_mod]
      rw [Nat.dvd_iff_mod_eq_zero] at hpar
      omega
    exact witness91_gen (Tt := t + d) (Y := Y) hT hM hCγ hβ ha hβγ ht (by omega) hlong hterm
      hP.first_zero hwide hQpos hS1pos hEpos hTcpos hYb hYlt hflow hpar'

end Jones1980
