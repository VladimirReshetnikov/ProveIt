import Diophantine.Paper1980.TagSound
import Diophantine.Paper1980.RowSum

/-!
# The rows of an actual tag computation

For the converse direction of the tag certificate, the nine fields are assembled from the
actual run `W₀, W₁, …` of the tag system.  This file records the row data of that run —
the length `ℓᵢ`, the content `nᵢ`, the head selector `sᵢ = nᵢ mod 3`, the deleted prefix
`dᵢ = nᵢ mod 3^β` and its upper part `eᵢ = dᵢ / 3` — together with the two step relations

    ℓᵢ₊₁ + β = ℓᵢ + (if sᵢ = 1 then a else 1),
    3^β · nᵢ₊₁ = nᵢ − dᵢ + 3^(ℓᵢ) · (if sᵢ = 1 then U else 0),

in the form used by the construction (`length_step'`, `content_step'`).
-/

namespace Jones1980

open Ternary TagSys

/-! ### Contents modulo three -/

theorem content_mod_three_le_one : ∀ W : List Bool, content W % 3 ≤ 1
  | [] => by rw [content_nil]; norm_num
  | b :: W => by rw [content_cons_mod]; exact bit_le_one b

theorem content_mod_three_eq_one_iff (b : Bool) (W : List Bool) :
    content (b :: W) % 3 = 1 ↔ b = true := by
  rw [content_cons_mod]
  cases b <;> simp [bit]

/-! ### The two step relations, stated through `content W % 3` -/

theorem length_step' (TS : TagSys) (hβ : 1 ≤ TS.β) {W : List Bool} (hW : TS.β ≤ W.length) :
    (TS.step W).length + TS.β = W.length + (if content W % 3 = 1 then TS.u.length else 1) := by
  cases W with
  | nil => simp at hW; omega
  | cons s W' =>
    have h := length_step TS hW
    by_cases hs : s = true
    · subst hs
      rw [(content_mod_three_eq_one_iff true W').2 rfl, if_pos rfl] at *
      simpa using h
    · have hs' : s = false := by cases s <;> simp at hs ⊢
      subst hs'
      have : ¬ (content (false :: W') % 3 = 1) := by
        rw [content_mod_three_eq_one_iff]; simp
      rw [if_neg this]
      simpa using h

theorem content_step' (TS : TagSys) (hβ : 1 ≤ TS.β) {W : List Bool} (hW : TS.β ≤ W.length) :
    3 ^ TS.β * content (TS.step W) =
      content W - content W % 3 ^ TS.β +
        3 ^ W.length * (if content W % 3 = 1 then content TS.u else 0) := by
  cases W with
  | nil => simp at hW; omega
  | cons s W' =>
    have h := content_step TS hW
    by_cases hs : s = true
    · subst hs
      rw [(content_mod_three_eq_one_iff true W').2 rfl, if_pos rfl] at *
      simpa using h
    · have hs' : s = false := by cases s <;> simp at hs ⊢
      subst hs'
      have : ¬ (content (false :: W') % 3 = 1) := by
        rw [content_mod_three_eq_one_iff]; simp
      rw [if_neg this]
      simpa using h

/-! ### The row data of a run -/

/-- The length of the `i`-th queue. -/
def hlen (TS : TagSys) (W₀ : List Bool) (i : ℕ) : ℕ := (run TS W₀ i).length

/-- The content of the `i`-th queue. -/
def hcon (TS : TagSys) (W₀ : List Bool) (i : ℕ) : ℕ := content (run TS W₀ i)

/-- The head selector of the `i`-th queue. -/
def hsel (TS : TagSys) (W₀ : List Bool) (i : ℕ) : ℕ := hcon TS W₀ i % 3

/-- The deleted prefix of the `i`-th queue. -/
def hdel (TS : TagSys) (W₀ : List Bool) (i : ℕ) : ℕ := hcon TS W₀ i % 3 ^ TS.β

/-- The upper part of the deleted prefix. -/
def hpre (TS : TagSys) (W₀ : List Bool) (i : ℕ) : ℕ := hdel TS W₀ i / 3

variable {TS : TagSys} {W₀ : List Bool}

theorem hsel_le_one (i : ℕ) : hsel TS W₀ i ≤ 1 := content_mod_three_le_one _

theorem hcon_lt (i : ℕ) : hcon TS W₀ i < 3 ^ hlen TS W₀ i := content_lt _

theorem hcon_bool3 (i : ℕ) : Bool3 (hcon TS W₀ i) := content_bool3 _

theorem hdel_le (i : ℕ) : hdel TS W₀ i ≤ hcon TS W₀ i := Nat.mod_le _ _

theorem hdel_lt (i : ℕ) : hdel TS W₀ i < 3 ^ TS.β := Nat.mod_lt _ (by positivity)

theorem hdel_bool3 (i : ℕ) : Bool3 (hdel TS W₀ i) := (hcon_bool3 i).mod_pow _

theorem hpre_bool3 (i : ℕ) : Bool3 (hpre TS W₀ i) := by
  have h : hpre TS W₀ i = hdel TS W₀ i / 3 ^ 1 := by unfold hpre; rw [pow_one]
  rw [h]; exact (hdel_bool3 i).div_pow 1

theorem hpre_lt (hβ : 1 ≤ TS.β) (i : ℕ) : hpre TS W₀ i < 3 ^ (TS.β - 1) := by
  have h := hdel_lt (TS := TS) (W₀ := W₀) i
  have he : 3 ^ TS.β = 3 ^ (TS.β - 1) * 3 := by
    rw [← pow_succ, Nat.sub_add_cancel hβ]
  unfold hpre
  rw [he] at h
  omega

/-- `dᵢ = 3 eᵢ + sᵢ`. -/
theorem hdel_eq (hβ : 1 ≤ TS.β) (i : ℕ) :
    hdel TS W₀ i = 3 * hpre TS W₀ i + hsel TS W₀ i := by
  unfold hpre hsel hdel
  have h1 : hcon TS W₀ i % 3 ^ TS.β % 3 = hcon TS W₀ i % 3 :=
    Nat.mod_mod_of_dvd _ (dvd_pow_self 3 (by omega))
  rw [← h1]
  omega

theorem hsel_le_hcon (hβ : 1 ≤ TS.β) (i : ℕ) : hsel TS W₀ i ≤ hcon TS W₀ i := by
  have h1 := hdel_le (TS := TS) (W₀ := W₀) i
  have h2 := hdel_eq (TS := TS) (W₀ := W₀) hβ i
  omega

/-- Three divides `nᵢ − sᵢ`. -/
theorem three_dvd_hcon_sub_hsel (i : ℕ) : 3 ∣ hcon TS W₀ i - hsel TS W₀ i := by
  unfold hsel
  exact Nat.dvd_sub_mod _

/-! ### The steps of the run -/

variable (hβ : 1 ≤ TS.β)

include hβ

theorem hlen_step {i : ℕ} (hi : TS.β ≤ hlen TS W₀ i) :
    hlen TS W₀ (i + 1) + TS.β =
      hlen TS W₀ i + (if hsel TS W₀ i = 1 then TS.u.length else 1) := by
  unfold hlen hsel hcon
  rw [run_succ]
  exact length_step' TS hβ hi

theorem hcon_step {i : ℕ} (hi : TS.β ≤ hlen TS W₀ i) :
    3 ^ TS.β * hcon TS W₀ (i + 1) =
      hcon TS W₀ i - hdel TS W₀ i +
        3 ^ hlen TS W₀ i * (if hsel TS W₀ i = 1 then content TS.u else 0) := by
  unfold hcon hdel hsel hlen
  rw [run_succ]
  exact content_step' TS hβ hi

end Jones1980
