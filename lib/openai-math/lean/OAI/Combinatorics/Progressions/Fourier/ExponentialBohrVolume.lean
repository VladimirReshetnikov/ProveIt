-- Modified for ProveIt: in character_comm, `rfl` after `ring_nf` became `all_goals rfl` (ring_nf closes the goal in Mathlib v4.32.0).
import Mathlib
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Combinatorics.Additive.Dissociation
import Mathlib.Combinatorics.Pigeonhole

namespace OAI

section

namespace Erdos3

open AddChar Finset
open scoped BigOperators

namespace CyclicBohr

variable {N : ℕ} [NeZero N]

noncomputable def character (r : ZMod N) : AddChar (ZMod N) ℂ :=
  AddChar.zmodAddEquiv r

@[simp] lemma character_zero (r : ZMod N) : character r 0 = 1 := by
  exact AddChar.map_zero_eq_one _

@[simp] lemma character_add (r x y : ZMod N) :
    character r (x + y) = character r x * character r y := by
  exact AddChar.map_add_eq_mul _ _ _

@[simp] lemma norm_character (r x : ZMod N) : ‖character r x‖ = 1 := by
  simp [character]

lemma character_comm (r x : ZMod N) : character r x = character x r := by
  obtain ⟨r, rfl⟩ := ZMod.intCast_surjective r
  obtain ⟨x, rfl⟩ := ZMod.intCast_surjective x
  change (↑(AddChar.zmod N (r : ZMod N) (x : ZMod N)) : ℂ) =
    ↑(AddChar.zmod N (x : ZMod N) (r : ZMod N))
  rw [AddChar.zmod_intCast, AddChar.zmod_intCast]
  congr 1
  ring_nf
  all_goals rfl

@[simp] lemma character_zero_index (x : ZMod N) : character 0 x = 1 := by
  rw [character_comm, character_zero]

@[simp] lemma character_add_index (r s x : ZMod N) :
    character (r + s) x = character r x * character s x := by
  rw [character_comm, character_add, character_comm x r, character_comm x s]

lemma norm_one_sub_mul_of_norm_le_one {a b : ℂ} (ha : ‖a‖ ≤ 1) :
    ‖1 - a * b‖ ≤ ‖1 - a‖ + ‖1 - b‖ := by
  calc
    ‖1 - a * b‖ = ‖(1 - a) + a * (1 - b)‖ := by ring_nf
    _ ≤ ‖1 - a‖ + ‖a * (1 - b)‖ := norm_add_le _ _
    _ ≤ ‖1 - a‖ + ‖1 - b‖ := by
      gcongr
      exact (norm_mul_le _ _).trans (mul_le_of_le_one_left (norm_nonneg _) ha)

structure Set (N : ℕ) [NeZero N] where
  frequencies : Finset (ZMod N)
  radius : ℝ
  radius_nonneg : 0 ≤ radius

namespace Set

noncomputable def carrier (B : Set N) : Finset (ZMod N) :=
  Finset.univ.filter fun x ↦
    ∀ r ∈ B.frequencies, ‖1 - character r x‖ ≤ B.radius

instance : Membership (ZMod N) (Set N) := ⟨fun B x ↦ x ∈ B.carrier⟩

@[simp] lemma mem_carrier {B : Set N} {x : ZMod N} :
    x ∈ B.carrier ↔
      ∀ r ∈ B.frequencies, ‖1 - character r x‖ ≤ B.radius := by
  simp [carrier]

lemma mem_iff {B : Set N} {x : ZMod N} :
    x ∈ B ↔ ∀ r ∈ B.frequencies, ‖1 - character r x‖ ≤ B.radius :=
  mem_carrier

def rank (B : Set N) : ℕ := B.frequencies.card

def dilate (ρ : ℝ) (B : Set N) : Set N where
  frequencies := B.frequencies
  radius := |ρ| * B.radius
  radius_nonneg := mul_nonneg (abs_nonneg _) B.radius_nonneg

def ofFrequencies (Γ : Finset (ZMod N)) (ρ : ℝ) (hρ : 0 ≤ ρ) : Set N where
  frequencies := Γ
  radius := ρ
  radius_nonneg := hρ

def meet (B C : Set N) : Set N where
  frequencies := B.frequencies ∪ C.frequencies
  radius := min B.radius C.radius
  radius_nonneg := le_min B.radius_nonneg C.radius_nonneg

@[simp] lemma frequencies_ofFrequencies (Γ : Finset (ZMod N)) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    (ofFrequencies Γ ρ hρ).frequencies = Γ := rfl

@[simp] lemma radius_ofFrequencies (Γ : Finset (ZMod N)) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    (ofFrequencies Γ ρ hρ).radius = ρ := rfl

@[simp] lemma rank_ofFrequencies (Γ : Finset (ZMod N)) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    (ofFrequencies Γ ρ hρ).rank = Γ.card := rfl

@[simp] lemma frequencies_meet (B C : Set N) :
    (B.meet C).frequencies = B.frequencies ∪ C.frequencies := rfl

@[simp] lemma radius_meet (B C : Set N) :
    (B.meet C).radius = min B.radius C.radius := rfl

lemma rank_meet_le (B C : Set N) : (B.meet C).rank ≤ B.rank + C.rank := by
  exact Finset.card_union_le _ _

@[simp] lemma frequencies_dilate (ρ : ℝ) (B : Set N) :
    (B.dilate ρ).frequencies = B.frequencies := rfl

@[simp] lemma radius_dilate (ρ : ℝ) (B : Set N) :
    (B.dilate ρ).radius = |ρ| * B.radius := rfl

@[simp] lemma rank_dilate (ρ : ℝ) (B : Set N) :
    (B.dilate ρ).rank = B.rank := rfl

@[simp] lemma zero_mem (B : Set N) : (0 : ZMod N) ∈ B := by
  rw [mem_iff]
  intro r hr
  simp [B.radius_nonneg]

lemma carrier_nonempty (B : Set N) : B.carrier.Nonempty :=
  ⟨0, B.zero_mem⟩

lemma card_pos (B : Set N) : 0 < B.carrier.card :=
  Finset.card_pos.mpr B.carrier_nonempty

lemma neg_mem_iff (B : Set N) (x : ZMod N) : -x ∈ B ↔ x ∈ B := by
  rw [mem_iff, mem_iff]
  have hnorm (z : ℂ) : ‖1 - (starRingEnd ℂ) z‖ = ‖1 - z‖ := by
    simpa using (RCLike.norm_conj (1 - z))
  constructor
  · intro h r hr
    have hr' := h r hr
    rw [AddChar.map_neg_eq_conj, hnorm] at hr'
    exact hr'
  · intro h r hr
    rw [AddChar.map_neg_eq_conj, hnorm]
    exact h r hr

lemma add_mem_of_mem {B₁ B₂ B₃ : Set N}
    (hfreq₁ : B₃.frequencies ⊆ B₁.frequencies)
    (hfreq₂ : B₃.frequencies ⊆ B₂.frequencies)
    (hradius : B₁.radius + B₂.radius ≤ B₃.radius)
    {x y : ZMod N} (hx : x ∈ B₁) (hy : y ∈ B₂) : x + y ∈ B₃ := by
  rw [mem_iff] at hx hy ⊢
  intro r hr
  calc
    ‖1 - character r (x + y)‖ =
        ‖1 - character r x * character r y‖ := by rw [character_add]
    _ ≤ ‖1 - character r x‖ + ‖1 - character r y‖ :=
      norm_one_sub_mul_of_norm_le_one (by rw [norm_character])
    _ ≤ B₁.radius + B₂.radius := add_le_add (hx r (hfreq₁ hr)) (hy r (hfreq₂ hr))
    _ ≤ B₃.radius := hradius

lemma add_mem_dilate {B : Set N} {ρ σ : ℝ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ)
    {x y : ZMod N} (hx : x ∈ B.dilate ρ) (hy : y ∈ B.dilate σ) :
    x + y ∈ B.dilate (ρ + σ) := by
  apply add_mem_of_mem (B₁ := B.dilate ρ) (B₂ := B.dilate σ)
      (B₃ := B.dilate (ρ + σ))
  · simp
  · simp
  · simp [abs_of_nonneg hρ, abs_of_nonneg hσ, abs_of_nonneg (add_nonneg hρ hσ), add_mul]
  · exact hx
  · exact hy

lemma sub_mem_dilate {B : Set N} {ρ σ : ℝ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ)
    {x y : ZMod N} (hx : x ∈ B.dilate ρ) (hy : y ∈ B.dilate σ) :
    x - y ∈ B.dilate (ρ + σ) := by
  rw [sub_eq_add_neg]
  apply add_mem_dilate hρ hσ hx
  exact (B.dilate σ).neg_mem_iff y |>.2 hy

lemma carrier_mono {B₁ B₂ : Set N} (hfreq : B₂.frequencies ⊆ B₁.frequencies)
    (hradius : B₁.radius ≤ B₂.radius) : B₁.carrier ⊆ B₂.carrier := by
  intro x hx
  rw [mem_carrier] at hx ⊢
  intro r hr
  exact (hx r (hfreq hr)).trans hradius

lemma carrier_meet_subset_left (B C : Set N) : (B.meet C).carrier ⊆ B.carrier := by
  apply carrier_mono
  · exact Finset.subset_union_left
  · exact min_le_left _ _

lemma carrier_meet_subset_right (B C : Set N) : (B.meet C).carrier ⊆ C.carrier := by
  apply carrier_mono
  · exact Finset.subset_union_right
  · exact min_le_right _ _

lemma dilate_mono (B : Set N) {ρ σ : ℝ} (hρ : 0 ≤ ρ) (hρσ : ρ ≤ σ) :
    (B.dilate ρ).carrier ⊆ (B.dilate σ).carrier := by
  apply carrier_mono
  · simp
  · have hσ : 0 ≤ σ := hρ.trans hρσ
    simp only [radius_dilate, ge_iff_le]
    rw [abs_of_nonneg hρ, abs_of_nonneg hσ]
    exact mul_le_mul_of_nonneg_right hρσ B.radius_nonneg

lemma carrier_eq_univ_of_two_le_radius (B : Set N) (hB : 2 ≤ B.radius) :
    B.carrier = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro x
  rw [mem_carrier]
  intro r hr
  calc
    ‖1 - character r x‖ ≤ ‖(1 : ℂ)‖ + ‖character r x‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_character]; norm_num
    _ ≤ B.radius := hB

@[simp] lemma dilate_one (B : Set N) : B.dilate 1 = B := by
  cases B
  simp [dilate]

@[simp] lemma dilate_dilate (B : Set N) (s t : ℝ) :
    (B.dilate s).dilate t = B.dilate (t * s) := by
  cases B
  simp [dilate, abs_mul, mul_assoc]

end Set
end CyclicBohr
end Erdos3

end

section

namespace Erdos3

open AddChar Finset
open scoped BigOperators

namespace CyclicBohr

variable {N : ℕ} [NeZero N]

lemma norm_sub_le_abs_arg_sub_of_norm_eq_one {z w : ℂ}
    (hz : ‖z‖ = 1) (hw : ‖w‖ = 1) :
    ‖z - w‖ ≤ |z.arg - w.arg| := by
  have hzexp : Complex.exp (z.arg * Complex.I) = z := by
    calc
      Complex.exp (z.arg * Complex.I) =
          ‖z‖ * Complex.exp (z.arg * Complex.I) := by simp [hz]
      _ = z := Complex.norm_mul_exp_arg_mul_I z
  have hwexp : Complex.exp (w.arg * Complex.I) = w := by
    calc
      Complex.exp (w.arg * Complex.I) =
          ‖w‖ * Complex.exp (w.arg * Complex.I) := by simp [hw]
      _ = w := Complex.norm_mul_exp_arg_mul_I w
  calc
    ‖z - w‖ =
        ‖Complex.exp (z.arg * Complex.I) - Complex.exp (w.arg * Complex.I)‖ := by
      rw [hzexp, hwexp]
    _ =
        ‖Complex.exp (w.arg * Complex.I) *
          (Complex.exp ((z.arg - w.arg) * Complex.I) - 1)‖ := by
      congr 1
      rw [mul_sub, mul_one, ← Complex.exp_add]
      congr 2
      ring
    _ = ‖Complex.exp ((z.arg - w.arg) * Complex.I) - 1‖ := by
      rw [norm_mul, Complex.norm_exp]
      simp
    _ ≤ |z.arg - w.arg| := by
      simpa [mul_comm, Real.norm_eq_abs] using
        (Real.norm_exp_I_mul_ofReal_sub_one_le (x := z.arg - w.arg))

noncomputable def scaledArg (m : ℕ) (z : ℂ) : ℝ :=
  (z.arg + Real.pi) * m / (2 * Real.pi)

lemma scaledArg_nonneg (m : ℕ) (z : ℂ) : 0 ≤ scaledArg m z := by
  unfold scaledArg
  have hz : 0 ≤ z.arg + Real.pi := by linarith [Complex.neg_pi_lt_arg z]
  positivity

lemma scaledArg_le (m : ℕ) (z : ℂ) : scaledArg m z ≤ m := by
  unfold scaledArg
  have hz : z.arg + Real.pi ≤ 2 * Real.pi := by
    linarith [Complex.arg_le_pi z]
  have hpi : 0 < 2 * Real.pi := by positivity
  rw [div_le_iff₀ hpi]
  nlinarith

noncomputable def argBin (m : ℕ) (z : ℂ) : Fin (m + 1) :=
  ⟨⌊scaledArg m z⌋₊, by
    rw [Nat.floor_lt' (Nat.add_one_ne_zero m)]
    exact (scaledArg_le m z).trans_lt (by exact_mod_cast Nat.lt_succ_self m)⟩

lemma abs_scaledArg_sub_lt_one_of_argBin_eq {m : ℕ} {z w : ℂ}
    (hbin : argBin m z = argBin m w) :
    |scaledArg m z - scaledArg m w| < 1 := by
  have hfloor : ⌊scaledArg m z⌋₊ = ⌊scaledArg m w⌋₊ :=
    congrArg Fin.val hbin
  have hfloorR : (⌊scaledArg m z⌋₊ : ℝ) = ⌊scaledArg m w⌋₊ := by
    exact_mod_cast hfloor
  have hzlow : (⌊scaledArg m z⌋₊ : ℝ) ≤ scaledArg m z :=
    Nat.floor_le (scaledArg_nonneg m z)
  have hwlow : (⌊scaledArg m w⌋₊ : ℝ) ≤ scaledArg m w :=
    Nat.floor_le (scaledArg_nonneg m w)
  have hzup : scaledArg m z < (⌊scaledArg m z⌋₊ : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hwup : scaledArg m w < (⌊scaledArg m w⌋₊ : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  rw [abs_lt]
  constructor <;> nlinarith

lemma abs_arg_sub_lt_of_argBin_eq {m : ℕ} (hm : 0 < m) {z w : ℂ}
    (hbin : argBin m z = argBin m w) :
    |z.arg - w.arg| < 2 * Real.pi / m := by
  have h := abs_scaledArg_sub_lt_one_of_argBin_eq hbin
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hpi : 0 < 2 * Real.pi := by positivity
  have hscale :
      |scaledArg m z - scaledArg m w| =
        |z.arg - w.arg| * (m : ℝ) / (2 * Real.pi) := by
    have heq : scaledArg m z - scaledArg m w =
        (z.arg - w.arg) * (m : ℝ) / (2 * Real.pi) := by
      unfold scaledArg
      ring
    rw [heq, abs_div, abs_mul, abs_of_pos hmR, abs_of_pos hpi]
  rw [hscale] at h
  rw [lt_div_iff₀ hmR]
  exact (div_lt_one hpi).mp h

noncomputable def argumentCode (B : Set N) (m : ℕ) (x : ZMod N) :
    (r : ↥B.frequencies) → Fin (m + 1) :=
  fun r ↦ argBin m (character r.1 x)

@[simp] lemma card_argumentCodeSpace (B : Set N) (m : ℕ) :
    Fintype.card ((r : ↥B.frequencies) → Fin (m + 1)) =
      (m + 1) ^ B.rank := by
  simp [Set.rank]

lemma norm_one_sub_character_sub (r x y : ZMod N) :
    ‖1 - character r (x - y)‖ = ‖character r x - character r y‖ := by
  have hy : character r y ≠ 0 :=
    norm_ne_zero_iff.mp (by rw [norm_character]; norm_num)
  rw [AddChar.map_sub_eq_div, one_sub_div hy, norm_div, norm_character]
  simp [norm_sub_rev]

lemma sub_mem_of_argumentCode_eq (B : Set N) {m : ℕ} (hm : 0 < m)
    (hwidth : 2 * Real.pi / m ≤ B.radius) {x y : ZMod N}
    (hcode : argumentCode B m x = argumentCode B m y) :
    x - y ∈ B := by
  rw [Set.mem_iff]
  intro r hr
  have hbin : argBin m (character r x) = argBin m (character r y) := by
    exact congrFun hcode ⟨r, hr⟩
  calc
    ‖1 - character r (x - y)‖ = ‖character r x - character r y‖ :=
      norm_one_sub_character_sub r x y
    _ ≤ |(character r x).arg - (character r y).arg| :=
      norm_sub_le_abs_arg_sub_of_norm_eq_one (norm_character r x) (norm_character r y)
    _ ≤ 2 * Real.pi / m := (abs_arg_sub_lt_of_argBin_eq hm hbin).le
    _ ≤ B.radius := hwidth

theorem natDiv_codeCard_le_card_carrier (B : Set N) {m : ℕ} (hm : 0 < m)
    (hwidth : 2 * Real.pi / m ≤ B.radius) :
    N / (m + 1) ^ B.rank ≤ B.carrier.card := by
  let Q := (r : ↥B.frequencies) → Fin (m + 1)
  let code : ZMod N → Q := argumentCode B m
  have hQ : Fintype.card Q = (m + 1) ^ B.rank := by
    simpa [Q] using card_argumentCodeSpace B m
  have hpigeon : Fintype.card Q * (N / Fintype.card Q) ≤
      Fintype.card (ZMod N) := by
    rw [ZMod.card]
    exact Nat.mul_div_le N (Fintype.card Q)
  obtain ⟨q, hq⟩ :=
    Fintype.exists_le_card_fiber_of_mul_le_card (f := code) hpigeon
  let S : Finset (ZMod N) := Finset.univ.filter fun x ↦ code x = q
  have hScard : N / Fintype.card Q ≤ S.card := by
    simpa [S] using hq
  by_cases hzero : N / Fintype.card Q = 0
  · rw [hQ] at hzero
    rw [hzero]
    exact Nat.zero_le _
  have hSnonempty : S.Nonempty := Finset.card_pos.mp (lt_of_lt_of_le
    (Nat.pos_of_ne_zero hzero) hScard)
  obtain ⟨x₀, hx₀⟩ := hSnonempty
  let e : ZMod N ↪ ZMod N := (Equiv.subRight x₀).toEmbedding
  have hmap : S.map e ⊆ B.carrier := by
    intro z hz
    rw [Finset.mem_map] at hz
    obtain ⟨x, hxS, rfl⟩ := hz
    have hcodex : code x = q := by simpa [S] using hxS
    have hcodex₀ : code x₀ = q := by simpa [S] using hx₀
    exact sub_mem_of_argumentCode_eq B hm hwidth (hcodex.trans hcodex₀.symm)
  calc
    N / (m + 1) ^ B.rank = N / Fintype.card Q := by rw [hQ]
    _ ≤ S.card := hScard
    _ = (S.map e).card := (Finset.card_map e).symm
    _ ≤ B.carrier.card := Finset.card_le_card hmap

lemma abs_arg_character_le_two_radius (B : Set N) {x r : ZMod N}
    (hx : x ∈ B) (hr : r ∈ B.frequencies) :
    |(character r x).arg| ≤ 2 * B.radius := by
  have hnorm := Set.mem_iff.mp hx r hr
  have hangle := Complex.angle_le_mul_norm_sub
    (norm_character r x) (by norm_num : ‖(1 : ℂ)‖ = 1)
  calc
    |(character r x).arg| = InnerProductGeometry.angle (character r x) 1 :=
      (Complex.angle_one_right (norm_ne_zero_iff.mp (by
        rw [norm_character]
        norm_num))).symm
    _ ≤ Real.pi / 2 * ‖character r x - 1‖ := hangle
    _ = Real.pi / 2 * ‖1 - character r x‖ := by rw [norm_sub_rev]
    _ ≤ Real.pi / 2 * B.radius :=
      mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ ≤ 2 * B.radius := by
      apply mul_le_mul_of_nonneg_right _ B.radius_nonneg
      linarith [Real.pi_lt_four]

noncomputable def localScaledArg (B : Set N) (z : ℂ) : ℝ :=
  2 * (z.arg + 2 * B.radius) / B.radius

lemma localScaledArg_nonneg (B : Set N) {x r : ZMod N}
    (hB : 0 < B.radius) (hx : x ∈ B) (hr : r ∈ B.frequencies) :
    0 ≤ localScaledArg B (character r x) := by
  have harg := abs_arg_character_le_two_radius B hx hr
  rw [abs_le] at harg
  unfold localScaledArg
  have hsum : 0 ≤ (character r x).arg + 2 * B.radius := by linarith [harg.1]
  exact div_nonneg (mul_nonneg (by norm_num) hsum) hB.le

lemma localScaledArg_le_eight (B : Set N) {x r : ZMod N}
    (hB : 0 < B.radius) (hx : x ∈ B) (hr : r ∈ B.frequencies) :
    localScaledArg B (character r x) ≤ 8 := by
  have harg := abs_arg_character_le_two_radius B hx hr
  rw [abs_le] at harg
  unfold localScaledArg
  rw [div_le_iff₀ hB]
  linarith

noncomputable def localArgBin (B : Set N) (hB : 0 < B.radius)
    (x : ↥B.carrier) (r : ↥B.frequencies) : Fin 9 :=
  ⟨⌊localScaledArg B (character r.1 x.1)⌋₊, by
    rw [Nat.floor_lt' (by norm_num : (9 : ℕ) ≠ 0)]
    exact (localScaledArg_le_eight B hB x.2 r.2).trans_lt (by norm_num)⟩

noncomputable def localArgumentCode (B : Set N) (hB : 0 < B.radius)
    (x : ↥B.carrier) : (r : ↥B.frequencies) → Fin 9 :=
  fun r ↦ localArgBin B hB x r

@[simp] lemma card_localArgumentCodeSpace (B : Set N) :
    Fintype.card ((r : ↥B.frequencies) → Fin 9) = 9 ^ B.rank := by
  simp [Set.rank]

lemma abs_localScaledArg_sub_lt_one_of_localArgBin_eq
    (B : Set N) (hB : 0 < B.radius) {x y : ↥B.carrier}
    {r : ↥B.frequencies}
    (hbin : localArgBin B hB x r = localArgBin B hB y r) :
    |localScaledArg B (character r.1 x.1) -
      localScaledArg B (character r.1 y.1)| < 1 := by
  have hfloor :
      ⌊localScaledArg B (character r.1 x.1)⌋₊ =
        ⌊localScaledArg B (character r.1 y.1)⌋₊ :=
    congrArg Fin.val hbin
  have hfloorR :
      (⌊localScaledArg B (character r.1 x.1)⌋₊ : ℝ) =
        ⌊localScaledArg B (character r.1 y.1)⌋₊ := by
    exact_mod_cast hfloor
  have hxlow :
      (⌊localScaledArg B (character r.1 x.1)⌋₊ : ℝ) ≤
        localScaledArg B (character r.1 x.1) :=
    Nat.floor_le (localScaledArg_nonneg B hB x.2 r.2)
  have hylow :
      (⌊localScaledArg B (character r.1 y.1)⌋₊ : ℝ) ≤
        localScaledArg B (character r.1 y.1) :=
    Nat.floor_le (localScaledArg_nonneg B hB y.2 r.2)
  have hxup := Nat.lt_floor_add_one
    (localScaledArg B (character r.1 x.1))
  have hyup := Nat.lt_floor_add_one
    (localScaledArg B (character r.1 y.1))
  rw [abs_lt]
  constructor <;> nlinarith

lemma abs_arg_sub_lt_half_radius_of_localArgBin_eq
    (B : Set N) (hB : 0 < B.radius) {x y : ↥B.carrier}
    {r : ↥B.frequencies}
    (hbin : localArgBin B hB x r = localArgBin B hB y r) :
    |(character r.1 x.1).arg - (character r.1 y.1).arg| < B.radius / 2 := by
  have h := abs_localScaledArg_sub_lt_one_of_localArgBin_eq B hB hbin
  have hscale :
      |localScaledArg B (character r.1 x.1) -
        localScaledArg B (character r.1 y.1)| =
      2 * |(character r.1 x.1).arg - (character r.1 y.1).arg| / B.radius := by
    have heq :
        localScaledArg B (character r.1 x.1) -
          localScaledArg B (character r.1 y.1) =
        2 * ((character r.1 x.1).arg - (character r.1 y.1).arg) /
          B.radius := by
      unfold localScaledArg
      ring
    rw [heq, abs_div, abs_mul, abs_of_pos hB]
    norm_num
  rw [hscale] at h
  rw [div_lt_iff₀ hB] at h
  linarith

lemma sub_mem_half_dilate_of_localArgumentCode_eq
    (B : Set N) (hB : 0 < B.radius) {x y : ↥B.carrier}
    (hcode : localArgumentCode B hB x = localArgumentCode B hB y) :
    x.1 - y.1 ∈ B.dilate (1 / 2 : ℝ) := by
  rw [Set.mem_iff]
  intro r hr
  have hbin : localArgBin B hB x ⟨r, hr⟩ =
      localArgBin B hB y ⟨r, hr⟩ := congrFun hcode ⟨r, hr⟩
  calc
    ‖1 - character r (x.1 - y.1)‖ =
        ‖character r x.1 - character r y.1‖ :=
      norm_one_sub_character_sub r x.1 y.1
    _ ≤ |(character r x.1).arg - (character r y.1).arg| :=
      norm_sub_le_abs_arg_sub_of_norm_eq_one
        (norm_character r x.1) (norm_character r y.1)
    _ ≤ B.radius / 2 :=
      (abs_arg_sub_lt_half_radius_of_localArgBin_eq B hB hbin).le
    _ = (B.dilate (1 / 2 : ℝ)).radius := by
      simp [div_eq_mul_inv, mul_comm]

theorem card_carrier_le_nine_pow_rank_mul_card_half
    (B : Set N) (hB : 0 < B.radius) :
    B.carrier.card ≤ 9 ^ B.rank * (B.dilate (1 / 2 : ℝ)).carrier.card := by
  let Q := (r : ↥B.frequencies) → Fin 9
  let code : ↥B.carrier → Q := localArgumentCode B hB
  have hQ : Fintype.card Q = 9 ^ B.rank := by
    simpa [Q] using card_localArgumentCodeSpace B
  have hmain : Fintype.card ↥B.carrier ≤
      Fintype.card Q * (B.dilate (1 / 2 : ℝ)).carrier.card := by
    by_contra hbound
    rw [not_le] at hbound
    obtain ⟨q, hq⟩ :=
      Fintype.exists_lt_card_fiber_of_mul_lt_card (f := code) hbound
    let S : Finset ↥B.carrier := Finset.univ.filter fun x ↦ code x = q
    have hScard : (B.dilate (1 / 2 : ℝ)).carrier.card < S.card := by
      simpa [S] using hq
    have hSnonempty : S.Nonempty := Finset.card_pos.mp
      (lt_of_le_of_lt (Nat.zero_le _) hScard)
    obtain ⟨x₀, hx₀⟩ := hSnonempty
    let e : ↥B.carrier ↪ ZMod N :=
      ⟨fun x ↦ x.1 - x₀.1, by
        intro x y hxy
        apply Subtype.ext
        exact (Equiv.subRight x₀.1).injective hxy⟩
    have hmap : S.map e ⊆ (B.dilate (1 / 2 : ℝ)).carrier := by
      intro z hz
      rw [Finset.mem_map] at hz
      obtain ⟨x, hxS, rfl⟩ := hz
      have hcodex : code x = q := by simpa [S] using hxS
      have hcodex₀ : code x₀ = q := by simpa [S] using hx₀
      exact sub_mem_half_dilate_of_localArgumentCode_eq B hB
        (hcodex.trans hcodex₀.symm)
    have hle : S.card ≤ (B.dilate (1 / 2 : ℝ)).carrier.card := by
      calc
        S.card = (S.map e).card := (Finset.card_map e).symm
        _ ≤ (B.dilate (1 / 2 : ℝ)).carrier.card := Finset.card_le_card hmap
    omega
  rw [hQ] at hmain
  have hcardcoe : Fintype.card ↥B.carrier = B.carrier.card :=
    Fintype.card_coe B.carrier
  rw [hcardcoe] at hmain
  exact hmain

end CyclicBohr
end Erdos3

end

section

namespace Erdos3.CyclicBohr.Set

open scoped BigOperators

variable {N : ℕ} [NeZero N]

lemma norm_one_sub_prod_le_sum {ι : Type*}
    (s : Finset ι) (f : ι → ℂ) (hf : ∀ i ∈ s, ‖f i‖ ≤ 1) :
    ‖1 - ∏ i ∈ s, f i‖ ≤ ∑ i ∈ s, ‖1 - f i‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      exact (norm_one_sub_mul_of_norm_le_one (hf a (by simp))).trans
        (add_le_add le_rfl (ih fun i hi ↦ hf i (by simp [hi])))

lemma character_sum {ι : Type*} (s : Finset ι)
    (f : ι → ZMod N) (x : ZMod N) :
    character (∑ i ∈ s, f i) x = ∏ i ∈ s, character (f i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, ih, character_add_index]

@[simp] lemma character_neg_index (r x : ZMod N) :
    character (-r) x = (starRingEnd ℂ) (character r x) := by
  rw [character_comm, AddChar.map_neg_eq_conj, character_comm]

@[simp]
lemma norm_one_sub_character_neg_index (r x : ZMod N) :
    ‖1 - character (-r) x‖ = ‖1 - character r x‖ := by
  rw [character_neg_index]
  simpa using (RCLike.norm_conj (1 - character r x))

def signedSpan (B : Set N) : _root_.Set (ZMod N) :=
  B.frequencies.addSpan

lemma norm_one_sub_character_le_rank_mul {B : Set N} {r x : ZMod N}
    (hr : r ∈ B.signedSpan) (hx : x ∈ B) :
    ‖1 - character r x‖ ≤ B.rank * B.radius := by
  rw [signedSpan] at hr
  obtain ⟨ε, hε, hsum⟩ := Finset.mem_addSpan.mp hr
  rw [← hsum]
  rw [character_sum]
  calc
    ‖1 - ∏ g ∈ B.frequencies, character (ε g • g) x‖ ≤
        ∑ g ∈ B.frequencies, ‖1 - character (ε g • g) x‖ :=
      norm_one_sub_prod_le_sum B.frequencies (fun g ↦ character (ε g • g) x)
        (fun g hg ↦ by rw [norm_character])
    _ ≤ ∑ _g ∈ B.frequencies, B.radius := by
      apply Finset.sum_le_sum
      intro g hg
      rcases hε g with hneg | hzero | hone
      · rw [hneg, neg_one_zsmul, norm_one_sub_character_neg_index]
        exact mem_iff.mp hx g hg
      · simp [hzero, B.radius_nonneg]
      · simpa [hone] using mem_iff.mp hx g hg
    _ = B.rank * B.radius := by simp [rank]

end Erdos3.CyclicBohr.Set

end

section

namespace Erdos3.CyclicBohr

lemma character_eq_one_mul {N : ℕ} [NeZero N] (r x : ZMod N) :
    character r x = character 1 (r * x) := by
  change (↑(AddChar.zmod N r x) : ℂ) = ↑(AddChar.zmod N 1 (r * x))
  simp [AddChar.zmod]

lemma norm_one_sub_character_intCast {N : ℕ} [NeZero N] (t : ℤ) :
    ‖1 - character 1 (t : ZMod N)‖ ≤ 8 * |(t : ℝ)| / N := by
  change ‖1 - (↑(AddChar.zmod N 1 (t : ZMod N)) : ℂ)‖ ≤ _
  rw [show (1 : ZMod N) = ((1 : ℤ) : ZMod N) by simp]
  rw [AddChar.zmod_intCast, Circle.coe_exp, norm_sub_rev]
  simp only [Int.cast_one, one_mul]
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hnorm : ‖Complex.exp ((2 * Real.pi * ((t : ℝ) / N) : ℝ) *
      Complex.I) - 1‖ ≤ |2 * Real.pi * ((t : ℝ) / N)| := by
    simpa only [mul_comm, Real.norm_eq_abs]
      using (Real.norm_exp_I_mul_ofReal_sub_one_le
        (x := 2 * Real.pi * ((t : ℝ) / N)))
  refine hnorm.trans ?_
  rw [← mul_div_assoc, abs_div, abs_mul, abs_mul, abs_of_pos hN,
    abs_of_pos Real.pi_pos, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  gcongr
  linarith [Real.pi_le_four]

lemma norm_one_sub_character_le_of_mul_eq_intCast {N : ℕ} [NeZero N]
    (r x : ZMod N) (t : ℤ) (h : r * x = (t : ZMod N)) :
    ‖1 - character r x‖ ≤ 8 * |(t : ℝ)| / N := by
  rw [character_eq_one_mul, h]
  exact norm_one_sub_character_intCast t

end Erdos3.CyclicBohr

end

section

namespace Erdos3.CyclicBohr

open Finset
open scoped BigOperators

variable {N : ℕ} [NeZero N]

theorem card_le_codeCard_mul_card (B : Set N) {m : ℕ} (hm : 0 < m)
    (hwidth : 2 * Real.pi / m ≤ B.radius) :
    N ≤ (m + 1) ^ B.rank * B.carrier.card := by
  classical
  let Q := (r : ↥B.frequencies) → Fin (m + 1)
  let code : ZMod N → Q := argumentCode B m
  have hQ : Fintype.card Q = (m + 1) ^ B.rank := card_argumentCodeSpace B m
  by_contra h
  have hsmall : Fintype.card Q * B.carrier.card < Fintype.card (ZMod N) := by
    simpa only [hQ, ZMod.card] using (not_le.mp h)
  obtain ⟨q, hq⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card (f := code) hsmall
  let A := Finset.univ.filter (fun x : ZMod N => code x = q)
  have hA : B.carrier.card < A.card := by simpa only [A] using hq
  obtain ⟨x₀, hx₀⟩ := Finset.card_pos.mp ((Nat.zero_le _).trans_lt hA)
  let e : ZMod N ↪ ZMod N := (Equiv.subRight x₀).toEmbedding
  have hmap : A.map e ⊆ B.carrier := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hz
    exact sub_mem_of_argumentCode_eq B hm hwidth
      ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hx₀).2.symm)
  have hcard := Finset.card_le_card hmap
  rw [Finset.card_map] at hcard
  omega

theorem card_lower_bound (B : Set N) (hB : 0 < B.radius) (hB1 : B.radius ≤ 1) :
    (B.radius / 10) ^ B.rank * N ≤ (B.carrier.card : ℝ) := by
  let m := ⌈2 * Real.pi / B.radius⌉₊
  have hratio : 0 < 2 * Real.pi / B.radius := div_pos (by positivity) hB
  have hm : 0 < m := Nat.ceil_pos.mpr hratio
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hwidth : 2 * Real.pi / m ≤ B.radius := by
    rw [div_le_iff₀ hmR]
    have h := (div_le_iff₀ hB).mp (Nat.le_ceil (2 * Real.pi / B.radius))
    nlinarith
  have hcode : (N : ℝ) ≤ ((m + 1 : ℕ) : ℝ) ^ B.rank * B.carrier.card := by
    exact_mod_cast card_le_codeCard_mul_card B hm hwidth
  have hmUpper : ((m + 1 : ℕ) : ℝ) ≤ 10 / B.radius := by
    have hceil := Nat.ceil_lt_add_one hratio.le
    rw [Nat.cast_add, Nat.cast_one]
    change (⌈2 * Real.pi / B.radius⌉₊ : ℝ) + 1 ≤ _
    rw [le_div_iff₀ hB]
    have hceilmul := mul_lt_mul_of_pos_right hceil hB
    have hquot : (2 * Real.pi / B.radius) * B.radius = 2 * Real.pi :=
      div_mul_cancel₀ _ hB.ne'
    nlinarith [Real.pi_lt_four]
  have hpower : ((B.radius / 10) * ((m + 1 : ℕ) : ℝ)) ^ B.rank ≤ 1 := by
    apply pow_le_one₀ (by positivity)
    have hmul := mul_le_mul_of_nonneg_left hmUpper (show 0 ≤ B.radius / 10 by positivity)
    have heq : B.radius / 10 * (10 / B.radius) = 1 := by field_simp
    exact hmul.trans_eq heq
  calc
    _ ≤ (B.radius / 10) ^ B.rank * (((m + 1 : ℕ) : ℝ) ^ B.rank * B.carrier.card) :=
      mul_le_mul_of_nonneg_left hcode (by positivity)
    _ = ((B.radius / 10) * ((m + 1 : ℕ) : ℝ)) ^ B.rank * B.carrier.card := by
      rw [mul_pow]
      ring
    _ ≤ 1 * (B.carrier.card : ℝ) := mul_le_mul_of_nonneg_right hpower (Nat.cast_nonneg _)
    _ = _ := one_mul _

theorem card_two_le_nine_pow_three_rank_mul_card_quarter (B : Set N) (hB : 0 < B.radius) :
    (B.dilate 2).carrier.card ≤ 9 ^ (3 * B.rank) * (B.dilate (1 / 4)).carrier.card := by
  have h₂ := card_carrier_le_nine_pow_rank_mul_card_half (B.dilate 2)
    (show 0 < (B.dilate 2).radius by simpa using mul_pos (by norm_num : (0 : ℝ) < 2) hB)
  have h₁ := card_carrier_le_nine_pow_rank_mul_card_half B hB
  have hh := card_carrier_le_nine_pow_rank_mul_card_half (B.dilate (1 / 2))
    (show 0 < (B.dilate (1 / 2)).radius by simpa using mul_pos (by norm_num : (0 : ℝ) < 1 / 2) hB)
  simp only [Set.rank_dilate, Set.dilate_dilate] at h₂ hh
  norm_num at h₂ hh
  calc
    _ ≤ 9 ^ B.rank * B.carrier.card := h₂
    _ ≤ 9 ^ B.rank * (9 ^ B.rank * (B.dilate (1 / 2)).carrier.card) := Nat.mul_le_mul_left _ h₁
    _ ≤ 9 ^ B.rank * (9 ^ B.rank * (9 ^ B.rank * (B.dilate (1 / 4)).carrier.card)) := by
      gcongr
    _ = _ := by
      rw [← mul_assoc, ← pow_add, ← mul_assoc, ← pow_add]
      congr 2
      omega

end Erdos3.CyclicBohr

end

section

namespace Erdos3.CyclicBohr

variable {N : ℕ} [NeZero N]

theorem card_le_dyadic_dilate (B : Set N) (hB : 0 < B.radius) (k : ℕ) :
    B.carrier.card ≤ 9 ^ (k * B.rank) * (B.dilate ((1 / 2 : ℝ) ^ k)).carrier.card := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hpos : 0 < (B.dilate ((1 / 2 : ℝ) ^ k)).radius := by
      simp only [Set.radius_dilate, abs_of_nonneg (pow_nonneg (by norm_num) _)]
      positivity
    have hh := card_carrier_le_nine_pow_rank_mul_card_half (B.dilate ((1 / 2 : ℝ) ^ k)) hpos
    have heq : (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ k = (1 / 2 : ℝ) ^ (k + 1) := by
      rw [pow_succ, mul_comm]
    simp only [Set.rank_dilate, Set.dilate_dilate, heq] at hh
    calc
      _ ≤ 9 ^ (k * B.rank) * (B.dilate ((1 / 2 : ℝ) ^ k)).carrier.card := ih
      _ ≤ 9 ^ (k * B.rank) *
          (9 ^ B.rank * (B.dilate ((1 / 2 : ℝ) ^ (k + 1))).carrier.card) := Nat.mul_le_mul_left _ hh
      _ = _ := by simp only [Nat.add_mul, Nat.one_mul, pow_add, mul_assoc]

theorem relative_card_lower_bound (B : Set N) (hB : 0 < B.radius)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    (r / 2) ^ (4 * B.rank) * (B.carrier.card : ℝ) ≤ (B.dilate r).carrier.card := by
  obtain ⟨n, hn, hn'⟩ := exists_nat_pow_near_of_lt_one hr hr1
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  let k := n + 1
  have hk : (1 / 2 : ℝ) ^ k ≤ r := hn.le
  have hhalf : r / 2 ≤ (1 / 2 : ℝ) ^ k := by
    dsimp [k]
    rw [pow_succ]
    nlinarith
  have hd := card_le_dyadic_dilate B hB k
  have hdR : (B.carrier.card : ℝ) ≤
      (9 : ℝ) ^ (k * B.rank) * (B.dilate ((1 / 2 : ℝ) ^ k)).carrier.card := by exact_mod_cast hd
  have hcoef : ((1 / 2 : ℝ) ^ k) ^ (4 * B.rank) * 9 ^ (k * B.rank) ≤ 1 := by
    calc
      _ = ((1 / 2 : ℝ) ^ 4) ^ (k * B.rank) * 9 ^ (k * B.rank) := by
        congr 1
        rw [← pow_mul, ← pow_mul]
        congr 1
        ring
      _ = ((1 / 2 : ℝ) ^ 4 * 9) ^ (k * B.rank) := (mul_pow _ _ _).symm
      _ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  calc
    _ ≤ ((1 / 2 : ℝ) ^ k) ^ (4 * B.rank) * B.carrier.card :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hhalf _) (Nat.cast_nonneg _)
    _ ≤ ((1 / 2 : ℝ) ^ k) ^ (4 * B.rank) *
        (9 ^ (k * B.rank) * (B.dilate ((1 / 2 : ℝ) ^ k)).carrier.card) :=
      mul_le_mul_of_nonneg_left hdR (by positivity)
    _ ≤ 1 * ((B.dilate ((1 / 2 : ℝ) ^ k)).carrier.card : ℝ) := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg _)
    _ ≤ (B.dilate r).carrier.card := by
      rw [one_mul]
      exact_mod_cast Finset.card_le_card (B.dilate_mono (pow_nonneg (by norm_num) _) hk)

end Erdos3.CyclicBohr

end

section

namespace Erdos3.CyclicBohr.Set

theorem card_lower_bound_of_quartic_rank {N : ℕ} [NeZero N]
    (B : Set N) {C p : ℝ} (hC : 0 ≤ C) (hp : 0 ≤ p)
    (hB : 0 < B.radius) (hB1 : B.radius ≤ 1)
    (hrank : (B.rank : ℝ) ≤ 1 + C * (p + 1) ^ 4)
    (hwidth : Real.exp (-(C * (p + 1))) ≤ B.radius) :
    Real.exp (-((C + 10) * (C + 1) * (p + 1) ^ 5)) * N ≤ (B.carrier.card : ℝ) := by
  let u := p + 1
  have hu : 1 ≤ u := by dsimp [u]; linarith
  have hu4 : 1 ≤ u ^ 4 := one_le_pow₀ hu
  have hten : Real.exp (-10) ≤ (1 / 10 : ℝ) := by
    rw [Real.exp_neg, ← one_div]
    apply one_div_le_one_div_of_le (by norm_num)
    linarith [Real.add_one_le_exp (10 : ℝ)]
  have hbase : Real.exp (-((C + 10) * u)) ≤ B.radius / 10 := by
    calc
      Real.exp (-((C + 10) * u)) ≤ Real.exp (-(C * u)) * Real.exp (-10) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        nlinarith
      _ ≤ Real.exp (-(C * u)) * (1 / 10) :=
        mul_le_mul_of_nonneg_left hten (Real.exp_pos _).le
      _ ≤ B.radius * (1 / 10) := mul_le_mul_of_nonneg_right hwidth (by norm_num)
      _ = B.radius / 10 := by ring
  have hr : (B.rank : ℝ) ≤ (C + 1) * u ^ 4 := by
    calc
      (B.rank : ℝ) ≤ 1 + C * u ^ 4 := hrank
      _ ≤ (C + 1) * u ^ 4 := by nlinarith
  have hexponent : (B.rank : ℝ) * ((C + 10) * u) ≤ (C + 10) * (C + 1) * u ^ 5 := by
    calc
      (B.rank : ℝ) * ((C + 10) * u) ≤ ((C + 1) * u ^ 4) * ((C + 10) * u) :=
        mul_le_mul_of_nonneg_right hr (by positivity)
      _ = _ := by ring
  have hpower : Real.exp (-((C + 10) * (C + 1) * u ^ 5)) ≤
      (B.radius / 10) ^ B.rank := by
    calc
      Real.exp (-((C + 10) * (C + 1) * u ^ 5)) ≤
          Real.exp ((B.rank : ℝ) * (-((C + 10) * u))) := by
        apply Real.exp_le_exp.mpr
        nlinarith
      _ = Real.exp (-((C + 10) * u)) ^ B.rank := Real.exp_nat_mul _ _
      _ ≤ (B.radius / 10) ^ B.rank := pow_le_pow_left₀ (by positivity) hbase _
  exact (mul_le_mul_of_nonneg_right hpower (Nat.cast_nonneg N)).trans
    (CyclicBohr.card_lower_bound B hB hB1)

end Erdos3.CyclicBohr.Set

end

end OAI
