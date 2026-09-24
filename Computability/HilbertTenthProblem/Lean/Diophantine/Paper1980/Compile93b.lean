import Diophantine.Paper1980.Compile93a
import Diophantine.Paper1980.Circuit

/-!
# Compiling a gate circuit into a layout (Section 1)

A circuit `C` over `cm` coordinates is compiled into `9 cm + 11` physical
coordinates: every circuit coordinate `c` gets three groups `P c, Q c, R c`
of three physical coordinates (with copy rows `Q c = P c`, `R c = P c`), the
normalization values `Y, Z, u` get one group each, and `δ, δ'` are single
coordinates.  Each circuit row becomes one paired row (its negation is
added by the layout); the normalization rows `P_inp² = x²`, `Y² = x²`,
`Z² = x²`, `δ'² = δ²`, `2x P_inp − 2δδ' − 2uδ = 0` and the padding sets
`P₅ = P_inp ∪ Y`, `P₇ = P₅ ∪ Z` complete the layout.

* `pairedRows_valid`: every paired row is valid;
* `decode_*`: if every paired row vanishes at nonnegative digits `z`, then
  `1 ≤ δ ≤ x`, `Σ_{P₅} z = 2x`, `Σ_{P₇} z = 3x`, and if moreover `δ = 1`
  the circuit accepts `x`;
* `witness`: conversely an accepting assignment yields digits `z` with
  bit `j` clear (for any `j ≥ 1`) at which every paired row vanishes and
  `δ = 1`.
-/

namespace Jones1980

namespace Iso

open Layout

section Phys

variable (cm : ℕ)

/-- The number of physical coordinates. -/
def nphys : ℕ := 9 * cm + 11

/-- Coordinate `a` of group `G`. -/
def phys (G : ℕ) (hG : G < 3 * cm + 3) (a : Fin 3) : Fin (nphys cm) :=
  ⟨3 * G + a, by unfold nphys; have := a.isLt; omega⟩

def gP (c : Fin cm) : Fin 3 → Fin (nphys cm) := phys cm (3 * c) (by have := c.isLt; omega)
def gQ (c : Fin cm) : Fin 3 → Fin (nphys cm) := phys cm (3 * c + 1) (by have := c.isLt; omega)
def gR (c : Fin cm) : Fin 3 → Fin (nphys cm) := phys cm (3 * c + 2) (by have := c.isLt; omega)
def gY : Fin 3 → Fin (nphys cm) := phys cm (3 * cm) (by omega)
def gZ : Fin 3 → Fin (nphys cm) := phys cm (3 * cm + 1) (by omega)
def gU : Fin 3 → Fin (nphys cm) := phys cm (3 * cm + 2) (by omega)
def iδ : Fin (nphys cm) := ⟨9 * cm + 9, by unfold nphys; omega⟩
def iδ' : Fin (nphys cm) := ⟨9 * cm + 10, by unfold nphys; omega⟩

theorem phys_val (G : ℕ) (hG : G < 3 * cm + 3) (a : Fin 3) :
    (phys cm G hG a).val = 3 * G + a := rfl

theorem phys_eq_iff {G G' : ℕ} {hG : G < 3 * cm + 3} {hG' : G' < 3 * cm + 3} {a b : Fin 3} :
    phys cm G hG a = phys cm G' hG' b ↔ G = G' ∧ a = b := by
  rw [Fin.ext_iff, phys_val, phys_val]
  constructor
  · intro h
    have := a.isLt; have := b.isLt
    exact ⟨by omega, Fin.ext (by omega)⟩
  · rintro ⟨rfl, rfl⟩; rfl

theorem phys_injective (G : ℕ) (hG : G < 3 * cm + 3) : Function.Injective (phys cm G hG) :=
  fun a b h => ((phys_eq_iff cm).1 h).2

theorem phys_disj {G G' : ℕ} (hG : G < 3 * cm + 3) (hG' : G' < 3 * cm + 3) (h : G ≠ G') :
    Disj (phys cm G hG) (phys cm G' hG') :=
  fun a b hab => h ((phys_eq_iff cm).1 hab).1

theorem phys_avoids_δ (G : ℕ) (hG : G < 3 * cm + 3) : Avoids (phys cm G hG) (iδ cm) := by
  intro a h
  rw [Fin.ext_iff, phys_val] at h
  simp only [iδ] at h
  have := a.isLt; omega

theorem phys_avoids_δ' (G : ℕ) (hG : G < 3 * cm + 3) : Avoids (phys cm G hG) (iδ' cm) := by
  intro a h
  rw [Fin.ext_iff, phys_val] at h
  simp only [iδ'] at h
  have := a.isLt; omega

theorem iδ_ne : iδ cm ≠ iδ' cm := by
  intro h; rw [Fin.ext_iff] at h; simp [iδ, iδ'] at h

end Phys

section Rows

variable (cm : ℕ)

/-- The paired row of a circuit row. -/
def circRow (ρ : Gates.Row cm) : Row (nphys cm) :=
  match ρ with
  | .add i j k => addRow (gP cm i) (gQ cm j) (gR cm k) (iδ cm)
  | .mul i j k => mulRow (gP cm i) (gQ cm j) (gR cm k) (iδ cm)
  | .eq i j => copyRow (gP cm i) (gQ cm j)
  | .zero i => zeroRow (gP cm i) (iδ cm)
  | .one i => oneRow (gP cm i) (iδ cm) (iδ' cm)

/-- The copy rows `Q c = P c`, `R c = P c`. -/
def copyRows : List (Row (nphys cm)) :=
  (List.finRange cm).flatMap fun c => [copyRow (gQ cm c) (gP cm c), copyRow (gR cm c) (gP cm c)]

/-- The normalization rows. -/
def normRows (inp : Fin cm) : List (Row (nphys cm)) :=
  [normRow (gP cm inp), normRow (gY cm), normRow (gZ cm), deltaRow (iδ cm) (iδ' cm),
    uRow (gP cm inp) (iδ cm) (iδ' cm) (gU cm)]

/-- All paired rows of a circuit. -/
def pairedRows (C : Gates.Circuit) : List (Row (nphys C.m)) :=
  copyRows C.m ++ C.rows.map (circRow C.m) ++ normRows C.m C.inp

/-- The padding sets. -/
def P5 (C : Gates.Circuit) : Finset (Fin (nphys C.m)) :=
  Finset.univ.image (gP C.m C.inp) ∪ Finset.univ.image (gY C.m)

def P7 (C : Gates.Circuit) : Finset (Fin (nphys C.m)) :=
  P5 C ∪ Finset.univ.image (gZ C.m)

theorem circRow_struct (ρ : Gates.Row cm) : RowStruct (circRow cm ρ) := by
  cases ρ with
  | add i j k =>
    exact addRow_struct (phys_injective _ _ _) (phys_injective _ _ _) (phys_injective _ _ _)
      (phys_disj _ _ _ (by omega)) (phys_disj _ _ _ (by omega)) (phys_disj _ _ _ (by omega))
      (phys_avoids_δ _ _ _) (phys_avoids_δ _ _ _) (phys_avoids_δ _ _ _)
  | mul i j k =>
    exact mulRow_struct (phys_injective _ _ _) (phys_injective _ _ _) (phys_injective _ _ _)
      (phys_disj _ _ _ (by omega)) (phys_disj _ _ _ (by omega)) (phys_disj _ _ _ (by omega))
      (phys_avoids_δ _ _ _) (phys_avoids_δ _ _ _) (phys_avoids_δ _ _ _)
  | eq i j =>
    exact copyRow_struct (phys_injective _ _ _) (phys_injective _ _ _) (phys_disj _ _ _ (by omega))
  | zero i => exact zeroRow_struct (phys_injective _ _ _) (phys_avoids_δ _ _ _)
  | one i =>
    exact oneRow_struct (phys_injective _ _ _) (phys_avoids_δ _ _ _) (phys_avoids_δ' _ _ _)
      (iδ_ne cm)

theorem pairedRows_struct (C : Gates.Circuit) : ∀ R ∈ pairedRows C, RowStruct R := by
  intro R hR
  unfold pairedRows at hR
  simp only [List.mem_append, copyRows, List.mem_flatMap, List.mem_finRange, true_and,
    List.mem_cons, List.not_mem_nil, or_false, List.mem_map, normRows] at hR
  rcases hR with (⟨c, rfl | rfl⟩ | ⟨ρ, _, rfl⟩) | rfl | rfl | rfl | rfl | rfl
  · exact copyRow_struct (phys_injective _ _ _) (phys_injective _ _ _)
      (phys_disj _ _ _ (by omega))
  · exact copyRow_struct (phys_injective _ _ _) (phys_injective _ _ _)
      (phys_disj _ _ _ (by omega))
  · exact circRow_struct _ ρ
  · exact normRow_struct (phys_injective _ _ _)
  · exact normRow_struct (phys_injective _ _ _)
  · exact normRow_struct (phys_injective _ _ _)
  · exact deltaRow_struct (iδ_ne _)
  · exact uRow_struct (phys_injective _ _ _) (phys_injective _ _ _) (phys_avoids_δ _ _ _)
      (phys_avoids_δ' _ _ _) (iδ_ne _)

theorem pairedRows_valid (C : Gates.Circuit) : ∀ R ∈ pairedRows C, RowValid R :=
  fun R hR => (pairedRows_struct C R hR).valid

end Rows

section Decode

variable {C : Gates.Circuit} {x : ℕ} {z : Fin (nphys C.m) → ℕ}

/-- The natural sum of a group. -/
def SN {m : ℕ} (g : Fin 3 → Fin m) (z : Fin m → ℕ) : ℕ := z (g 0) + z (g 1) + z (g 2)

theorem S_cast {m : ℕ} (g : Fin 3 → Fin m) (z : Fin m → ℕ) :
    S g (fun i => (z i : ℤ)) = (SN g z : ℤ) := by
  unfold S SN; push_cast; ring

theorem mem_normRows (R : Row (nphys C.m)) (h : R ∈ normRows C.m C.inp) : R ∈ pairedRows C := by
  unfold pairedRows
  simp only [List.mem_append]
  exact Or.inr h

theorem sum_image_group {m : ℕ} (g : Fin 3 → Fin m) (hg : Function.Injective g)
    (z : Fin m → ℕ) : ∑ q ∈ Finset.univ.image g, (z q : ℤ) = (SN g z : ℤ) := by
  rw [Finset.sum_image (fun a _ b _ h => hg h), Fin.sum_univ_three]
  unfold SN; push_cast; ring

variable (hrows : ∀ R ∈ pairedRows C, R.val (x : ℤ) (fun i => (z i : ℤ)) = 0)

include hrows

theorem decode_copy (c : Fin C.m) : SN (gQ C.m c) z = SN (gP C.m c) z ∧
    SN (gR C.m c) z = SN (gP C.m c) z := by
  have h1 := hrows (copyRow (gQ C.m c) (gP C.m c)) (by
    unfold pairedRows copyRows
    simp only [List.mem_append, List.mem_flatMap, List.mem_finRange, true_and, List.mem_cons,
      List.not_mem_nil, or_false]
    exact Or.inl (Or.inl ⟨c, Or.inl rfl⟩))
  have h2 := hrows (copyRow (gR C.m c) (gP C.m c)) (by
    unfold pairedRows copyRows
    simp only [List.mem_append, List.mem_flatMap, List.mem_finRange, true_and, List.mem_cons,
      List.not_mem_nil, or_false]
    exact Or.inl (Or.inl ⟨c, Or.inr rfl⟩))
  rw [copyRow_val, S_cast, S_cast, sub_eq_zero] at h1 h2
  exact ⟨by exact_mod_cast (sq_eq_sq₀ (by positivity) (by positivity)).1 h1,
    by exact_mod_cast (sq_eq_sq₀ (by positivity) (by positivity)).1 h2⟩

theorem decode_norm : SN (gP C.m C.inp) z = x ∧ SN (gY C.m) z = x ∧ SN (gZ C.m) z = x := by
  have h1 := hrows (normRow (gP C.m C.inp)) (mem_normRows _ (by simp [normRows]))
  have h2 := hrows (normRow (gY C.m)) (mem_normRows _ (by simp [normRows]))
  have h3 := hrows (normRow (gZ C.m)) (mem_normRows _ (by simp [normRows]))
  rw [normRow_val, S_cast, sub_eq_zero] at h1 h2 h3
  exact ⟨by exact_mod_cast (sq_eq_sq₀ (by positivity) (by positivity)).1 h1,
    by exact_mod_cast (sq_eq_sq₀ (by positivity) (by positivity)).1 h2,
    by exact_mod_cast (sq_eq_sq₀ (by positivity) (by positivity)).1 h3⟩

theorem decode_delta' : z (iδ' C.m) = z (iδ C.m) := by
  have h := hrows (deltaRow (iδ C.m) (iδ' C.m)) (mem_normRows _ (by simp [normRows]))
  rw [deltaRow_val, sub_eq_zero] at h
  exact_mod_cast (sq_eq_sq₀ (by positivity) (by positivity)).1 h

/-- `x² = δ² + δ u`. -/
theorem decode_u : x ^ 2 = z (iδ C.m) ^ 2 + z (iδ C.m) * SN (gU C.m) z := by
  have h := hrows (uRow (gP C.m C.inp) (iδ C.m) (iδ' C.m) (gU C.m))
    (mem_normRows _ (by simp [normRows]))
  rw [uRow_val, S_cast, S_cast] at h
  have h1 := (decode_norm hrows).1
  have h2 := decode_delta' hrows
  rw [h1, h2] at h
  have : (x : ℤ) ^ 2 = (z (iδ C.m) : ℤ) ^ 2 + z (iδ C.m) * SN (gU C.m) z := by linarith
  exact_mod_cast this

theorem decode_delta_bounds (hx : 1 ≤ x) : 1 ≤ z (iδ C.m) ∧ z (iδ C.m) ≤ x := by
  have h := decode_u hrows
  constructor
  · by_contra hcon
    have : z (iδ C.m) = 0 := by omega
    rw [this] at h
    simp at h
    omega
  · have : z (iδ C.m) ^ 2 ≤ x ^ 2 := by rw [h]; exact Nat.le_add_right _ _
    exact (Nat.pow_le_pow_iff_left two_ne_zero).1 this

theorem decode_pads : ∑ q ∈ P5 C, (z q : ℤ) = 2 * x ∧ ∑ q ∈ P7 C, (z q : ℤ) = 3 * x := by
  obtain ⟨h1, h2, h3⟩ := decode_norm hrows
  have hPY : Disjoint (Finset.univ.image (gP C.m C.inp)) (Finset.univ.image (gY C.m)) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at ha hb
    obtain ⟨a1, rfl⟩ := ha
    obtain ⟨b1, hb1⟩ := hb
    have := C.inp.isLt
    exact phys_disj C.m _ _ (by omega) b1 a1 hb1
  have hPYZ : Disjoint (P5 C) (Finset.univ.image (gZ C.m)) := by
    unfold P5
    rw [Finset.disjoint_union_left]
    constructor <;> rw [Finset.disjoint_left] <;> intro a ha hb <;>
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at ha hb <;>
      obtain ⟨a1, rfl⟩ := ha <;> obtain ⟨b1, hb1⟩ := hb
    · have := C.inp.isLt
      exact phys_disj C.m _ _ (by omega) b1 a1 hb1
    · exact phys_disj C.m _ _ (by omega) b1 a1 hb1
  have e5 : ∑ q ∈ P5 C, (z q : ℤ) = 2 * x := by
    unfold P5
    rw [Finset.sum_union hPY, sum_image_group (gP C.m C.inp) (phys_injective _ _ _),
      sum_image_group (gY C.m) (phys_injective _ _ _), h1, h2]
    ring
  refine ⟨e5, ?_⟩
  unfold P7
  rw [Finset.sum_union hPYZ, e5, sum_image_group (gZ C.m) (phys_injective _ _ _), h3]
  ring

theorem decode_accepts (hδ : z (iδ C.m) = 1) : C.Accepts x := by
  refine ⟨fun c => SN (gP C.m c) z, (decode_norm hrows).1, ?_⟩
  intro ρ hρ
  have hmem : circRow C.m ρ ∈ pairedRows C := by
    unfold pairedRows
    simp only [List.mem_append, List.mem_map]
    exact Or.inl (Or.inr ⟨ρ, hρ, rfl⟩)
  have h := hrows _ hmem
  have hδZ : (z (iδ C.m) : ℤ) = 1 := by exact_mod_cast hδ
  cases ρ with
  | add i j k =>
    simp only [circRow, addRow_val, S_cast, hδZ, mul_one] at h
    have h' := (mul_eq_zero.1 h).resolve_left (by norm_num)
    obtain ⟨hq, _⟩ := decode_copy hrows j
    obtain ⟨_, hr⟩ := decode_copy hrows k
    show SN (gP C.m i) z + SN (gP C.m j) z = SN (gP C.m k) z
    rw [← hq, ← hr]
    have : (SN (gP C.m i) z : ℤ) + SN (gQ C.m j) z = SN (gR C.m k) z := by linarith
    exact_mod_cast this
  | mul i j k =>
    simp only [circRow, mulRow_val, S_cast, hδZ, mul_one] at h
    have h' := (mul_eq_zero.1 h).resolve_left (by norm_num)
    obtain ⟨hq, _⟩ := decode_copy hrows j
    obtain ⟨_, hr⟩ := decode_copy hrows k
    show SN (gP C.m i) z * SN (gP C.m j) z = SN (gP C.m k) z
    rw [← hq, ← hr]
    have : (SN (gP C.m i) z : ℤ) * SN (gQ C.m j) z = SN (gR C.m k) z := by linarith
    exact_mod_cast this
  | eq i j =>
    simp only [circRow, copyRow_val, S_cast] at h
    obtain ⟨hq, _⟩ := decode_copy hrows j
    show SN (gP C.m i) z = SN (gP C.m j) z
    rw [← hq]
    rw [sub_eq_zero] at h
    exact_mod_cast (sq_eq_sq₀ (by positivity) (by positivity)).1 h
  | zero i =>
    simp only [circRow, zeroRow_val, S_cast, hδZ, mul_one] at h
    have h' := (mul_eq_zero.1 h).resolve_left (by norm_num)
    show SN (gP C.m i) z = 0
    exact_mod_cast h'
  | one i =>
    simp only [circRow, oneRow_val, S_cast, hδZ, mul_one] at h
    have h2 := decode_delta' hrows
    rw [h2, hδ] at h
    have h' := (mul_eq_zero.1 h).resolve_left (by norm_num)
    show SN (gP C.m i) z = 1
    have : (SN (gP C.m i) z : ℤ) = 1 := by push_cast at h'; linarith
    exact_mod_cast this

end Decode

section Witness

/-- The three-way split of a value: if bit `j` of `n` is clear, `(n, 0, 0)`; otherwise
`(n − 2^j, 2^(j−1), 2^(j−1))`. -/
def split (j n : ℕ) (a : Fin 3) : ℕ :=
  if n.testBit j then (if a = 0 then n - 2 ^ j else 2 ^ (j - 1)) else (if a = 0 then n else 0)

theorem split_sum (j n : ℕ) (hj : 1 ≤ j) : split j n 0 + split j n 1 + split j n 2 = n := by
  unfold split
  by_cases h : n.testBit j
  · rw [if_pos h, if_pos h, if_pos h, if_pos rfl, if_neg (by decide), if_neg (by decide)]
    have h1 := Nat.ge_two_pow_of_testBit h
    have h2 : 2 ^ j = 2 * 2 ^ (j - 1) := by
      rw [← pow_succ']; congr 1; omega
    omega
  · rw [if_neg h, if_neg h, if_neg h, if_pos rfl, if_neg (by decide), if_neg (by decide)]
    omega

theorem split_bit (j n : ℕ) (hj : 1 ≤ j) (a : Fin 3) : (split j n a).testBit j = false := by
  unfold split
  by_cases h : n.testBit j
  · rw [if_pos h]
    split_ifs with ha
    · -- `n − 2^j` has bit `j` clear
      rw [Nat.testBit_eq_decide_div_mod_eq] at h ⊢
      simp only [decide_eq_true_eq] at h
      simp only [decide_eq_false_iff_not]
      have h1 := Nat.ge_two_pow_of_testBit (by rw [Nat.testBit_eq_decide_div_mod_eq]; simpa using h)
      have : (n - 2 ^ j) / 2 ^ j = n / 2 ^ j - 1 := by
        have := Nat.sub_mul_div n (2 ^ j) 1
        rw [mul_one] at this; exact this
      rw [this]
      have h2 : 1 ≤ n / 2 ^ j := by
        rw [Nat.le_div_iff_mul_le (by positivity), one_mul]; exact h1
      generalize n / 2 ^ j = q at h h2 ⊢
      omega
    · exact Nat.testBit_lt_two_pow (Nat.pow_lt_pow_right (by norm_num) (by omega))
  · rw [if_neg h]
    split_ifs
    · rwa [Bool.not_eq_true] at h
    · simp

theorem split_le (j n : ℕ) (a : Fin 3) : split j n a ≤ n := by
  unfold split
  split_ifs with h
  · exact Nat.sub_le _ _
  · have h1 := Nat.ge_two_pow_of_testBit h
    have : 2 ^ (j - 1) ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact le_trans this h1
  · exact le_rfl
  · exact Nat.zero_le _

variable (cm : ℕ)

/-- The physical assignment of a circuit assignment `X`, input `x`, and bit `j`. -/
def assign (X : Fin cm → ℕ) (x j : ℕ) (i : Fin (nphys cm)) : ℕ :=
  if h : i.val / 3 < 3 * cm then split j (X ⟨i.val / 3 / 3, by omega⟩) ⟨i.val % 3, Nat.mod_lt _ (by norm_num)⟩
  else if i.val / 3 < 3 * cm + 2 then split j x ⟨i.val % 3, Nat.mod_lt _ (by norm_num)⟩
  else if i.val / 3 < 3 * cm + 3 then split j (x ^ 2 - 1) ⟨i.val % 3, Nat.mod_lt _ (by norm_num)⟩
  else 1

variable (X : Fin cm → ℕ) (x j : ℕ)

theorem assign_phys (G : ℕ) (hG : G < 3 * cm + 3) (a : Fin 3) :
    assign cm X x j (phys cm G hG a) =
      if h : G < 3 * cm then split j (X ⟨G / 3, by omega⟩) a
      else if G < 3 * cm + 2 then split j x a else split j (x ^ 2 - 1) a := by
  unfold assign
  have e1 : (phys cm G hG a).val / 3 = G := by rw [phys_val]; have := a.isLt; omega
  have e2 : (phys cm G hG a).val % 3 = a := by rw [phys_val]; have := a.isLt; omega
  have ea : (⟨(phys cm G hG a).val % 3, Nat.mod_lt _ (by norm_num)⟩ : Fin 3) = a :=
    Fin.ext e2
  simp only [e1, ea]
  split_ifs <;> first | rfl | omega

theorem assign_gP (c : Fin cm) (a : Fin 3) : assign cm X x j (gP cm c a) = split j (X c) a := by
  unfold gP; rw [assign_phys, dif_pos (by have := c.isLt; omega)]
  congr 2; exact Fin.ext (by simp only [Fin.val_mk]; omega)

theorem assign_gQ (c : Fin cm) (a : Fin 3) : assign cm X x j (gQ cm c a) = split j (X c) a := by
  unfold gQ; rw [assign_phys, dif_pos (by have := c.isLt; omega)]
  congr 2; exact Fin.ext (by simp only [Fin.val_mk]; omega)

theorem assign_gR (c : Fin cm) (a : Fin 3) : assign cm X x j (gR cm c a) = split j (X c) a := by
  unfold gR; rw [assign_phys, dif_pos (by have := c.isLt; omega)]
  congr 2; exact Fin.ext (by simp only [Fin.val_mk]; omega)

theorem assign_gY (a : Fin 3) : assign cm X x j (gY cm a) = split j x a := by
  unfold gY; rw [assign_phys, dif_neg (by omega), if_pos (by omega)]

theorem assign_gZ (a : Fin 3) : assign cm X x j (gZ cm a) = split j x a := by
  unfold gZ; rw [assign_phys, dif_neg (by omega), if_pos (by omega)]

theorem assign_gU (a : Fin 3) : assign cm X x j (gU cm a) = split j (x ^ 2 - 1) a := by
  unfold gU; rw [assign_phys, dif_neg (by omega), if_neg (by omega)]

theorem assign_iδ : assign cm X x j (iδ cm) = 1 := by
  unfold assign iδ; simp only
  rw [dif_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem assign_iδ' : assign cm X x j (iδ' cm) = 1 := by
  unfold assign iδ'; simp only
  rw [dif_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem SN_split (g : Fin 3 → Fin (nphys cm)) (n : ℕ) (hj : 1 ≤ j)
    (h : ∀ a, assign cm X x j (g a) = split j n a) : SN g (assign cm X x j) = n := by
  unfold SN; rw [h, h, h]; exact split_sum j n hj

theorem assign_bit (hj : 1 ≤ j) (i : Fin (nphys cm)) : (assign cm X x j i).testBit j = false := by
  unfold assign
  split_ifs
  · exact split_bit j _ hj _
  · exact split_bit j _ hj _
  · exact split_bit j _ hj _
  · exact Nat.testBit_lt_two_pow (by
      calc 1 < 2 ^ 1 := by norm_num
        _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj)

end Witness

section WitnessRows

variable {C : Gates.Circuit} {x : ℕ} (hx : 1 ≤ x) {X : Fin C.m → ℕ} (hX : X C.inp = x)
  (hR : ∀ ρ ∈ C.rows, ρ.Holds X) {j : ℕ} (hj : 1 ≤ j)

include hx hX hR hj

/-- Every paired row vanishes at the physical assignment of an accepting assignment. -/
theorem witness_rows : ∀ R ∈ pairedRows C,
    R.val (x : ℤ) (fun i => (assign C.m X x j i : ℤ)) = 0 := by
  intro R hR'
  have hP : ∀ c, SN (gP C.m c) (assign C.m X x j) = X c :=
    fun c => SN_split _ _ _ _ _ _ hj (assign_gP _ _ _ _ c)
  have hQ : ∀ c, SN (gQ C.m c) (assign C.m X x j) = X c :=
    fun c => SN_split _ _ _ _ _ _ hj (assign_gQ _ _ _ _ c)
  have hRc : ∀ c, SN (gR C.m c) (assign C.m X x j) = X c :=
    fun c => SN_split _ _ _ _ _ _ hj (assign_gR _ _ _ _ c)
  have hY : SN (gY C.m) (assign C.m X x j) = x := SN_split _ _ _ _ _ _ hj (assign_gY _ _ _ _)
  have hZ : SN (gZ C.m) (assign C.m X x j) = x := SN_split _ _ _ _ _ _ hj (assign_gZ _ _ _ _)
  have hU : SN (gU C.m) (assign C.m X x j) = x ^ 2 - 1 :=
    SN_split _ _ _ _ _ _ hj (assign_gU _ _ _ _)
  have hδ := assign_iδ C.m X x j
  have hδ' := assign_iδ' C.m X x j
  unfold pairedRows at hR'
  simp only [List.mem_append, copyRows, List.mem_flatMap, List.mem_finRange, true_and,
    List.mem_cons, List.not_mem_nil, or_false, List.mem_map, normRows] at hR'
  rcases hR' with (⟨c, rfl | rfl⟩ | ⟨ρ, hρ, rfl⟩) | rfl | rfl | rfl | rfl | rfl
  · rw [copyRow_val, S_cast, S_cast, hQ, hP]; ring
  · rw [copyRow_val, S_cast, S_cast, hRc, hP]; ring
  · have hh := hR ρ hρ
    cases ρ with
    | add i j' k =>
      simp only [circRow, addRow_val, S_cast, hP, hQ, hRc, hδ]
      simp only [Gates.Row.Holds] at hh
      have : (X i : ℤ) + X j' = X k := by exact_mod_cast hh
      linear_combination 2 * this
    | mul i j' k =>
      simp only [circRow, mulRow_val, S_cast, hP, hQ, hRc, hδ]
      simp only [Gates.Row.Holds] at hh
      have : (X i : ℤ) * X j' = X k := by exact_mod_cast hh
      linear_combination 2 * this
    | eq i j' =>
      simp only [circRow, copyRow_val, S_cast, hP, hQ]
      simp only [Gates.Row.Holds] at hh
      rw [hh]; ring
    | zero i =>
      simp only [circRow, zeroRow_val, S_cast, hP, hδ]
      simp only [Gates.Row.Holds] at hh
      rw [hh]; ring
    | one i =>
      simp only [circRow, oneRow_val, S_cast, hP, hδ, hδ']
      simp only [Gates.Row.Holds] at hh
      rw [hh]; ring
  · rw [normRow_val, S_cast, hP, hX]; ring
  · rw [normRow_val, S_cast, hY]; ring
  · rw [normRow_val, S_cast, hZ]; ring
  · rw [deltaRow_val, hδ, hδ']; ring
  · rw [uRow_val, S_cast, S_cast, hP, hX, hU, hδ, hδ']
    have : 1 ≤ x ^ 2 := Nat.one_le_pow _ _ hx
    push_cast [Nat.cast_sub this]
    ring

end WitnessRows

end Iso

end Jones1980
