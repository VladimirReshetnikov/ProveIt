import Diophantine.Paper1980.Compile90b

/-!
# Decoding and witnessing the compiled rows of the 90-operation layout

* `decode_*`: if every paired row vanishes at nonnegative digits `z`, then
  `Q c = R c = P c`, `X = V₀`, `δ' = δ`, `V₀² = δ² + δ u`, hence `1 ≤ δ ≤ V₀`
  once `V₀ ≥ 1`; and if moreover `δ = 1` and `V₀ = x` the circuit accepts `x`.
* `witness_rows90`: conversely the physical assignment `Iso.assign` of an
  accepting circuit assignment (with `V₀ = V₁ = x`, `δ = δ' = 1`, `u = x² − 1`)
  makes every paired row vanish; its digits have bit `j` clear.
-/

namespace Jones1980

namespace L90

open Layout (Row)
open Iso (negRow S SN S_cast sqTerms crossTerms prodTerms dotTerms copyRow addRow mulRow zeroRow
  oneRow deltaRow unitRow nphys phys gP gQ gR gU iδ iδ' phys_injective phys_disj circRow
  copyRows assign split assign_gP assign_gQ assign_gR assign_gY assign_gZ assign_gU assign_iδ
  assign_iδ' SN_split assign_bit sum_image_group copyRow_val addRow_val mulRow_val zeroRow_val
  oneRow_val deltaRow_val unitRow_val negRow_val)

/-- The cast of the group value of the 90-operation layout. -/
theorem S_cast90 {m : ℕ} (g : Fin 3 → Fin m) (z : Fin m → ℕ) :
    L90.S g (fun i => (z i : ℤ)) = (SN g z : ℤ) := by
  unfold L90.S SN; push_cast; ring

/-! ### Membership in the paired rows -/

theorem mem_paired_copy (C : Gates.Circuit) (c : Fin C.m) :
    copyRow (gQ C.m c) (gP C.m c) ∈ pairedRows90 C ∧
      copyRow (gR C.m c) (gP C.m c) ∈ pairedRows90 C := by
  unfold pairedRows90 copyRows
  simp only [List.mem_append, List.mem_flatMap, List.mem_finRange, true_and, List.mem_cons,
    List.not_mem_nil, or_false]
  exact ⟨Or.inl (Or.inl ⟨c, Or.inl rfl⟩), Or.inl (Or.inl ⟨c, Or.inr rfl⟩)⟩

theorem mem_paired_circ (C : Gates.Circuit) (ρ : Gates.Row C.m) (hρ : ρ ∈ C.rows) :
    circRow C.m ρ ∈ pairedRows90 C := by
  unfold pairedRows90
  simp only [List.mem_append, List.mem_map]
  exact Or.inl (Or.inr ⟨ρ, hρ, rfl⟩)

theorem mem_paired_norm (C : Gates.Circuit) (R : Row (nphys C.m))
    (h : R ∈ normRows90 C.m C.inp) : R ∈ pairedRows90 C := by
  unfold pairedRows90
  simp only [List.mem_append]
  exact Or.inr h

/-! ### Decoding -/

section Decode

variable {C : Gates.Circuit} {x : ℕ} {z : Fin (nphys C.m) → ℕ}
  (hrows : ∀ R ∈ pairedRows90 C, R.val (x : ℤ) (fun i => (z i : ℤ)) = 0)

include hrows

theorem decode_copy90 (c : Fin C.m) : SN (gQ C.m c) z = SN (gP C.m c) z ∧
    SN (gR C.m c) z = SN (gP C.m c) z := by
  have h1 := hrows _ (mem_paired_copy C c).1
  have h2 := hrows _ (mem_paired_copy C c).2
  rw [copyRow_val, S_cast, S_cast, sub_eq_zero] at h1 h2
  exact ⟨by exact_mod_cast (sq_eq_sq₀ (by positivity) (by positivity)).1 h1,
    by exact_mod_cast (sq_eq_sq₀ (by positivity) (by positivity)).1 h2⟩

/-- `X = V₀`. -/
theorem decode_X : SN (gP C.m C.inp) z = SN (gV0 C.m) z := by
  have h := hrows (copyRow (gP C.m C.inp) (gV0 C.m)) (mem_paired_norm C _ (by simp [normRows90]))
  rw [copyRow_val, S_cast, S_cast, sub_eq_zero] at h
  exact_mod_cast (sq_eq_sq₀ (by positivity) (by positivity)).1 h

theorem decode_delta'90 : z (iδ' C.m) = z (iδ C.m) := by
  have h := hrows (deltaRow (iδ C.m) (iδ' C.m)) (mem_paired_norm C _ (by simp [normRows90]))
  rw [deltaRow_val, sub_eq_zero] at h
  exact_mod_cast (sq_eq_sq₀ (by positivity) (by positivity)).1 h

/-- `V₀² = δ² + δ u`. -/
theorem decode_u90 : SN (gV0 C.m) z ^ 2 = z (iδ C.m) ^ 2 + z (iδ C.m) * SN (gU C.m) z := by
  have h := hrows (uRow90 (gV0 C.m) (gP C.m C.inp) (iδ C.m) (iδ' C.m) (gU C.m))
    (mem_paired_norm C _ (by simp [normRows90]))
  rw [uRow90_val, S_cast90, S_cast90, S_cast90] at h
  have h1 := decode_X hrows
  have h2 := decode_delta'90 hrows
  rw [h1, h2] at h
  have : (SN (gV0 C.m) z : ℤ) ^ 2 = (z (iδ C.m) : ℤ) ^ 2 + z (iδ C.m) * SN (gU C.m) z := by
    linarith
  exact_mod_cast this

theorem decode_delta_bounds90 (hV0 : 1 ≤ SN (gV0 C.m) z) :
    1 ≤ z (iδ C.m) ∧ z (iδ C.m) ≤ SN (gV0 C.m) z := by
  have h := decode_u90 hrows
  constructor
  · by_contra hcon
    have : z (iδ C.m) = 0 := by omega
    rw [this] at h
    simp at h
    omega
  · have : z (iδ C.m) ^ 2 ≤ SN (gV0 C.m) z ^ 2 := by rw [h]; exact Nat.le_add_right _ _
    exact (Nat.pow_le_pow_iff_left two_ne_zero).1 this

/-- The padding group `P_X` sums to `X`. -/
theorem decode_pad : ∑ q ∈ cPX C, (z q : ℤ) = (SN (gP C.m C.inp) z : ℤ) := by
  unfold cPX
  exact sum_image_group (gP C.m C.inp) (phys_injective _ _ _) z

theorem decode_accepts90 (hδ : z (iδ C.m) = 1) (hV0 : SN (gV0 C.m) z = x) : C.Accepts x := by
  refine ⟨fun c => SN (gP C.m c) z, ?_, ?_⟩
  · show SN (gP C.m C.inp) z = x
    rw [decode_X hrows, hV0]
  intro ρ hρ
  have h := hrows _ (mem_paired_circ C ρ hρ)
  have hδZ : (z (iδ C.m) : ℤ) = 1 := by exact_mod_cast hδ
  cases ρ with
  | add i j k =>
    simp only [circRow, addRow_val, S_cast, hδZ, mul_one] at h
    have h' := (mul_eq_zero.1 h).resolve_left (by norm_num)
    obtain ⟨hq, _⟩ := decode_copy90 hrows j
    obtain ⟨_, hr⟩ := decode_copy90 hrows k
    show SN (gP C.m i) z + SN (gP C.m j) z = SN (gP C.m k) z
    rw [← hq, ← hr]
    have : (SN (gP C.m i) z : ℤ) + SN (gQ C.m j) z = SN (gR C.m k) z := by linarith
    exact_mod_cast this
  | mul i j k =>
    simp only [circRow, mulRow_val, S_cast, hδZ, mul_one] at h
    have h' := (mul_eq_zero.1 h).resolve_left (by norm_num)
    obtain ⟨hq, _⟩ := decode_copy90 hrows j
    obtain ⟨_, hr⟩ := decode_copy90 hrows k
    show SN (gP C.m i) z * SN (gP C.m j) z = SN (gP C.m k) z
    rw [← hq, ← hr]
    have : (SN (gP C.m i) z : ℤ) * SN (gQ C.m j) z = SN (gR C.m k) z := by linarith
    exact_mod_cast this
  | eq i j =>
    simp only [circRow, copyRow_val, S_cast] at h
    obtain ⟨hq, _⟩ := decode_copy90 hrows j
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
    have h2 := decode_delta'90 hrows
    rw [h2, hδ] at h
    have h' := (mul_eq_zero.1 h).resolve_left (by norm_num)
    show SN (gP C.m i) z = 1
    have : (SN (gP C.m i) z : ℤ) = 1 := by push_cast at h'; linarith
    exact_mod_cast this

end Decode

/-! ### The witness assignment -/

section Witness

variable {C : Gates.Circuit} {x : ℕ} (hx : 1 ≤ x) {X : Fin C.m → ℕ} (hX : X C.inp = x)
  (hR : ∀ ρ ∈ C.rows, ρ.Holds X) {j : ℕ} (hj : 1 ≤ j)

theorem witness_V0 (hj : 1 ≤ j) : SN (gV0 C.m) (assign C.m X x j) = x :=
  SN_split _ _ _ _ _ _ hj (assign_gY _ _ _ _)

theorem witness_V1 (hj : 1 ≤ j) : SN (gV1 C.m) (assign C.m X x j) = x :=
  SN_split _ _ _ _ _ _ hj (assign_gZ _ _ _ _)

theorem witness_P (hj : 1 ≤ j) (c : Fin C.m) : SN (gP C.m c) (assign C.m X x j) = X c :=
  SN_split _ _ _ _ _ _ hj (assign_gP _ _ _ _ c)

include hx hX hR hj

/-- Every paired row vanishes at the physical assignment of an accepting assignment. -/
theorem witness_rows90 : ∀ R ∈ pairedRows90 C,
    R.val (x : ℤ) (fun i => (assign C.m X x j i : ℤ)) = 0 := by
  intro R hR'
  have hP : ∀ c, SN (gP C.m c) (assign C.m X x j) = X c :=
    fun c => SN_split _ _ _ _ _ _ hj (assign_gP _ _ _ _ c)
  have hQ : ∀ c, SN (gQ C.m c) (assign C.m X x j) = X c :=
    fun c => SN_split _ _ _ _ _ _ hj (assign_gQ _ _ _ _ c)
  have hRc : ∀ c, SN (gR C.m c) (assign C.m X x j) = X c :=
    fun c => SN_split _ _ _ _ _ _ hj (assign_gR _ _ _ _ c)
  have hV0 : SN (gV0 C.m) (assign C.m X x j) = x := witness_V0 hj
  have hU : SN (gU C.m) (assign C.m X x j) = x ^ 2 - 1 :=
    SN_split _ _ _ _ _ _ hj (assign_gU _ _ _ _)
  have hδ := assign_iδ C.m X x j
  have hδ' := assign_iδ' C.m X x j
  unfold pairedRows90 at hR'
  simp only [List.mem_append, copyRows, List.mem_flatMap, List.mem_finRange, true_and,
    List.mem_cons, List.not_mem_nil, or_false, List.mem_map, normRows90] at hR'
  rcases hR' with (⟨c, rfl | rfl⟩ | ⟨ρ, hρ, rfl⟩) | rfl | rfl | rfl
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
  · rw [copyRow_val, S_cast, S_cast, hP, hX, hV0]; ring
  · rw [deltaRow_val, hδ, hδ']; ring
  · rw [uRow90_val, S_cast90, S_cast90, S_cast90, hV0, hP, hX, hU, hδ, hδ']
    have : 1 ≤ x ^ 2 := Nat.one_le_pow _ _ hx
    push_cast [Nat.cast_sub this]
    ring

end Witness

end L90

end Jones1980
