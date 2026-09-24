import Diophantine.Paper1980.Compile90a
import Diophantine.Paper1980.Compile93b

/-!
# Compiling a gate circuit into a 90-operation layout

`Papers/1980/BINARY_PRODUCT_90_PROOF.md`, Section 2.  The physical
coordinates are those of the 93-operation compiler (`Compile93b.lean`): three
groups `P c, Q c, R c` per circuit coordinate, the groups `V₀, V₁` (the two
reserved helpers, in the slots of `Y, Z`), the group `u`, and the units
`δ, δ'`.  The rows, each with its helper group, are

1. the seeds `−x²` for `V₀` and `V₁` (helper: the seed's own group);
2. the reverses `2 x δ − 2 δ Vᵢ` (helper: the other group `V_{1−i}`);
3. the paired ordinary rows and their negations (helper `V₁`): the copy rows
   `Q c = P c`, `R c = P c`, the circuit rows, and the normalization rows
   `X² − V₀²` (`X = P_inp`), `δ'² − δ²`, `2 V₀ X − 2 δ δ' − 2 δ u`;
4. two unit rows `δ²`.

The padding group is `P_X = P_inp`.  Every row is valid with its helper
(`layoutOk`).
-/

namespace Jones1980

namespace L90

open Layout (Row)
open Iso (negRow S sqTerms crossTerms prodTerms dotTerms copyRow addRow mulRow zeroRow oneRow
  deltaRow unitRow RowStruct Disj Avoids nphys phys gP gQ gR gY gZ gU iδ iδ' phys_injective
  phys_disj phys_avoids_δ phys_avoids_δ' iδ_ne circRow copyRows circRow_struct negRow_struct
  copyRow_struct addRow_struct mulRow_struct zeroRow_struct oneRow_struct deltaRow_struct
  unitRow_struct)

/-! ### Rows avoiding a group -/

variable {m : ℕ}

/-- The group `P` avoids every coordinate of the squares and cross terms of `R`. -/
def AvoidsRow (R : Row m) (P : Fin 3 → Fin m) : Prop :=
  (∀ q ∈ R.sq, ∀ a, P a ≠ q.1) ∧ (∀ q ∈ R.cross, ∀ a, P a ≠ q.1 ∧ P a ≠ q.2.1)

theorem avoids_negRow {R : Row m} {P : Fin 3 → Fin m} (h : AvoidsRow R P) : AvoidsRow (negRow R) P := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · intro q hq a
    unfold negRow at hq
    simp only [List.mem_map] at hq
    obtain ⟨q', hq', rfl⟩ := hq
    exact h1 q' hq' a
  · intro q hq a
    unfold negRow at hq
    simp only [List.mem_map] at hq
    obtain ⟨q', hq', rfl⟩ := hq
    exact h2 q' hq' a

theorem avoids_copyRow {P g h : Fin 3 → Fin m} (hg : Disj P g) (hh : Disj P h) :
    AvoidsRow (copyRow g h) P := by
  simp [AvoidsRow, copyRow, sqTerms, crossTerms, hg _ _, hh _ _]

theorem avoids_addRow {P g h k : Fin 3 → Fin m} {d : Fin m} (hg : Disj P g) (hh : Disj P h)
    (hk : Disj P k) (hd : Avoids P d) : AvoidsRow (addRow g h k d) P := by
  simp [AvoidsRow, addRow, dotTerms, hg _ _, hh _ _, hk _ _, hd _]

theorem avoids_mulRow {P g h k : Fin 3 → Fin m} {d : Fin m} (hg : Disj P g) (hh : Disj P h)
    (hk : Disj P k) (hd : Avoids P d) : AvoidsRow (mulRow g h k d) P := by
  simp [AvoidsRow, mulRow, prodTerms, dotTerms, hg _ _, hh _ _, hk _ _, hd _]

theorem avoids_zeroRow {P g : Fin 3 → Fin m} {d : Fin m} (hg : Disj P g) (hd : Avoids P d) :
    AvoidsRow (zeroRow g d) P := by
  simp [AvoidsRow, zeroRow, dotTerms, hg _ _, hd _]

theorem avoids_oneRow {P g : Fin 3 → Fin m} {d d' : Fin m} (hg : Disj P g) (hd : Avoids P d)
    (hd' : Avoids P d') : AvoidsRow (oneRow g d d') P := by
  simp [AvoidsRow, oneRow, dotTerms, hg _ _, hd _, hd' _]

theorem avoids_deltaRow {P : Fin 3 → Fin m} {d d' : Fin m} (hd : Avoids P d) (hd' : Avoids P d') :
    AvoidsRow (deltaRow d d') P := by
  simp [AvoidsRow, deltaRow, hd _, hd' _]

theorem avoids_unitRow {P : Fin 3 → Fin m} {d : Fin m} (hd : Avoids P d) :
    AvoidsRow (unitRow d) P := by
  simp [AvoidsRow, unitRow, hd _]

theorem avoids_uRow90 {P g h u : Fin 3 → Fin m} {d d' : Fin m} (hg : Disj P g) (hh : Disj P h)
    (hu : Disj P u) (hd : Avoids P d) (hd' : Avoids P d') : AvoidsRow (uRow90 g h d d' u) P := by
  simp [AvoidsRow, uRow90, prodTerms, dotTerms, hg _ _, hh _ _, hu _ _, hd _, hd' _]

theorem avoids_revRow {P g : Fin 3 → Fin m} {d : Fin m} (hg : Disj P g) (hd : Avoids P d) :
    AvoidsRow (revRow d g) P := by
  simp [AvoidsRow, revRow, dotTerms, hg _ _, hd _]

theorem avoids_seedRow (P : Fin 3 → Fin m) : AvoidsRow (seedRow : Row m) P := by
  simp [AvoidsRow, seedRow]

/-- An ordinary row (no `x` terms) that is structurally valid and avoided by `P` is `RowOk`. -/
theorem rowOk_ordinary {R : Row m} {P : Fin 3 → Fin m} (hS : RowStruct R) (hxz : R.xz = [])
    (hxx : R.xx = 0) (hP : Function.Injective P) (hA : AvoidsRow R P) : RowOk R P :=
  rowOk_of_struct hS (by rw [hxz]; simp) (by rw [hxx]) hP hA.1 hA.2 (by rw [hxx]; intro h; omega)

theorem rowOk_negRow {R : Row m} {P : Fin 3 → Fin m} (hS : RowStruct R) (hxz : R.xz = [])
    (hxx : R.xx = 0) (hP : Function.Injective P) (hA : AvoidsRow R P) : RowOk (negRow R) P :=
  rowOk_ordinary (negRow_struct hS) (by simp [negRow, hxz]) (by simp [negRow, hxx]) hP
    (avoids_negRow hA)

theorem rowOk_seedRow {P : Fin 3 → Fin m} (hP : Function.Injective P) : RowOk (seedRow : Row m) P :=
  rowOk_of_struct seedRow_struct (by simp [seedRow]) (by simp [seedRow]) hP (by simp [seedRow])
    (by simp [seedRow]) (fun _ => by simp [seedRow])

theorem rowOk_revRow {P g : Fin 3 → Fin m} {d : Fin m} (hg : Function.Injective g)
    (hgd : Avoids g d) (hP : Function.Injective P) (hPg : Disj P g) (hPd : Avoids P d) :
    RowOk (revRow d g) P :=
  rowOk_of_struct (revRow_struct hg hgd) (by simp [revRow]) (by simp [revRow]) hP
    (avoids_revRow hPg hPd).1 (avoids_revRow hPg hPd).2 (by simp [revRow])

theorem rowOk_unitRow {P : Fin 3 → Fin m} {d : Fin m} (hP : Function.Injective P)
    (hPd : Avoids P d) : RowOk (unitRow d) P :=
  rowOk_ordinary (unitRow_struct d) (by simp [unitRow]) (by simp [unitRow]) hP
    (avoids_unitRow hPd)

/-! ### The layout of a circuit -/

section Circuit

variable (cm : ℕ)

/-- The helper groups: `V₀` and `V₁` occupy the slots of `Y` and `Z`. -/
def gV0 : Fin 3 → Fin (nphys cm) := gY cm
def gV1 : Fin 3 → Fin (nphys cm) := gZ cm

theorem gV0_eq : gV0 cm = phys cm (3 * cm) (by omega) := rfl
theorem gV1_eq : gV1 cm = phys cm (3 * cm + 1) (by omega) := rfl

/-- The normalization rows: `X² − V₀²`, `δ'² − δ²`, `2 V₀ X − 2 δ δ' − 2 δ u`. -/
def normRows90 (inp : Fin cm) : List (Row (nphys cm)) :=
  [copyRow (gP cm inp) (gV0 cm), deltaRow (iδ cm) (iδ' cm),
    uRow90 (gV0 cm) (gP cm inp) (iδ cm) (iδ' cm) (gU cm)]

/-- All paired rows of a circuit. -/
def pairedRows90 (C : Gates.Circuit) : List (Row (nphys C.m)) :=
  copyRows C.m ++ C.rows.map (circRow C.m) ++ normRows90 C.m C.inp

/-- A row with its helper group. -/
abbrev HRow (cm : ℕ) := Row (nphys cm) × (Fin 3 → Fin (nphys cm))

/-- The seed and reverse rows. -/
def headRows : List (HRow cm) :=
  [(seedRow, gV0 cm), (seedRow, gV1 cm), (revRow (iδ cm) (gV0 cm), gV1 cm),
    (revRow (iδ cm) (gV1 cm), gV0 cm)]

/-- The paired ordinary rows with their negations, helper `V₁`. -/
def l1 (C : Gates.Circuit) : List (HRow C.m) :=
  (pairedRows90 C).flatMap fun R => [(R, gV1 C.m), (negRow R, gV1 C.m)]

/-- The unit row with its (irrelevant) helper. -/
def unitPair : HRow cm := (unitRow (iδ cm), gV1 cm)

/-- All rows before the unit rows. -/
def preRows (C : Gates.Circuit) : List (HRow C.m) := headRows C.m ++ l1 C

/-- All rows. -/
def allRows (C : Gates.Circuit) : List (HRow C.m) := preRows C ++ [unitPair C.m, unitPair C.m]

/-- The number of rows. -/
def cs (C : Gates.Circuit) : ℕ := (allRows C).length

/-- The rows and helpers, indexed. -/
def crows (C : Gates.Circuit) (j : Fin (cs C)) : Row (nphys C.m) := ((allRows C)[(j : ℕ)]'j.isLt).1
def chel (C : Gates.Circuit) (j : Fin (cs C)) : Fin 3 → Fin (nphys C.m) := ((allRows C)[(j : ℕ)]'j.isLt).2

/-- The padding group `P_X = P_inp`. -/
def cPX (C : Gates.Circuit) : Finset (Fin (nphys C.m)) := Finset.univ.image (gP C.m C.inp)

theorem cs_eq (C : Gates.Circuit) : cs C = (preRows C).length + 2 := by
  unfold cs allRows; simp

theorem preRows_length (C : Gates.Circuit) : (preRows C).length = 4 + 2 * (pairedRows90 C).length := by
  unfold preRows headRows l1
  simp [List.length_flatMap, List.map_const', List.sum_replicate]
  ring

theorem six_le_cs (C : Gates.Circuit) : 6 ≤ cs C := by
  rw [cs_eq, preRows_length]; omega

/-! ### Membership facts -/

theorem mem_allRows_iff (C : Gates.Circuit) (p : HRow C.m) :
    p ∈ allRows C ↔ p ∈ headRows C.m ∨ p ∈ l1 C ∨ p = unitPair C.m := by
  unfold allRows preRows
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc, or_self]

theorem crows_mem (C : Gates.Circuit) (j : Fin (cs C)) : (crows C j, chel C j) ∈ allRows C := by
  unfold crows chel
  exact List.getElem_mem _

/-- The rows at or beyond `(preRows C).length` are the unit rows. -/
theorem allRows_getElem_unit (C : Gates.Circuit) (j : ℕ) (hj : j < cs C)
    (hpre : (preRows C).length ≤ j) : (allRows C)[j]'hj = unitPair C.m := by
  have hj2 : j < (preRows C).length + 2 := by rw [cs_eq] at hj; exact hj
  unfold allRows
  rw [List.getElem_append_right hpre]
  rcases Nat.lt_or_ge (j - (preRows C).length) 1 with h | h
  · have e : j - (preRows C).length = 0 := by omega
    simp [e]
  · have e : j - (preRows C).length = 1 := by omega
    simp [e]

theorem crows_unit (C : Gates.Circuit) (j : Fin (cs C)) (hj : (preRows C).length ≤ (j : ℕ)) :
    crows C j = unitRow (iδ C.m) ∧ chel C j = gV1 C.m := by
  unfold crows chel
  rw [allRows_getElem_unit C j j.isLt hj]
  exact ⟨rfl, rfl⟩

theorem allRows_getElem_pre (C : Gates.Circuit) (j : ℕ) (hj : j < cs C)
    (hpre : j < (preRows C).length) : (allRows C)[j]'hj = (preRows C)[j]'hpre := by
  unfold allRows
  rw [List.getElem_append_left hpre]

/-! ### Physical facts -/

theorem gP_lt (c : Fin cm) : 3 * (c : ℕ) < 3 * cm + 3 := by have := c.isLt; omega

theorem disj_V1_P (c : Fin cm) : Disj (gV1 cm) (gP cm c) := by
  exact phys_disj cm (by have := c.isLt; omega) (by have := c.isLt; omega) (by have := c.isLt; omega)
theorem disj_V1_Q (c : Fin cm) : Disj (gV1 cm) (gQ cm c) := by
  exact phys_disj cm (by have := c.isLt; omega) (by have := c.isLt; omega) (by have := c.isLt; omega)
theorem disj_V1_R (c : Fin cm) : Disj (gV1 cm) (gR cm c) := by
  exact phys_disj cm (by have := c.isLt; omega) (by have := c.isLt; omega) (by have := c.isLt; omega)
theorem disj_V1_V0 : Disj (gV1 cm) (gV0 cm) := by
  exact phys_disj cm (by omega) (by omega) (by omega)
theorem disj_V0_V1 : Disj (gV0 cm) (gV1 cm) := by
  exact phys_disj cm (by omega) (by omega) (by omega)
theorem disj_V1_U : Disj (gV1 cm) (gU cm) := by
  exact phys_disj cm (by omega) (by omega) (by omega)
theorem disj_V0_U : Disj (gV0 cm) (gU cm) := by
  exact phys_disj cm (by omega) (by omega) (by omega)
theorem disj_V0_P (c : Fin cm) : Disj (gV0 cm) (gP cm c) := by
  exact phys_disj cm (by have := c.isLt; omega) (by have := c.isLt; omega) (by have := c.isLt; omega)
theorem disj_P_U (c : Fin cm) : Disj (gP cm c) (gU cm) := by
  exact phys_disj cm (by have := c.isLt; omega) (by have := c.isLt; omega) (by have := c.isLt; omega)
theorem avoids_V1_δ : Avoids (gV1 cm) (iδ cm) := phys_avoids_δ cm _ (by omega)
theorem avoids_V1_δ' : Avoids (gV1 cm) (iδ' cm) := phys_avoids_δ' cm _ (by omega)
theorem avoids_V0_δ : Avoids (gV0 cm) (iδ cm) := phys_avoids_δ cm _ (by omega)
theorem avoids_V0_δ' : Avoids (gV0 cm) (iδ' cm) := phys_avoids_δ' cm _ (by omega)
theorem inj_V0 : Function.Injective (gV0 cm) := phys_injective cm _ (by omega)
theorem inj_V1 : Function.Injective (gV1 cm) := phys_injective cm _ (by omega)

/-- The helper `V₁` avoids every ordinary row. -/
theorem avoids_V1_paired (C : Gates.Circuit) : ∀ R ∈ pairedRows90 C, AvoidsRow R (gV1 C.m) := by
  intro R hR
  unfold pairedRows90 at hR
  simp only [List.mem_append, copyRows, List.mem_flatMap, List.mem_finRange, true_and,
    List.mem_cons, List.not_mem_nil, or_false, List.mem_map, normRows90] at hR
  rcases hR with (⟨c, rfl | rfl⟩ | ⟨ρ, _, rfl⟩) | rfl | rfl | rfl
  · exact avoids_copyRow (disj_V1_Q _ c) (disj_V1_P _ c)
  · exact avoids_copyRow (disj_V1_R _ c) (disj_V1_P _ c)
  · cases ρ with
    | add i j k => exact avoids_addRow (disj_V1_P _ i) (disj_V1_Q _ j) (disj_V1_R _ k) (avoids_V1_δ _)
    | mul i j k => exact avoids_mulRow (disj_V1_P _ i) (disj_V1_Q _ j) (disj_V1_R _ k) (avoids_V1_δ _)
    | eq i j => exact avoids_copyRow (disj_V1_P _ i) (disj_V1_Q _ j)
    | zero i => exact avoids_zeroRow (disj_V1_P _ i) (avoids_V1_δ _)
    | one i => exact avoids_oneRow (disj_V1_P _ i) (avoids_V1_δ _) (avoids_V1_δ' _)
  · exact avoids_copyRow (disj_V1_P _ _) (disj_V1_V0 _)
  · exact avoids_deltaRow (avoids_V1_δ _) (avoids_V1_δ' _)
  · exact avoids_uRow90 (disj_V1_V0 _) (disj_V1_P _ _) (disj_V1_U _) (avoids_V1_δ _) (avoids_V1_δ' _)

/-- Every ordinary row is structurally valid, with no `x` terms. -/
theorem paired_struct (C : Gates.Circuit) :
    ∀ R ∈ pairedRows90 C, RowStruct R ∧ R.xz = [] ∧ R.xx = 0 := by
  intro R hR
  unfold pairedRows90 at hR
  simp only [List.mem_append, copyRows, List.mem_flatMap, List.mem_finRange, true_and,
    List.mem_cons, List.not_mem_nil, or_false, List.mem_map, normRows90] at hR
  rcases hR with (⟨c, rfl | rfl⟩ | ⟨ρ, _, rfl⟩) | rfl | rfl | rfl
  · exact ⟨copyRow_struct (phys_injective _ _ _) (phys_injective _ _ _)
      (phys_disj _ _ _ (by omega)), rfl, rfl⟩
  · exact ⟨copyRow_struct (phys_injective _ _ _) (phys_injective _ _ _)
      (phys_disj _ _ _ (by omega)), rfl, rfl⟩
  · refine ⟨circRow_struct _ ρ, ?_⟩
    cases ρ <;> exact ⟨rfl, rfl⟩
  · exact ⟨copyRow_struct (phys_injective _ _ _) (inj_V0 _) (disj_V0_P _ _).symm, rfl, rfl⟩
  · exact ⟨deltaRow_struct (iδ_ne _), rfl, rfl⟩
  · refine ⟨uRow90_struct (inj_V0 _) (phys_injective _ _ _) (phys_injective _ _ _)
      (disj_V0_P _ _) (disj_V0_U _) (disj_P_U _ _) (avoids_V0_δ _) (avoids_V0_δ' _)
      (phys_avoids_δ _ _ _) (phys_avoids_δ' _ _ _) (phys_avoids_δ _ _ _) (phys_avoids_δ' _ _ _)
      (iδ_ne _), rfl, rfl⟩

/-- Every row of the layout is valid with its helper. -/
theorem allRows_ok (C : Gates.Circuit) : ∀ p ∈ allRows C, RowOk p.1 p.2 := by
  intro p hp
  rcases (mem_allRows_iff C p).1 hp with hh | hl | hu
  · unfold headRows at hh
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
    rcases hh with rfl | rfl | rfl | rfl
    · exact rowOk_seedRow (inj_V0 _)
    · exact rowOk_seedRow (inj_V1 _)
    · exact rowOk_revRow (inj_V0 _) (avoids_V0_δ _) (inj_V1 _) (disj_V1_V0 _) (avoids_V1_δ _)
    · exact rowOk_revRow (inj_V1 _) (avoids_V1_δ _) (inj_V0 _) (disj_V0_V1 _) (avoids_V0_δ _)
  · unfold l1 at hl
    simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hl
    obtain ⟨R, hR, rfl | rfl⟩ := hl
    · obtain ⟨hS, hxz, hxx⟩ := paired_struct C R hR
      exact rowOk_ordinary hS hxz hxx (inj_V1 _) (avoids_V1_paired C R hR)
    · obtain ⟨hS, hxz, hxx⟩ := paired_struct C R hR
      exact rowOk_negRow hS hxz hxx (inj_V1 _) (avoids_V1_paired C R hR)
  · subst hu
    exact rowOk_unitRow (inj_V1 _) (avoids_V1_δ _)

/-- The layout of a circuit is valid. -/
theorem layoutOk (C : Gates.Circuit) : LayoutOk (cs C) (crows C) (chel C) where
  three_le := by have := six_le_cs C; omega
  rows_ok := fun j => allRows_ok C _ (crows_mem C j)
  last := by
    intro j hj
    have hpre : (preRows C).length ≤ (j : ℕ) := by have := cs_eq C; omega
    obtain ⟨h1, _⟩ := crows_unit C j hpre
    rw [h1]
    refine ⟨?_, rfl⟩
    unfold negs terms unitRow
    simp

end Circuit

end L90

end Jones1980
