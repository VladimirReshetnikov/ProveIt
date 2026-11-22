import MoserWorm.UpperBound.Certificate.Extraction
import MoserWorm.UpperBound.Shape
import MoserWorm.UpperBound.Length

/-! Real support semantics and completed-prefix soundness of accepted rational leaves. -/

noncomputable section
namespace MoserWorm.UpperBound.Certificate
open Finset

@[simp] theorem qPlane_zero : qPlane (0 : Q2) = 0 := by
  apply Complex.ext <;> simp [qPlane]
@[simp] theorem qPlane_add (u v : Q2) : qPlane (u + v) = qPlane u + qPlane v := by
  apply Complex.ext <;> simp [qPlane]
@[simp] theorem qPlane_sub (u v : Q2) : qPlane (u - v) = qPlane u - qPlane v := by
  apply Complex.ext <;> simp [qPlane]
@[simp] theorem qPlane_smul (a : ℚ) (u : Q2) :
    qPlane (a • u) = (a : ℝ) • qPlane u := by
  apply Complex.ext <;> simp [qPlane, Prod.smul_def, smul_eq_mul]

private def qPlaneAdd : Q2 →+ Plane where
  toFun := qPlane
  map_zero' := qPlane_zero
  map_add' := qPlane_add

lemma qPlane_sum {ι : Type*} (s : Finset ι) (f : ι → Q2) :
    qPlane (∑ i ∈ s, f i) = ∑ i ∈ s, qPlane (f i) := map_sum qPlaneAdd f s

lemma qPlane_list_sum (l : List Q2) :
    qPlane l.sum = (l.map qPlane).sum := map_list_sum qPlaneAdd l

private lemma support_conic {C : Set Plane} (hC : IsCompact C) (hne : C.Nonempty)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {u w₁ w₂ : Plane}
    (hu : u = a • w₁ + b • w₂) :
    support C u ≤ a * support C w₁ + b * support C w₂ := by
  obtain ⟨x, hx, hxs⟩ := support_attained hC hne u
  rw [← hxs, hu, inner_add_left, real_inner_smul_left, real_inner_smul_left]
  exact add_le_add (mul_le_mul_of_nonneg_left (le_support hC hx _) ha)
    (mul_le_mul_of_nonneg_left (le_support hC hx _) hb)

lemma normalOf_one (T : LabelTables) : T.normalOf 1 = ((0 : ℚ), (-1 : ℚ)) := rfl
/-- The label-2 normal is `(0, 1)`. -/
lemma normalOf_two (T : LabelTables) : T.normalOf 2 = ((0 : ℚ), (1 : ℚ)) := rfl

/-- The right-table normals. -/
lemma normalOf_right (T : LabelTables) {i : ℕ} (h : i < T.kR) :
    T.normalOf (3 + i) = T.right.getD i (0,0) := by
  unfold LabelTables.normalOf
  simp only [beq_iff_eq]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  congr 1
  omega

/-- The left-table normals. -/
lemma normalOf_left (T : LabelTables) {j : ℕ} (_h : j < T.kL) :
    T.normalOf (3 + T.kR + j) = T.left.getD j (0,0) := by
  unfold LabelTables.normalOf
  simp only [beq_iff_eq]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  congr 1
  omega

/-- A successful `labOf` returns a valid label with the queried normal. -/
lemma labOf_spec {T : LabelTables} (hOK : labelsOK T = true) {u : Q2} {l : ℕ}
    (h : T.labOf u = some l) : l < T.nLab ∧ T.normalOf l = u := by
  obtain ⟨hsR, hsL, _, _, _, _⟩ := labelsOK_props T hOK
  unfold LabelTables.labOf at h
  by_cases h1 : u == ((0 : ℚ), (-1 : ℚ))
  · rw [if_pos h1] at h
    obtain rfl : (1 : ℕ) = l := Option.some.inj h
    rw [beq_iff_eq] at h1
    exact ⟨by unfold LabelTables.nLab; omega, by rw [normalOf_one, h1]⟩
  · rw [if_neg h1] at h
    by_cases h2 : u == ((0 : ℚ), (1 : ℚ))
    · rw [if_pos h2] at h
      obtain rfl : (2 : ℕ) = l := Option.some.inj h
      rw [beq_iff_eq] at h2
      exact ⟨by unfold LabelTables.nLab; omega, by rw [normalOf_two, h2]⟩
    · rw [if_neg h2] at h
      by_cases h3 : u.1 > 0
      · rw [if_pos h3, Option.map_eq_some_iff] at h
        obtain ⟨i, hfi, rfl⟩ := h
        rw [Array.findIdx?_eq_some_iff_getElem] at hfi
        obtain ⟨hilt, hbeq, _⟩ := hfi
        rw [beq_iff_eq] at hbeq
        have hik : i < T.kR := hsR ▸ hilt
        refine ⟨by unfold LabelTables.nLab; omega, ?_⟩
        rw [normalOf_right T hik, ← Array.getElem_eq_getD (h := hilt) (0,0), hbeq]
      · rw [if_neg h3, Option.map_eq_some_iff] at h
        obtain ⟨j, hfj, rfl⟩ := h
        rw [Array.findIdx?_eq_some_iff_getElem] at hfj
        obtain ⟨hjlt, hbeq, _⟩ := hfj
        rw [beq_iff_eq] at hbeq
        have hjk : j < T.kL := hsL ▸ hjlt
        refine ⟨by unfold LabelTables.nLab; omega, ?_⟩
        rw [normalOf_left T hjk,
          ← Array.getElem_eq_getD (h := hjlt) (0,0), hbeq]

/-! ### decompose specification -/

lemma decompose_cases {T : LabelTables} {named : Array Q2} {u : Q2}
    {parts : List (Q2 × ℚ)} (h : decompose T named u = some parts) :
    (parts = [(u, 1)]) ∨
    ∃ w1 w2 α β, parts = [(w1, α), (w2, β)] ∧ 0 ≤ α ∧ 0 ≤ β ∧
      α * w1.1 + β * w2.1 = u.1 ∧ α * w1.2 + β * w2.2 = u.2 := by
  unfold decompose at h
  split at h
  · exact Or.inl (Option.some.inj h).symm
  · dsimp only at h
    split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · split at h
        case isTrue hchk =>
          simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hchk
          exact Or.inr ⟨_, _, _, _, (Option.some.inj h).symm,
            hchk.1.1.1, hchk.1.1.2, hchk.1.2, hchk.2⟩
        case isFalse => exact absurd h (by simp)

/-- Destructuring `List.mapM` over `Option` at a cons. -/
lemma mapM_cons_some {α β : Type} (f : α → Option β) (a : α) (l : List α)
    {out : List β} (h : (a :: l).mapM f = some out) :
    ∃ b rest, f a = some b ∧ l.mapM f = some rest ∧ out = b :: rest := by
  rw [List.mapM_cons] at h
  cases hfa : f a with
  | none => rw [hfa] at h; simp at h
  | some b =>
    rw [hfa] at h
    cases hml : l.mapM f with
    | none => rw [hml] at h; simp at h
    | some rest =>
      rw [hml] at h
      refine ⟨b, rest, rfl, rfl, ?_⟩
      simpa using h.symm

lemma mapM_nil_some {α β : Type} (f : α → Option β) {out : List β}
    (h : ([] : List α).mapM f = some out) : out = [] := by
  simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
  exact h.symm

/-- The contact hypothesis: `z l` is a point of `C` attaining the support in
direction `normalOf l`, for every label `l < nLab`. -/
structure ContactData (T : LabelTables) (C : Set Plane) (z : ℕ → Plane) : Prop where
  mem : ∀ l, l < T.nLab → z l ∈ C
  supp : ∀ l, l < T.nLab →
    (inner ℝ (qPlane (T.normalOf l)) (z l) : ℝ) = support C (qPlane (T.normalOf l))

/-- The value of the coefficient list of a row at `z`. -/
def coeffVal (coeffs : List (ℕ × Q2)) (z : ℕ → Plane) : ℝ :=
  (coeffs.map (fun lc => (inner ℝ (qPlane lc.2) (z lc.1) : ℝ))).sum

/-- The affine value of a rational row at actual contacts. -/
def rowVal (row : RowData) (z : ℕ → Plane) : ℝ :=
  coeffVal row.coeffs z + (row.const : ℝ)

/-- The row value in terms of `coeffVal`. -/
lemma rowVal_coeffVal (row : RowData) (z : ℕ → Plane) :
    rowVal row z = coeffVal row.coeffs z + (row.const : ℝ) := rfl

/-- `coeffVal` is additive on appended coefficient lists. -/
lemma coeffVal_append (l1 l2 : List (ℕ × Q2)) (z : ℕ → Plane) :
    coeffVal (l1 ++ l2) z = coeffVal l1 z + coeffVal l2 z := by
  unfold coeffVal; rw [List.map_append, List.sum_append]

/-- `coeffVal` of a flattened list of coefficient lists. -/
lemma coeffVal_flatten (ls : List (List (ℕ × Q2))) (z : ℕ → Plane) :
    coeffVal ls.flatten z = (ls.map (fun l => coeffVal l z)).sum := by
  induction ls with
  | nil => simp [coeffVal]
  | cons a l ih => rw [List.flatten_cons, coeffVal_append, ih, List.map_cons,
      List.sum_cons]

/-- Value of the labelled pieces of a decomposition: an exact identity, by
induction over the decomposition list. -/
lemma coeffVal_labelled_eq {T : LabelTables} (hOK : labelsOK T = true)
    {C : Set Plane} {z : ℕ → Plane} (hz : ContactData T C z) (μ : ℚ) :
    ∀ (parts : List (Q2 × ℚ)) (out : List (ℕ × Q2)),
      parts.mapM (fun wc =>
        (T.labOf wc.1).map (fun l => (l, qsmul (μ * wc.2) wc.1))) = some out →
      coeffVal out z =
        (parts.map (fun wc => ((μ * wc.2 : ℚ) : ℝ) * support C (qPlane wc.1))).sum := by
  intro parts
  induction parts with
  | nil => intro out h; rw [mapM_nil_some _ h]; simp [coeffVal]
  | cons wc parts' ih =>
    intro out h
    obtain ⟨b, rest, hb, hrest, rfl⟩ := mapM_cons_some _ _ _ h
    rw [Option.map_eq_some_iff] at hb
    obtain ⟨l, hl, rfl⟩ := hb
    obtain ⟨hlt, hnorm⟩ := labOf_spec hOK hl
    have hsupp := hz.supp l hlt
    rw [hnorm] at hsupp
    unfold coeffVal
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons]
    have : (inner ℝ (qPlane (qsmul (μ * wc.2) wc.1)) (z l) : ℝ) =
        ((μ * wc.2 : ℚ) : ℝ) * support C (qPlane wc.1) := by
      rw [qsmul_eq, qPlane_smul, real_inner_smul_left, hsupp]
    rw [this]
    congr 1
    exact ih rest hrest

/-- Value of the pieces of one direction: for a real placement an equality
with `λᵢ · h_C(uᵢ)`, for a virtual placement a lower bound by it. -/
lemma coeffVal_rowEPieces_ge {T : LabelTables} (hOK : labelsOK T = true)
    {named : Array Q2} {C : Set Plane} (hC : IsCompact C) (hne : C.Nonempty)
    {z : ℕ → Plane} (hz : ContactData T C z)
    (p : PSpec) (r : Fin 2) (i : Fin 4)
    {pieces : List (ℕ × Q2)}
    (hp : rowEPieces T named p r i = some pieces) :
    (ray r i : ℝ) * support C (qPlane (specDirs p i)) ≤ coeffVal pieces z := by
  have hlam : 0 ≤ ray r i := MoserWorm.UpperBound.ray_nonneg r i
  have hlamR : (0:ℝ) ≤ (ray r i : ℝ) := by exact_mod_cast hlam
  unfold rowEPieces at hp
  -- the real branches: exact equality
  have real_case : ∀ (u : Q2), (T.labOf u).map
      (fun l => [(l, qsmul (ray r i) u)]) = some pieces →
      u = specDirs p i →
      (ray r i : ℝ) * support C (qPlane (specDirs p i)) = coeffVal pieces z := by
    intro u hu hueq
    rw [Option.map_eq_some_iff] at hu
    obtain ⟨l, hl, rfl⟩ := hu
    obtain ⟨hlt, hnorm⟩ := labOf_spec hOK hl
    have hsupp := hz.supp l hlt
    rw [hnorm] at hsupp
    unfold coeffVal
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero]
    rw [qsmul_eq, qPlane_smul, real_inner_smul_left, hsupp, hueq]
  cases p with
  | flush s fl mir =>
    simp only at hp
    exact le_of_eq (real_case _ hp rfl)
  | rot t mir =>
    simp only at hp
    exact le_of_eq (real_case _ hp rfl)
  | vrot t mir =>
    simp only at hp
    rw [Option.bind_eq_some_iff] at hp
    obtain ⟨parts, hdec, hmap⟩ := hp
    have heq := coeffVal_labelled_eq hOK hz (ray r i) parts pieces hmap
    rcases decompose_cases hdec with hone | ⟨w1, w2, α, β, rfl, hα, hβ, hx, hy⟩
    · subst hone
      rw [heq]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero, mul_one]
      exact le_rfl
    · rw [heq]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero]
      have hsub : support C (qPlane (specDirs (PSpec.vrot t mir) i)) ≤
          (α : ℝ) * support C (qPlane w1) + (β : ℝ) * support C (qPlane w2) := by
        refine support_conic hC hne (by exact_mod_cast hα)
          (by exact_mod_cast hβ) ?_
        have he : specDirs (PSpec.vrot t mir) i = α • w1 + β • w2 :=
          Prod.ext hx.symm hy.symm
        rw [he, qPlane_add, qPlane_smul, qPlane_smul]
      calc (ray r i : ℝ) * support C (qPlane (specDirs (PSpec.vrot t mir) i))
          ≤ (ray r i : ℝ) * ((α : ℝ) * support C (qPlane w1)
              + (β : ℝ) * support C (qPlane w2)) :=
            mul_le_mul_of_nonneg_left hsub hlamR
        _ = ((ray r i * α : ℚ) : ℝ) * support C (qPlane w1)
              + ((ray r i * β : ℚ) : ℝ) * support C (qPlane w2) := by
            push_cast; ring

/-- The mapped `rowEPieces` of a list of directions bound the corresponding
support-function sum from above. -/
private lemma sum_le_coeffVal_of_mapM {T : LabelTables} (hOK : labelsOK T = true)
    {named : Array Q2} {C : Set Plane} (hC : IsCompact C) (hne : C.Nonempty)
    {z : ℕ → Plane} (hz : ContactData T C z) (p : PSpec) (r : Fin 2) :
    ∀ (l : List (Fin 4)) (ps : List (List (ℕ × Q2))),
      l.mapM (rowEPieces T named p r) = some ps →
      (l.map (fun i => (ray r i : ℝ) * support C (qPlane (specDirs p i)))).sum
        ≤ (ps.map (fun q => coeffVal q z)).sum := by
  intro l
  induction l with
  | nil => intro ps hps; rw [mapM_nil_some _ hps]; simp
  | cons a l' ih =>
    intro ps hps
    obtain ⟨pa, rest, hpa, hrest, rfl⟩ := mapM_cons_some _ _ _ hps
    simp only [List.map_cons, List.sum_cons]
    have h1 := coeffVal_rowEPieces_ge hOK hC hne hz p r a hpa
    have h2 := ih rest hrest
    linarith

/-- **E-row lower bound.**  If `rowE` succeeds, its value at a contact
assignment is at least `Σ_{i ∈ supp r} λ_i h_C(u_i) - D_r`. -/
lemma rowVal_rowE_ge {T : LabelTables} (hOK : labelsOK T = true)
    {named : Array Q2} {C : Set Plane} (hC : IsCompact C) (hne : C.Nonempty)
    {z : ℕ → Plane} (hz : ContactData T C z)
    (p : PSpec) (r : Fin 2) {row : RowData}
    (hrow : rowE T named p r = some row) :
    (∑ i ∈ (raySupp r).toFinset,
        (ray r i : ℝ) * support C (qPlane (specDirs p i))) - (Dray r : ℝ)
      ≤ rowVal row z := by
  unfold rowE at hrow
  rw [Option.bind_eq_some_iff] at hrow
  obtain ⟨pieces, hpieces, hrow⟩ := hrow
  dsimp only at hrow
  split at hrow
  case isTrue =>
    obtain rfl := (Option.some.inj hrow).symm
    rw [rowVal_coeffVal]
    change _ ≤ coeffVal pieces.flatten z + ((-(Dray r) : ℚ) : ℝ)
    have hconst : ((-(Dray r) : ℚ) : ℝ) = -(Dray r : ℝ) := by push_cast; ring
    rw [hconst, ← sub_eq_add_neg]
    gcongr
    rw [coeffVal_flatten]
    have hkey := sum_le_coeffVal_of_mapM hOK hC hne hz p r (raySupp r) pieces hpieces
    have hsum : ∑ i ∈ (raySupp r).toFinset,
        (ray r i : ℝ) * support C (qPlane (specDirs p i)) =
        ((raySupp r).map
          (fun i => (ray r i : ℝ) * support C (qPlane (specDirs p i)))).sum := by
      fin_cases r <;>
        simp [raySupp, Finset.sum_insert, Finset.sum_singleton]
    rw [hsum]
    exact hkey
  case isFalse => exact absurd hrow (by simp)


lemma rowE_const {T : LabelTables} {named : Array Q2} {p : PSpec} {r : Fin 2}
    {row : RowData} (h : rowE T named p r = some row) :
    row.const = -(Dray r) := by
  unfold rowE at h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨pieces, _, h⟩ := h
  dsimp only at h
  split at h
  case isTrue => rw [← Option.some.inj h]
  case isFalse => exact absurd h (by simp)


lemma coeff_regroup (coeffs : List (ℕ × Q2)) (z : ℕ → Plane) (n : ℕ)
    (hl : ∀ lc ∈ coeffs, lc.1 < n) :
    (coeffs.map (fun lc => (inner ℝ (qPlane lc.2) (z lc.1) : ℝ))).sum
      = ∑ l ∈ Finset.range n, (inner ℝ (qPlane (coeffAt coeffs l)) (z l) : ℝ) := by
  induction coeffs with
  | nil => simp
  | cons lc rest ih =>
    rw [List.map_cons, List.sum_cons, ih (fun x hx => hl x (by simp [hx]))]
    have hstep : ∀ l, coeffAt (lc :: rest) l
        = (if lc.1 = l then lc.2 else 0) + coeffAt rest l :=
      fun l => coeffAt_cons lc rest l
    calc (inner ℝ (qPlane lc.2) (z lc.1) : ℝ)
          + ∑ l ∈ Finset.range n, (inner ℝ (qPlane (coeffAt rest l)) (z l) : ℝ)
        = (∑ l ∈ Finset.range n,
            (inner ℝ (qPlane (if lc.1 = l then lc.2 else 0)) (z l) : ℝ))
          + ∑ l ∈ Finset.range n, (inner ℝ (qPlane (coeffAt rest l)) (z l) : ℝ) := by
          congr 1
          rw [Finset.sum_eq_single lc.1]
          · simp
          · intro b _ hb
            rw [if_neg (fun h => hb h.symm)]
            simp
          · intro habs
            exact absurd (Finset.mem_range.mpr (hl lc (by simp))) habs
      _ = ∑ l ∈ Finset.range n, (inner ℝ (qPlane (coeffAt (lc :: rest) l)) (z l) : ℝ) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [hstep l, qPlane_add, inner_add_left]

lemma sum_rowVal_regroup (rws : List (RowData × ℚ)) (z : ℕ → Plane) (n : ℕ)
    (hl : ∀ rm ∈ rws, RowLabelsLt n rm.1) :
    (rws.map (fun rm => (rm.2 : ℝ) * rowVal rm.1 z)).sum
      = (∑ l ∈ Finset.range n, (inner ℝ (qPlane (Cfun rws l)) (z l) : ℝ))
        + ((rws.map (fun rm => rm.2 * rm.1.const)).sum : ℚ) := by
  induction rws with
  | nil => simp [rowVal, coeffVal]
  | cons rm rest ih =>
    rw [List.map_cons, List.sum_cons, ih (fun x hx => hl x (by simp [hx]))]
    have hrow : rowVal rm.1 z
        = (∑ l ∈ Finset.range n, (inner ℝ (qPlane (rowCoeff rm.1 l)) (z l) : ℝ))
          + (rm.1.const : ℝ) := by
      rw [rowVal, coeffVal, coeff_regroup _ _ _ (hl rm (by simp))]
      rfl
    rw [hrow]
    have hCfun : ∀ l, Cfun (rm :: rest) l = rm.2 • rowCoeff rm.1 l + Cfun rest l :=
      fun l => Cfun_cons rm rest l
    have : ∑ l ∈ Finset.range n, (inner ℝ (qPlane (Cfun (rm :: rest) l)) (z l) : ℝ)
        = ∑ l ∈ Finset.range n,
            ((rm.2 : ℝ) * inner ℝ (qPlane (rowCoeff rm.1 l)) (z l)
              + inner ℝ (qPlane (Cfun rest l)) (z l)) := by
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [hCfun l, qPlane_add, inner_add_left, qPlane_smul, real_inner_smul_left]
    rw [this, Finset.sum_add_distrib, ← Finset.mul_sum]
    simp only [List.map_cons, List.sum_cons]
    push_cast
    ring


/-- A successful escape row is strictly positive for its escaped support ray. -/
theorem rowE_strict {T : LabelTables} (hOK : labelsOK T = true)
    {C : Set Plane} (hC : IsCompact C) (hne : C.Nonempty)
    {z : ℕ → Plane} (hz : ContactData T C z)
    {p : PSpec} {r : Fin 2} {row : RowData}
    (hrow : rowE T (namedByAngle T) p r = some row)
    (hescape : (Dray r : ℝ) <
      ∑ i : Fin 4, (ray r i : ℝ) * support C (qPlane (specDirs p i))) :
    0 < rowVal row z := by
  have hb := rowVal_rowE_ge hOK hC hne hz p r hrow
  have he : (∑ i ∈ (raySupp r).toFinset,
        (ray r i : ℝ) * support C (qPlane (specDirs p i))) =
      ∑ i : Fin 4, (ray r i : ℝ) * support C (qPlane (specDirs p i)) := by
    fin_cases r <;> simp [raySupp, ray, rayA, rayB, Fin.sum_univ_succ]
  rw [he] at hb
  linarith

private theorem rowS_nonneg {T : LabelTables} {C : Set Plane} (hC : IsCompact C)
    {z : ℕ → Plane} (hz : ContactData T C z) {d P : ℕ}
    (hd : d < T.nLab) (hP : P < T.nLab) : 0 ≤ rowVal (rowS T d P) z := by
  have he : qPlane (-(T.normalOf d).1, -(T.normalOf d).2) =
      -qPlane (T.normalOf d) := by apply Complex.ext <;> simp [qPlane]
  have h := le_support hC (hz.mem P hP) (qPlane (T.normalOf d))
  rw [← hz.supp d hd] at h
  simpa only [rowVal, coeffVal, rowS, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero, Rat.cast_zero, he, inner_neg_left,
    ← sub_eq_add_neg] using sub_nonneg.mpr h

private theorem rowN_nonneg {z : ℕ → Plane} (h : (z 0).re ≤ (z 1).re) :
    0 ≤ rowVal rowN z := by
  simpa [rowVal, coeffVal, rowN, inner_plane, qPlane] using sub_nonneg.mpr h

/-- Actual contact semantics for every kind of row referenced by a leaf. -/
theorem allowedRow_real (c : Cert) (T : LabelTables) (hOK : labelsOK T = true)
    (assign : List (ℕ × Fin 2))
    (hbnd : ∀ mr ∈ assign, mr.1 < c.specs.size)
    {C : Set Plane} (hC : IsCompact C) (hne : C.Nonempty)
    {z : ℕ → Plane} (hz : ContactData T C z) (hfloor : (z 0).re ≤ (z 1).re)
    (hescape : ∀ mr ∈ assign, ∀ hm : mr.1 < c.specs.size,
      (Dray mr.2 : ℝ) < ∑ i : Fin 4, (ray mr.2 i : ℝ) *
        support C (qPlane (specDirs (c.specs[mr.1]'hm) i)))
    {row : RowData}
    (hrow : AllowedRow ⟨T, eRowsArr c T (namedByAngle T), c.target⟩ assign row) :
    RowLabelsLt T.nLab row ∧ 0 ≤ rowVal row z ∧
      (row.const < 0 → 0 < rowVal row z) := by
  cases hrow with
  | s d P hd hP hne =>
    refine ⟨?_, rowS_nonneg hC hz hd hP, ?_⟩
    · intro lc hlc
      simp only [rowS, List.mem_cons, List.not_mem_nil, or_false] at hlc
      rcases hlc with rfl | rfl <;> assumption
    · simp [rowS]
  | n =>
    refine ⟨?_, rowN_nonneg hfloor, ?_⟩
    · intro lc hlc
      have hn := nLab_ge_three T
      simp only [rowN, List.mem_cons, List.not_mem_nil, or_false] at hlc
      rcases hlc with rfl | rfl <;> simp only <;> omega
    · simp [rowN]
  | e m r row hmem he =>
    have hm := hbnd (m, r) hmem
    change (eRowsArr c T (namedByAngle T)).getD (2*m+r.val) none = some row at he
    rw [eRowsArr_getD c T (namedByAngle T) m r hm] at he
    have hs := rowE_strict hOK hC hne hz he (hescape (m,r) hmem hm)
    obtain ⟨hr, hl, _⟩ := labelsOK_props T hOK
    exact ⟨rowE_labels T _ _ _ row he hr hl, hs.le, fun _ => hs⟩

private theorem weighted_rowVal_pos (rws : List (RowData × ℚ)) (z : ℕ → Plane)
    (h : ∀ rm ∈ rws, 0 ≤ rm.2 ∧ 0 ≤ rowVal rm.1 z ∧
      (rm.1.const < 0 → 0 < rowVal rm.1 z)) (hB : 0 < lbOf rws) :
    0 < (rws.map (fun rm => (rm.2 : ℝ) * rowVal rm.1 z)).sum := by
  induction rws with
  | nil => simp at hB
  | cons rm rest ih =>
    have ht := h rm (by simp)
    have hr := fun x hx => h x (List.mem_cons_of_mem rm hx)
    have hμ : (0 : ℝ) ≤ (rm.2 : ℝ) := by exact_mod_cast ht.1
    rw [List.map_cons, List.sum_cons]
    by_cases hb : 0 < lbOf rest
    · exact add_pos_of_nonneg_of_pos (mul_nonneg hμ ht.2.1) (ih hr hb)
    · have hm : 0 < rm.2 * (-rm.1.const) := by
        rw [lbOf_cons] at hB
        linarith
      have hc : rm.1.const < 0 := neg_pos.mp (pos_of_mul_pos_right hm ht.1)
      have hmp : (0 : ℝ) < (rm.2 : ℝ) := by
        exact_mod_cast pos_of_mul_pos_left hm (neg_nonneg.mpr hc.le)
      apply add_pos_of_pos_of_nonneg (mul_pos hmp (ht.2.2 hc))
      apply List.sum_nonneg
      intro x hx
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
      exact mul_nonneg (by exact_mod_cast (hr a ha).1) (hr a ha).2.1

/-- Nonnegative exact checker multipliers and strict escape rows force the
actual contact functional above the normalized target. -/
theorem contact_functional_gt_one (rws : List (RowData × ℚ)) (T : LabelTables)
    (z : ℕ → Plane)
    (h : ∀ rm ∈ rws, 0 ≤ rm.2 ∧ RowLabelsLt T.nLab rm.1 ∧
      0 ≤ rowVal rm.1 z ∧ (rm.1.const < 0 → 0 < rowVal rm.1 z))
    (hB : 1 ≤ lbOf rws) :
    1 < ∑ l ∈ range T.nLab, inner ℝ (qPlane (Cfun rws l)) (z l) := by
  have hp := weighted_rowVal_pos rws z
    (fun rm hm => ⟨(h rm hm).1, (h rm hm).2.2⟩) (lt_of_lt_of_le (by norm_num) hB)
  rw [sum_rowVal_regroup rws z T.nLab (fun rm hm => (h rm hm).2.1)] at hp
  have hb : (1 : ℝ) ≤ (lbOf rws : ℝ) := by exact_mod_cast hB
  simp only [lbOf, Rat.cast_neg] at hb
  linarith

/-- Consecutive labels starting at `offset`, with half-open local indices. -/
def labelBlock (offset a b : ℕ) : Finset ℕ := (Ico a b).image (offset + ·)

/-- The four completed-prefix families, in checker label order. -/
def PrefixFamily (T : LabelTables) (p q : ℕ) (S : Finset ℕ) : Prop :=
  (∃ a b, q ≤ a ∧ a ≤ b ∧ b ≤ T.kL ∧ S = labelBlock (3 + T.kR) a b) ∨
  (∃ j, j ≤ q ∧ S = insert 0 (labelBlock (3 + T.kR) j T.kL)) ∨
  (∃ j, p ≤ j ∧ j ≤ T.kR ∧ S = insert 1 (labelBlock 3 0 j)) ∨
  (∃ a b, a ≤ b ∧ b ≤ p ∧ S = labelBlock 3 a b)

/-- Label sets completed before an edge, including the empty and full sets.
A proper prefix or its complement must have one of the four explicit shapes. -/
def ContactPrefixes (T : LabelTables) (p q : ℕ) (rank : ℕ → ℕ) (m : ℕ) : Prop :=
  ∀ j < m, let S := (range T.nLab).filter (fun l => rank l ≤ j)
    S = ∅ ∨ S = range T.nLab ∨ PrefixFamily T p q S ∨
      PrefixFamily T p q (range T.nLab \ S)

private lemma psum_eq_sum (g : ℕ → Q2) (n : ℕ) :
    psum g n = ∑ i ∈ range n, g i := by
  induction n with
  | zero => simp
  | succ n ih => rw [psum_succ, sum_range_succ, ih]

private lemma sum_labelBlock (g : ℕ → Q2) (o a b : ℕ) (hab : a ≤ b) :
    (∑ l ∈ labelBlock o a b, g l) =
      psum (fun i => g (o + i)) b - psum (fun i => g (o + i)) a := by
  rw [labelBlock, sum_image]
  · rw [sum_Ico_eq_sub _ hab, psum_eq_sum, psum_eq_sum]
  · intro i _ j _ h; exact Nat.add_left_cancel h

private lemma anchor_not_mem (o a b l : ℕ) (h : l < o) :
    l ∉ labelBlock o a b := by
  simp only [labelBlock, mem_image, mem_Ico]
  rintro ⟨i, _, hi⟩
  omega

/-- The four rational family tests imply unit real force sums for each
concrete family, at any split contained in the checked rectangle. -/
theorem family_force_bound (T : LabelTables) (g : ℕ → Q2)
    (rect : ℕ × ℕ × ℕ × ℕ) (p q : ℕ)
    (hp : rect.1 ≤ p ∧ p ≤ rect.2.1) (hq : rect.2.2.1 ≤ q ∧ q ≤ rect.2.2.2)
    (hpr : rect.2.1 ≤ T.kR) (hqr : rect.2.2.2 ≤ T.kL)
    (hi : ∀ a b, rect.2.2.1 ≤ a → a ≤ b → b < T.kL →
      qnorm2 (psum (fun i => g (3 + T.kR + i)) (b + 1) -
        psum (fun i => g (3 + T.kR + i)) a) ≤ 1)
    (hii : ∀ j, j ≤ min rect.2.2.2 T.kL →
      qnorm2 (psum (fun i => g (3 + T.kR + i)) T.kL -
        psum (fun i => g (3 + T.kR + i)) j + g 0) ≤ 1)
    (hiii : ∀ j, rect.1 ≤ j → j ≤ T.kR →
      qnorm2 (g 1 + psum (fun i => g (3 + i)) j) ≤ 1)
    (hiv : ∀ a b, a ≤ b → b ≤ rect.2.1 → rect.2.1 ≤ T.kR →
      qnorm2 (psum (fun i => g (3 + i)) b - psum (fun i => g (3 + i)) a) ≤ 1)
    {S : Finset ℕ} (hS : PrefixFamily T p q S) :
    ‖∑ l ∈ S, qPlane (g l)‖ ≤ 1 := by
  rw [← qPlane_sum]
  apply qPlane_norm_le_one
  rcases hS with ⟨a,b,hqa,hab,hb,rfl⟩ | ⟨j,hj,rfl⟩ |
    ⟨j,hpj,hj,rfl⟩ | ⟨a,b,hab,hbp,rfl⟩
  · rw [sum_labelBlock g _ _ _ hab]
    by_cases he : a = b
    · subst b; simp [qnorm2]
    · have h := hi a (b-1) (by omega) (by omega) (by omega)
      rwa [show b-1+1=b by omega] at h
  · rw [sum_insert (anchor_not_mem _ _ _ _ (by omega)),
      sum_labelBlock g _ _ _ (by omega), add_comm]
    exact hii j (by omega)
  · rw [sum_insert (anchor_not_mem _ _ _ _ (by omega)),
      sum_labelBlock g _ _ _ (by omega), psum_zero, sub_zero]
    exact hiii j (by omega) hj
  · rw [sum_labelBlock g _ _ _ hab]
    exact hiv a b hab (by omega) hpr

private lemma prefixForce_eq (T : LabelTables) (g : ℕ → Q2) (rank : ℕ → ℕ) (j : ℕ) :
    prefixForce (fun l : Fin T.nLab => qPlane (g l)) (fun l => rank l) j =
      ∑ l ∈ (range T.nLab).filter (fun l => rank l ≤ j), qPlane (g l) := by
  simp only [prefixForce, sum_filter]
  exact Fin.sum_univ_eq_sum_range (fun l => if rank l ≤ j then qPlane (g l) else 0) _

/-- Concrete prefix shapes transfer rational family tests to the visiting-path
length estimate. Coincident contacts and unlabelled vertices are allowed. -/
theorem prefix_functional_le_length (T : LabelTables) (g : ℕ → Q2)
    (rank : ℕ → ℕ) (v : ℕ → Plane) (m p q : ℕ)
    (hrank : ∀ l < T.nLab, rank l ≤ m)
    (hzero : ((List.range T.nLab).map g).sum = 0)
    (hprefix : ContactPrefixes T p q rank m)
    (hfamily : ∀ S, PrefixFamily T p q S → ‖∑ l ∈ S, qPlane (g l)‖ ≤ 1) :
    (∑ l ∈ range T.nLab, inner ℝ (qPlane (g l)) (v (rank l))) ≤
      ∑ j ∈ range m, dist (v j) (v (j+1)) := by
  have hz : (∑ l ∈ range T.nLab, qPlane (g l)) = 0 := by
    rw [← qPlane_sum, ← psum_eq_sum]
    change qPlane (((List.range T.nLab).map g).sum) = 0
    rw [hzero, qPlane_zero]
  have hzfin : (∑ l : Fin T.nLab, qPlane (g l)) = 0 := by
    rw [Fin.sum_univ_eq_sum_range (fun l => qPlane (g l)) T.nLab]; exact hz
  rw [← Fin.sum_univ_eq_sum_range
    (fun l => inner ℝ (qPlane (g l)) (v (rank l))) T.nLab]
  apply completed_prefix_length_bound (fun l : Fin T.nLab => qPlane (g l))
    (fun l => rank l) v m (fun l => hrank l l.isLt) hzfin
  intro j hj
  rw [prefixForce_eq]
  rcases hprefix j hj with he | he | he | he
  · rw [he]; simp
  · rw [he, hz]; simp
  · exact hfamily _ he
  · have hc := hfamily _ he
    have hsum := sum_sdiff_eq_sub (f := fun l => qPlane (g l))
      (filter_subset (fun l => rank l ≤ j) (range T.nLab))
    rw [hsum, hz, zero_sub, norm_neg] at hc
    exact hc

/-- Geometric input in checker label order. All coefficient inequalities are
proved from checker acceptance, rather than stored in this model. -/
structure ContactModel (T : LabelTables) (C : Set Plane) (v : ℕ → Plane) (m : ℕ) where
  rank : ℕ → ℕ
  p : ℕ
  q : ℕ
  rank_le : ∀ l < T.nLab, rank l ≤ m
  contacts : ContactData T C (fun l => v (rank l))
  floor_order : (v (rank 0)).re ≤ (v (rank 1)).re
  p_le : p ≤ T.kR
  q_le : q ≤ T.kL
  prefixes : ContactPrefixes T p q rank m

/-- An accepted leaf contradicts an actual contact path of length at most one,
when its assigned escape alternatives hold. -/
theorem checkLeaf_contact_contradiction (c : Cert) (T : LabelTables)
    (hOK : labelsOK T = true) (htarget : c.target = 1)
    (assign : List (ℕ × Fin 2)) (hbnd : ∀ mr ∈ assign, mr.1 < c.specs.size)
    (rect : ℕ × ℕ × ℕ × ℕ) (mu : List (RowKey × ℚ))
    (hcheck : checkLeaf ⟨T, eRowsArr c T (namedByAngle T), c.target⟩ assign rect mu = true)
    {C : Set Plane} (hC : IsCompact C) (hne : C.Nonempty)
    (v : ℕ → Plane) (m : ℕ) (model : ContactModel T C v m)
    (hp : rect.1 ≤ model.p ∧ model.p ≤ rect.2.1)
    (hq : rect.2.2.1 ≤ model.q ∧ model.q ≤ rect.2.2.2)
    (hpr : rect.2.1 ≤ T.kR) (hqr : rect.2.2.2 ≤ T.kL)
    (hescape : ∀ mr ∈ assign, ∀ hm : mr.1 < c.specs.size,
      (Dray mr.2 : ℝ) < ∑ i : Fin 4, (ray mr.2 i : ℝ) *
        support C (qPlane (specDirs (c.specs[mr.1]'hm) i)))
    (hlen : (∑ j ∈ range m, dist (v j) (v (j+1))) ≤ 1) : False := by
  obtain ⟨rws, hrows, hzero, hB, hi, hii, hiii, hiv⟩ :=
    checkLeaf_extract _ assign rect mu hcheck
  have hr : ∀ rm ∈ rws, 0 ≤ rm.2 ∧ RowLabelsLt T.nLab rm.1 ∧
      0 ≤ rowVal rm.1 (fun l => v (model.rank l)) ∧
      (rm.1.const < 0 → 0 < rowVal rm.1 (fun l => v (model.rank l))) := by
    intro rm hm
    exact ⟨(hrows rm hm).1, allowedRow_real c T hOK assign hbnd hC hne
      model.contacts model.floor_order hescape (hrows rm hm).2⟩
  have hgt := contact_functional_gt_one rws T (fun l => v (model.rank l)) hr
    (by simpa only [htarget] using hB)
  have hle := prefix_functional_le_length T (Cfun rws) model.rank v m model.p model.q
    model.rank_le hzero model.prefixes
    (fun S hS => family_force_bound T (Cfun rws) rect model.p model.q
      hp hq hpr hqr hi hii hiii hiv hS)
  linarith

/-- Accepted normalized certificates cover every contact model whose visiting
path has length at most one. Escape choices and a compatible accepted leaf
are obtained from the actual uncovered compact set and the checked tree. -/
theorem checkCert_contact_cover (c : Cert) (hc : checkCert c = true)
    (T : LabelTables) (hT : buildLabels c.specs.toList = some T)
    {C : Set Plane} (hC : IsCompact C) (hne : C.Nonempty)
    (v : ℕ → Plane) (m : ℕ) (model : ContactModel T C v m)
    (hlen : (∑ j ∈ range m, dist (v j) (v (j + 1))) ≤ 1) :
    ∃ g : Plane ≃ᵢ Plane, g '' C ⊆ Kquad := by
  classical
  by_contra hmiss
  obtain ⟨_, _, hOK, _, htree⟩ := checkCert_extract c hc T hT
  have hortho : ∀ j (hj : j < c.specs.size), isOrtho (specMap (c.specs[j]'hj)) = true := by
    have hall : c.specs.all (fun p => isOrtho (specMap p)) = true := by
      unfold checkCert at hc
      simp only [Bool.and_eq_true] at hc
      tauto
    exact Array.all_eq_true.mp hall
  have hex : ∀ j, ∃ r : Fin 2, ∀ hj : j < c.specs.size,
      (Dray r : ℝ) < ∑ i : Fin 4, (ray r i : ℝ) *
        support C (qPlane (specDirs (c.specs[j]'hj) i)) := by
    intro j
    by_cases hj : j < c.specs.size
    · obtain ⟨r, hr⟩ := Kquad_escape_matrix hC hne hmiss _ (hortho j hj)
      exact ⟨r, fun _ => hr⟩
    · exact ⟨0, fun h => (hj h).elim⟩
  choose β hβ using hex
  obtain ⟨assign, rect, mu, hassign, hbnd, hp, hq, hrect, hleaf⟩ :=
    checkTree_leaf_extract _ 1000 c.tree [] (0, T.kR, 0, T.kL) htree β
      (by simp) (by simp) model.p model.q ⟨Nat.zero_le _, model.p_le⟩
        ⟨Nat.zero_le _, model.q_le⟩
  have hspec : ∀ mr ∈ assign, mr.1 < c.specs.size := by
    intro mr hmr
    have hb := hbnd mr hmr
    change 2 * mr.1 + 1 < (eRowsArr c T (namedByAngle T)).size at hb
    rw [eRowsArr, Array.size_ofFn] at hb
    omega
  apply checkLeaf_contact_contradiction c T hOK (checkCert_target c hc) assign hspec
    rect mu hleaf hC hne v m model hp hq hrect.2.1 hrect.2.2.2 _ hlen
  intro mr hmr hm
  simpa only [hassign mr hmr] using hβ mr.1 hm

end MoserWorm.UpperBound.Certificate
