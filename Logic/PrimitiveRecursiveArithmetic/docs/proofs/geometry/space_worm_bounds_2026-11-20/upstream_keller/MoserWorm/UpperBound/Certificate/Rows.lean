import MoserWorm.UpperBound.Certificate.Checker
import Mathlib.Algebra.Module.Prod
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

namespace MoserWorm.UpperBound.Certificate

/-! ### Q2 algebra -/

@[simp] lemma qadd_eq (u v : Q2) : qadd u v = u + v := rfl
@[simp] lemma qsub_eq (u v : Q2) : qsub u v = u - v := rfl
@[simp] lemma qsmul_eq (c : ℚ) (u : Q2) : qsmul c u = c • u := by
  cases u; simp [qsmul, Prod.smul_def, smul_eq_mul]

lemma qnorm2_eq (u : Q2) : qnorm2 u = u.1 * u.1 + u.2 * u.2 := rfl

lemma nLab_ge_three (T : LabelTables) : 3 ≤ T.nLab := by
  simp only [LabelTables.nLab]; omega

/-! ### Coefficient-of-label and functional forces -/

/-- Total coefficient of label `l` in a coefficient list. -/
def coeffAt (coeffs : List (ℕ × Q2)) (l : ℕ) : Q2 :=
  ((coeffs.filter (fun lc => lc.1 = l)).map (·.2)).sum

@[simp] lemma coeffAt_nil (l : ℕ) : coeffAt [] l = 0 := rfl

lemma coeffAt_cons (lc : ℕ × Q2) (rest : List (ℕ × Q2)) (l : ℕ) :
    coeffAt (lc :: rest) l =
      (if lc.1 = l then lc.2 else 0) + coeffAt rest l := by
  by_cases h : lc.1 = l <;> simp [coeffAt, h]

/-- Total coefficient of label `l` in a row. -/
def rowCoeff (row : RowData) (l : ℕ) : Q2 := coeffAt row.coeffs l

/-- All coefficient labels of a row are below `n`. -/
def RowLabelsLt (n : ℕ) (row : RowData) : Prop :=
  ∀ lc ∈ row.coeffs, lc.1 < n

/-- Functional force of a list of (row, multiplier) pairs at label `l`. -/
def Cfun (rws : List (RowData × ℚ)) (l : ℕ) : Q2 :=
  (rws.map (fun rm => rm.2 • rowCoeff rm.1 l)).sum

@[simp] lemma Cfun_nil (l : ℕ) : Cfun [] l = 0 := rfl

@[simp] lemma Cfun_cons (rm : RowData × ℚ) (rws : List (RowData × ℚ)) (l : ℕ) :
    Cfun (rm :: rws) l = rm.2 • rowCoeff rm.1 l + Cfun rws l := rfl

/-- The negated total constant (the raw lower bound). -/
def lbOf (rws : List (RowData × ℚ)) : ℚ :=
  - (rws.map (fun rm => rm.2 * rm.1.const)).sum

@[simp] lemma lbOf_nil : lbOf [] = 0 := by simp [lbOf]

@[simp] lemma lbOf_cons (rm : RowData × ℚ) (rws : List (RowData × ℚ)) :
    lbOf (rm :: rws) = lbOf rws - rm.2 * rm.1.const := by
  simp [lbOf]; ring

/-! ### Rows allowed at a leaf -/

/-- The rows a multiplier may reference at a leaf with path assignment
`assign`. -/
inductive AllowedRow (ctx : Ctx) (assign : List (ℕ × Fin 2)) : RowData → Prop
  | s (d P : ℕ) (hd : d < ctx.T.nLab) (hP : P < ctx.T.nLab) (hne : d ≠ P) :
      AllowedRow ctx assign (rowS ctx.T d P)
  | n : AllowedRow ctx assign rowN
  | e (m : ℕ) (r : Fin 2) (row : RowData) (hmem : (m, r) ∈ assign)
      (h : ctx.eRows.getD (2 * m + r.val) none = some row) :
      AllowedRow ctx assign row

/-! ### The array/functional bridge for the mu-fold -/

/-- Apply a coefficient list to the force array with multiplier `m`. -/
def applyCoeffs (C : Array Q2) (m : ℚ) (coeffs : List (ℕ × Q2)) : Array Q2 :=
  coeffs.foldl (fun C lc => C.modify lc.1 (fun c => qadd c (qsmul m lc.2))) C

@[simp] lemma applyCoeffs_nil (C : Array Q2) (m : ℚ) :
    applyCoeffs C m [] = C := rfl

lemma applyCoeffs_cons (C : Array Q2) (m : ℚ) (lc : ℕ × Q2)
    (rest : List (ℕ × Q2)) :
    applyCoeffs C m (lc :: rest) =
      applyCoeffs (C.modify lc.1 (fun c => qadd c (qsmul m lc.2))) m rest := rfl

@[simp] lemma applyCoeffs_size (C : Array Q2) (m : ℚ) (coeffs : List (ℕ × Q2)) :
    (applyCoeffs C m coeffs).size = C.size := by
  induction coeffs generalizing C with
  | nil => rfl
  | cons lc rest ih => rw [applyCoeffs_cons, ih, Array.size_modify]

lemma applyCoeffs_getD (C : Array Q2) (m : ℚ) (coeffs : List (ℕ × Q2))
    (l : ℕ) (hl : l < C.size) :
    (applyCoeffs C m coeffs).getD l ((0 : ℚ), (0 : ℚ))
      = C.getD l ((0 : ℚ), (0 : ℚ)) + m • coeffAt coeffs l := by
  induction coeffs generalizing C with
  | nil => simp
  | cons lc rest ih =>
    rw [applyCoeffs_cons, ih _ (by rwa [Array.size_modify]), coeffAt_cons]
    have hgd : ∀ (D : Array Q2) (j : ℕ) (hj : j < D.size),
        D.getD j ((0 : ℚ), (0 : ℚ)) = D[j] := fun D j hj => by
      simp [Array.getD, hj]
    by_cases h : lc.1 = l
    · subst h
      rw [hgd _ _ (by rwa [Array.size_modify]), hgd _ _ hl]
      simp [Array.getElem_modify_self, smul_add]
      abel
    · have h2 : (C.modify lc.1 (fun c => qadd c (qsmul m lc.2))).getD l ((0 : ℚ), (0 : ℚ))
          = C.getD l ((0 : ℚ), (0 : ℚ)) := by
        by_cases hls : l < C.size
        · rw [hgd _ _ (by rwa [Array.size_modify]), hgd _ _ hls]
          simp [Array.getElem_modify_of_ne h]
        · simp [Array.getD, Array.size_modify, hls]
      rw [h2]
      simp [h]

/-- The mu-fold as a pure `foldlM`. -/
def muFold (ctx : Ctx) (assign : List (ℕ × Fin 2))
    (mu : List (RowKey × ℚ)) (init : Array Q2 × ℚ) :
    Option (Array Q2 × ℚ) :=
  mu.foldlM (fun s kv => applyRow ctx assign s.1 s.2 kv) init

/-- The pure tail of `checkLeaf` after the mu loop. -/
def checkLeafTail (ctx : Ctx) (rect : ℕ × ℕ × ℕ × ℕ)
    (C : Array Q2) (LB : ℚ) : Bool :=
  if C.foldl qadd (0, 0) != ((0 : ℚ), (0 : ℚ)) then false
  else
    let maxNorm2 := familyMaxNorm2 ctx.T C rect.1 rect.2.1 rect.2.2.1 rect.2.2.2
    decide (maxNorm2 ≤ 1) && decide (LB ≥ ctx.target)

/-- `checkLeaf` from an arbitrary initial state. -/
def checkLeafGen (ctx : Ctx) (assign : List (ℕ × Fin 2))
    (rect : ℕ × ℕ × ℕ × ℕ) (mu : List (RowKey × ℚ))
    (C0 : Array Q2) (LB0 : ℚ) : Bool := Id.run do
  let mut C := C0
  let mut LB := LB0
  for kv in mu do
    match applyRow ctx assign C LB kv with
    | none => return false
    | some (C', LB') => C := C'; LB := LB'
  let s := C.foldl qadd (0, 0)
  if s != ((0 : ℚ), (0 : ℚ)) then return false
  let (pLo, pHi, qLo, qHi) := rect
  let maxNorm2 := familyMaxNorm2 ctx.T C pLo pHi qLo qHi
  return maxNorm2 ≤ 1 && LB ≥ ctx.target

lemma checkLeaf_eq_gen (ctx : Ctx) (assign : List (ℕ × Fin 2))
    (rect : ℕ × ℕ × ℕ × ℕ) (mu : List (RowKey × ℚ)) :
    checkLeaf ctx assign rect mu
      = checkLeafGen ctx assign rect mu
          (Array.replicate ctx.T.nLab ((0 : ℚ), (0 : ℚ))) 0 := rfl

lemma checkLeafGen_eq (ctx : Ctx) (assign : List (ℕ × Fin 2))
    (rect : ℕ × ℕ × ℕ × ℕ) (mu : List (RowKey × ℚ))
    (C0 : Array Q2) (LB0 : ℚ) :
    checkLeafGen ctx assign rect mu C0 LB0 =
      match muFold ctx assign mu (C0, LB0) with
      | none => false
      | some (C, LB) => checkLeafTail ctx rect C LB := by
  induction mu generalizing C0 LB0 with
  | nil =>
    unfold checkLeafGen checkLeafTail muFold
    obtain ⟨pLo, pHi, qLo, qHi⟩ := rect
    simp only [List.foldlM_nil, List.forIn_nil, Id.run]
    rfl
  | cons kv mu' ih =>
    unfold checkLeafGen at *
    simp only [muFold, List.forIn_cons, List.foldlM_cons] at *
    cases h : applyRow ctx assign C0 LB0 kv with
    | none => simp only; rfl
    | some s' =>
      obtain ⟨C', LB'⟩ := s'
      simpa [h, Id.run] using ih C' LB'

/-! ### Characterization of `applyRow` -/

lemma applyRow_some (ctx : Ctx) (assign : List (ℕ × Fin 2))
    (C : Array Q2) (LB : ℚ) (kv : RowKey × ℚ) (out : Array Q2 × ℚ)
    (h : applyRow ctx assign C LB kv = some out) :
    ∃ row : RowData, AllowedRow ctx assign row ∧ 0 ≤ kv.2 ∧
      out.1 = applyCoeffs C (kv.2) row.coeffs ∧
      out.2 = LB - (kv.2) * row.const := by
  obtain ⟨key, v⟩ := kv
  cases key with
  | s d p =>
    dsimp only [applyRow] at h
    by_cases hv : v < 0
    · simp [hv] at h
    rw [if_neg hv] at h
    by_cases hbad : (d == p || decide (d ≥ ctx.T.nLab) || decide (p ≥ ctx.T.nLab)) = true
    · rw [if_pos hbad] at h; exact absurd h (by simp)
    rw [if_neg hbad] at h
    simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, not_or, not_le] at hbad
    obtain ⟨⟨hne, hd⟩, hp⟩ := hbad
    injection h with h
    subst h
    refine ⟨rowS ctx.T d p, AllowedRow.s d p hd hp hne, not_lt.mp hv, ?_, ?_⟩
    · have e2 : (fun c => qsub c (qsmul (v) (ctx.T.normalOf d)))
          = (fun c => qadd c (qsmul (v)
              (-(ctx.T.normalOf d).1, -(ctx.T.normalOf d).2))) := by
        funext c
        simp only [qsub, qadd, qsmul, Prod.mk.injEq]
        exact ⟨by ring, by ring⟩
      change _ = applyCoeffs C (v) [(d, ctx.T.normalOf d),
        (p, (-(ctx.T.normalOf d).1, -(ctx.T.normalOf d).2))]
      rw [applyCoeffs_cons, applyCoeffs_cons, applyCoeffs_nil, ← e2]
    · change LB = LB - v * (rowS ctx.T d p).const
      simp [rowS]
  | n =>
    dsimp only [applyRow] at h
    by_cases hv : v < 0
    · simp [hv] at h
    rw [if_neg hv] at h
    injection h with h
    subst h
    refine ⟨rowN, AllowedRow.n, not_lt.mp hv, ?_, ?_⟩
    · have e1 : (fun (c : Q2) => qadd c ((v : ℚ), (0 : ℚ)))
          = (fun c => qadd c (qsmul (v) ((1 : ℚ), (0 : ℚ)))) := by
        funext c
        simp only [qadd, qsmul, Prod.mk.injEq]
        exact ⟨by ring, by ring⟩
      have e2 : (fun (c : Q2) => qsub c ((v : ℚ), (0 : ℚ)))
          = (fun c => qadd c (qsmul (v) ((-1 : ℚ), (0 : ℚ)))) := by
        funext c
        simp only [qsub, qadd, qsmul, Prod.mk.injEq]
        exact ⟨by ring, by ring⟩
      change _ = applyCoeffs C (v) [(1, ((1 : ℚ), (0 : ℚ))), (0, ((-1 : ℚ), (0 : ℚ)))]
      rw [applyCoeffs_cons, applyCoeffs_cons, applyCoeffs_nil, ← e1, ← e2]
    · change LB = LB - v * rowN.const
      simp [rowN]
  | e m r =>
    dsimp only [applyRow] at h
    by_cases hv : v < 0
    · simp [hv] at h
    rw [if_neg hv] at h
    by_cases hmem : assign.contains (m, r)
    · rw [if_pos hmem] at h
      cases hrow : ctx.eRows.getD (2 * m + r.val) none with
      | none => rw [hrow] at h; exact absurd h (by simp)
      | some row =>
        rw [hrow] at h
        injection h with h
        subst h
        exact ⟨row, AllowedRow.e m r row (by simpa using hmem) hrow,
          not_lt.mp hv, rfl, rfl⟩
    · rw [if_neg hmem] at h; exact absurd h (by simp)

/-! ### Characterization of the whole mu-fold -/

lemma muFold_some (ctx : Ctx) (assign : List (ℕ × Fin 2))
    (mu : List (RowKey × ℚ)) (init out : Array Q2 × ℚ)
    (h : muFold ctx assign mu init = some out) :
    ∃ rws : List (RowData × ℚ),
      (∀ rm ∈ rws, 0 ≤ rm.2 ∧ AllowedRow ctx assign rm.1) ∧
      out.1 = rws.foldl (fun C rm => applyCoeffs C rm.2 rm.1.coeffs) init.1 ∧
      out.2 = init.2 + lbOf rws := by
  induction mu generalizing init with
  | nil =>
    simp only [muFold, List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
    exact ⟨[], by simp, by simp [← h], by simp [← h]⟩
  | cons kv mu' ih =>
    rw [muFold, List.foldlM_cons] at h
    cases happ : applyRow ctx assign init.1 init.2 kv with
    | none => rw [happ] at h; exact absurd h (by simp)
    | some mid =>
      rw [happ] at h
      obtain ⟨row, hallow, hv, hC, hLB⟩ := applyRow_some _ _ _ _ _ _ happ
      obtain ⟨rws, hrws, hCout, hLBout⟩ := ih mid h
      refine ⟨(row, kv.2) :: rws, ?_, ?_, ?_⟩
      · intro rm hm
        rcases List.mem_cons.mp hm with rfl | hm2
        · exact ⟨hv, hallow⟩
        · exact hrws rm hm2
      · rw [hCout, List.foldl_cons, ← hC]
      · rw [hLBout, hLB]
        simp only [lbOf_cons]
        ring


end MoserWorm.UpperBound.Certificate
