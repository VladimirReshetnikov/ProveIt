/- Exact certificate arithmetic and its kernel-checked proof interface. -/
import MoserWorm.UpperBound.Certificate.Kernel.Partition

namespace MoserWorm.UpperBound.Certificate.Kernel

open MoserWorm.UpperBound.Certificate MoserWorm.UpperBound.Certificate.Partition

/-- Check presence on the structural list, without rebuilding a decoded array. -/
theorem decodeCtx_rows_present (c : KCtx)
    (h : c.eRows.all Option.isSome = true) :
    (decodeCtx c).eRows.all Option.isSome = true := by
  simpa [decodeCtx, ← Array.all_toList, List.all_map] using h

/-- Decidable equality for `RowData` (scoped: needed only for the kernel
`==` checks of the generated header modules). -/
scoped instance : DecidableEq RowData := fun a b =>
  decidable_of_iff (a.coeffs = b.coeffs ∧ a.const = b.const)
    (by cases a; cases b; simp)

/-- Decidable equality for `LabelTables` (scoped, same reason). -/
scoped instance : DecidableEq LabelTables := fun a b =>
  decidable_of_iff (a.kR = b.kR ∧ a.kL = b.kL ∧ a.right = b.right ∧
    a.left = b.left) (by cases a; cases b; simp)

/-! ### The shipped certificate -/

/-- Kernel placement spec: mirrors `PSpec`. -/
inductive KPSpec where
  | flush (s : Fin 4) (flip mir : Bool)
  | rot (t : KQ) (mir : Bool)
  | vrot (t : KQ) (mir : Bool)

def decodePSpec : KPSpec → PSpec
  | .flush s f m => .flush s f m
  | .rot t m => .rot (toQ t) m
  | .vrot t m => .vrot (toQ t) m

/-- Kernel certificate: mirrors `Cert` (via `decodeCert`). -/
structure KCert where
  t0 : KQ
  t1 : KQ
  t2 : KQ
  t3 : KQ
  h0 : KQ
  h1 : KQ
  h2 : KQ
  h3 : KQ
  target : KQ
  kR : ℕ
  kL : ℕ
  specs : List KPSpec
  tree : KTree

def decodeCert (c : KCert) : Cert :=
  { t := ![toQ c.t0, toQ c.t1, toQ c.t2, toQ c.t3],
    h := ![toQ c.h0, toQ c.h1, toQ c.h2, toQ c.h3],
    target := toQ c.target, kR := c.kR, kL := c.kL,
    specs := (c.specs.map decodePSpec).toArray,
    tree := decodeTree c.tree }

/-! ### E-rows, row by row -/

/-- The `k`-th E-row as computed by `eRowsArr` (body copied verbatim). -/
def eRowAt (c : Cert) (T : LabelTables) (named : Array Q2) (k : ℕ) :
    Option RowData :=
  rowE T named (c.specs.getD (k / 2) default)
    ⟨k % 2, Nat.mod_lt _ two_pos⟩

theorem eRowsArr_eq_ofFn (c : Cert) (T : LabelTables) (named : Array Q2) :
    eRowsArr c T named =
      Array.ofFn (n := 2 * c.specs.size) (fun k => eRowAt c T named k.val) :=
  rfl

/-- `eRowAt` with the spec list given directly (so the generated header
modules do not have to mention the full certificate/tree). -/
def eRowAtL (specs : List PSpec) (T : LabelTables) (named : Array Q2)
    (k : ℕ) : Option RowData :=
  rowE T named (specs.getD (k / 2) default)
    ⟨k % 2, Nat.mod_lt _ two_pos⟩

theorem eRowAt_eq_eRowAtL (c : Cert) (l : List PSpec)
    (hl : c.specs.toList = l) (T : LabelTables) (named : Array Q2) (k : ℕ) :
    eRowAt c T named k = eRowAtL l T named k := by
  unfold eRowAt eRowAtL
  rw [← hl, ← toArray_getD c.specs.toList (k / 2) default]

/-! ### Range gluing -/

/-- Glue two contiguous `range'` alls. -/
theorem all_range'_glue (f : ℕ → Bool) (s a b : ℕ)
    (h1 : (List.range' s a).all f = true)
    (h2 : (List.range' (s + a) b).all f = true) :
    (List.range' s (a + b)).all f = true := by
  have := List.range'_append (s := s) (m := a) (n := b) (step := 1)
  simp only [Nat.mul_one, Nat.mul_comm] at this
  rw [← this, List.all_append, h1, h2]
  rfl

/-- Pointwise facts from a `[0, n)` coverage. -/
theorem forall_of_range'_all (f : ℕ → Bool) (n : ℕ)
    (h : (List.range' 0 n).all f = true) : ∀ k, k < n → f k = true := by
  rw [List.all_eq_true] at h
  intro k hk
  exact h k (List.mem_range'_1.mpr ⟨Nat.zero_le _, by omega⟩)

/-- The E-row array equals the shipped literal, from per-range pointwise
`beq` facts. -/
theorem eRowsArr_eq_of_ranges (c : Cert) (T : LabelTables) (named : Array Q2)
    (er : Array (Option RowData))
    (hsize : 2 * c.specs.size = er.size)
    (hall : (List.range' 0 er.size).all
      (fun k => eRowAt c T named k == er.getD k none) = true) :
    eRowsArr c T named = er := by
  have hpt := forall_of_range'_all _ _ hall
  rw [eRowsArr_eq_ofFn]
  refine Array.ext (by simpa using hsize) ?_
  intro i h1 h2
  rw [Array.getElem_ofFn]
  have h := hpt i h2
  rw [beq_iff_eq] at h
  rw [h, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h2]
  rfl

/-! ### Header assembly -/

/-- `checkHeader` and `theCtxR` from the kernel-checked pieces. -/
theorem header_of_parts (c : Cert) (T : LabelTables) (er : Array (Option RowData))
    (hlit : checkLiterals c = true)
    (hortho : c.specs.toList.all (fun p => isOrtho (specMap p)) = true)
    (hbuild : buildLabels c.specs.toList = some T)
    (hkR : T.kR = c.kR) (hkL : T.kL = c.kL)
    (hlab : labelsOK T = true)
    (her : eRowsArr c T (namedByAngle T) = er)
    (hsome : er.all Option.isSome = true) :
    checkHeader c = true ∧
      theCtxR c = some ({ T := T, eRows := er, target := c.target },
        (0, T.kR, 0, T.kL)) := by
  have hortho' : c.specs.all (fun p => isOrtho (specMap p)) = true := by
    rw [← Array.all_toList]
    exact hortho
  constructor
  · unfold checkHeader
    rw [hbuild, hlit, hortho']
    dsimp only
    rw [hkR, hkL, hlab, her, hsome]
    simp
  · unfold theCtxR
    rw [hbuild]
    dsimp only
    rw [her]

/-- The whole kernel-only certificate check, assembled.  All hypotheses are
either `decide +kernel` facts from the generated modules or `rfl`. -/
theorem checkCert_of_kernel (kc : KCert) (kctx : KCtx) (d : ℕ) (hd : d ≤ 999)
    (hlit : checkLiterals (decodeCert kc) = true)
    (hortho : (decodeCert kc).specs.toList.all
      (fun p => isOrtho (specMap p)) = true)
    (hbuild : buildLabels (decodeCert kc).specs.toList
      = some (decodeCtx kctx).T)
    (hkR : (decodeCtx kctx).T.kR = (decodeCert kc).kR)
    (hkL : (decodeCtx kctx).T.kL = (decodeCert kc).kL)
    (hlab : labelsOK (decodeCtx kctx).T = true)
    (her : eRowsArr (decodeCert kc) (decodeCtx kctx).T
      (namedByAngle (decodeCtx kctx).T) = (decodeCtx kctx).eRows)
    (hsome : (decodeCtx kctx).eRows.all Option.isSome = true)
    (htgt : (decodeCtx kctx).target = (decodeCert kc).target)
    (htop : kCutTop kctx.eRows.length d kc.tree []
      (0, (decodeCtx kctx).T.kR, 0, (decodeCtx kctx).T.kL) = true)
    (hobs : ∀ ob ∈ kCutFrontier d kc.tree []
        (0, (decodeCtx kctx).T.kR, 0, (decodeCtx kctx).T.kL),
      checkTree (decodeCtx kctx) (1000 - d) (decodeTree ob.1)
        ob.2.1 ob.2.2 = true) :
    checkCert (decodeCert kc) = true := by
  obtain ⟨hh, hctx⟩ := header_of_parts (decodeCert kc) (decodeCtx kctx).T
    (decodeCtx kctx).eRows hlit hortho hbuild hkR hkL hlab her hsome
  refine checkCert_of_parts (decodeCert kc) (decodeCtx kctx)
    (0, (decodeCtx kctx).T.kR, 0, (decodeCtx kctx).T.kL) hh ?_ ?_
  · rw [hctx, ← htgt]
  · exact checkTree_of_kernel_parts kctx d hd kc.tree _ htop hobs

/-- The E-row identity from the glued per-range `eRowAtL` facts. -/
theorem her_of (c : Cert) (l : List PSpec) (hl : c.specs.toList = l)
    (T : LabelTables) (named : Array Q2) (er : Array (Option RowData))
    (hsize : 2 * c.specs.size = er.size)
    (hall : (List.range' 0 er.size).all
      (fun k => eRowAtL l T named k == er.getD k none) = true) :
    eRowsArr c T named = er := by
  refine eRowsArr_eq_of_ranges c T named er hsize ?_
  rw [all_congr _ _ _
    (fun k _ => by rw [eRowAt_eq_eRowAtL c l hl])]
  exact hall

/-- Transport the ortho fact from the spec-list form. -/
theorem hortho_of (c : Cert) (l : List PSpec) (hl : c.specs.toList = l)
    (h : l.all (fun p => isOrtho (specMap p)) = true) :
    c.specs.toList.all (fun p => isOrtho (specMap p)) = true := by
  rw [hl]
  exact h

end MoserWorm.UpperBound.Certificate.Kernel
