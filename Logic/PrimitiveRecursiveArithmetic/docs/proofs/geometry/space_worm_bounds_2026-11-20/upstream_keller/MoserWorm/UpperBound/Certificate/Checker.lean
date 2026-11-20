/- Exact certificate arithmetic and its kernel-checked proof interface. -/
import MoserWorm.UpperBound.Certificate.Spec

namespace MoserWorm.UpperBound.Certificate

/-- Key of a multiplier row. -/
inductive RowKey
  | s (d p : ℕ)              -- S:d:P
  | n                        -- N
  | e (m : ℕ) (r : Fin 2)    -- E:placement m:ray r
deriving Repr, DecidableEq

/-- Decision tree with leaf multipliers. -/
inductive CTree
  | pl (m : ℕ) (c0 c1 : CTree)                       -- placement node
  | split (cells : List ((ℕ × ℕ × ℕ × ℕ) × CTree))   -- refinement node
  | leaf (mu : List (RowKey × ℚ))                    -- leaf
deriving Repr

set_option linter.dupNamespace false in
/-- A certificate for the fixed quadrilateral. -/
structure Cert where
  t : Fin 4 → ℚ
  h : Fin 4 → ℚ
  target : ℚ
  kR : ℕ
  kL : ℕ
  specs : Array PSpec
  tree : CTree

/-! ### Checking -/

/-- Context prepared once per certificate. -/
structure Ctx where
  T : LabelTables
  eRows : Array (Option RowData)   -- index 2*m + r
  target : ℚ

/-- Accumulate one multiplier row into the force array and the bound.
Returns `none` if the row is invalid at this leaf. -/
def applyRow (ctx : Ctx) (assign : List (ℕ × Fin 2))
    (C : Array Q2) (LB : ℚ) : RowKey × ℚ → Option (Array Q2 × ℚ)
  | (key, v) =>
    if v < 0 then none else
    let mult := v
    match key with
    | .s d p =>
      if d == p || d ≥ ctx.T.nLab || p ≥ ctx.T.nLab then none
      else
        let nd := ctx.T.normalOf d
        let C := C.modify d (fun c => qadd c (qsmul mult nd))
        let C := C.modify p (fun c => qsub c (qsmul mult nd))
        some (C, LB)
    | .n =>
      let C := C.modify 1 (fun c => qadd c (mult, 0))
      let C := C.modify 0 (fun c => qsub c (mult, 0))
      some (C, LB)
    | .e m r =>
      if assign.contains (m, r) then
        match ctx.eRows.getD (2 * m + r.val) none with
        | none => none
        | some row =>
          let C := row.coeffs.foldl
            (fun C (l, v) => C.modify l (fun c => qadd c (qsmul mult v))) C
          some (C, LB - mult * row.const)
      else none

/-- Check valid multipliers, balance, all four norm bounds, and the target. -/
def checkLeaf (ctx : Ctx) (assign : List (ℕ × Fin 2))
    (rect : ℕ × ℕ × ℕ × ℕ) (mu : List (RowKey × ℚ)) : Bool := Id.run do
  let n := ctx.T.nLab
  let mut C : Array Q2 := .replicate n (0, 0)
  let mut LB : ℚ := 0
  for kv in mu do
    match applyRow ctx assign C LB kv with
    | none => return false
    | some (C', LB') => C := C'; LB := LB'
  -- forces sum to zero
  let s := C.foldl qadd (0, 0)
  if s != ((0 : ℚ), (0 : ℚ)) then return false
  let (pLo, pHi, qLo, qHi) := rect
  let maxNorm2 := familyMaxNorm2 ctx.T C pLo pHi qLo qHi
  return maxNorm2 ≤ 1 && LB ≥ ctx.target

/-- Check a subtree at (assign, rect).  Fuel bounds the recursion depth. -/
def checkTree (ctx : Ctx) : ℕ → CTree → List (ℕ × Fin 2) →
    ℕ × ℕ × ℕ × ℕ → Bool
  | 0, _, _, _ => false
  | fuel + 1, .pl m c0 c1, assign, rect =>
    -- placement m exists, not yet assigned on this path
    (2 * m + 1 < ctx.eRows.size) &&
    !(assign.any (fun (m', _) => m' == m)) &&
    checkTree ctx fuel c0 ((m, 0) :: assign) rect &&
    checkTree ctx fuel c1 ((m, 1) :: assign) rect
  | fuel + 1, .split cells, assign, rect => Id.run do
    let (pLo, pHi, qLo, qHi) := rect
    -- every cell a rectangle inside the parent
    for ((a, b, c, d), _) in cells do
      if !(pLo ≤ a && a ≤ b && b ≤ pHi && qLo ≤ c && c ≤ d && d ≤ qHi) then
        return false
    -- pairwise disjoint
    let rects := cells.map (·.1)
    let rec pairwiseOk : List (ℕ × ℕ × ℕ × ℕ) → Bool
      | [] => true
      | (a, b, c, d) :: rest =>
        rest.all (fun (a2, b2, c2, d2) =>
          b < a2 || b2 < a || d < c2 || d2 < c) && pairwiseOk rest
    if !pairwiseOk rects then return false
    -- cardinalities add up
    let area := rects.foldl
      (fun acc (a, b, c, d) => acc + (b - a + 1) * (d - c + 1)) 0
    if area != (pHi - pLo + 1) * (qHi - qLo + 1) then return false
    for (cell, child) in cells do
      if !checkTree ctx fuel child assign cell then return false
    return true
  | _ + 1, .leaf mu, assign, rect => checkLeaf ctx assign rect mu

/-- Literal check: the certificate is about the fixed quadrilateral at target 1. -/
def checkLiterals (c : Cert) : Bool :=
  c.t 0 == tLit 0 && c.t 1 == tLit 1 && c.t 2 == tLit 2 && c.t 3 == tLit 3 &&
  c.h 0 == hLit 0 && c.h 1 == hLit 1 && c.h 2 == hLit 2 && c.h 3 == hLit 3 &&
  c.target == 1

/-- All E rows (index 2m + r), built totally. -/
def eRowsArr (c : Cert) (T : LabelTables) (named : Array Q2) :
    Array (Option RowData) :=
  .ofFn (n := 2 * c.specs.size) (fun k =>
    rowE T named (c.specs.getD (k.val / 2) default)
      ⟨k.val % 2, Nat.mod_lt _ two_pos⟩)

/-- Full certificate check (thm mode): literals, structure, all leaves. -/
def checkCert (c : Cert) : Bool :=
  checkLiterals c &&
  c.specs.all (fun p => isOrtho (specMap p)) &&
  match buildLabels c.specs.toList with
  | none => false
  | some T =>
    T.kR == c.kR && T.kL == c.kL && labelsOK T &&
    (eRowsArr c T (namedByAngle T)).all Option.isSome &&
    checkTree { T := T, eRows := eRowsArr c T (namedByAngle T),
                target := c.target }
      1000 c.tree [] (0, T.kR, 0, T.kL)

end MoserWorm.UpperBound.Certificate
