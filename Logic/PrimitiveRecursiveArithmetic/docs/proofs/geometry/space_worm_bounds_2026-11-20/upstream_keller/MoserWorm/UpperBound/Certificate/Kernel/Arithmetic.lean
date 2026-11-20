/- Exact certificate arithmetic and its kernel-checked proof interface. -/
import MoserWorm.UpperBound.Certificate.Partition

namespace MoserWorm.UpperBound.Certificate.Kernel

open MoserWorm.UpperBound.Certificate

/-! ### Kernel rationals -/

/-- Kernel rational `(n, d)` denoting `n / (d + 1)`: numerator and
PREDECESSOR of the denominator, so the denominator is positive by
construction.  Never reduced (no gcd) except via the explicit `kRed`. -/
abbrev KQ := ℤ × ℕ

/-- Kernel plane vector. -/
abbrev KQ2 := KQ × KQ

/-- The rational denoted by a `KQ`. -/
def toQ (x : KQ) : ℚ := (x.1 : ℚ) / ((x.2 + 1 : ℕ) : ℚ)

/-- The plane vector denoted by a `KQ2`. -/
def toQ2 (u : KQ2) : Q2 := (toQ u.1, toQ u.2)

def kQ0 : KQ := (0, 0)
def kQ1 : KQ := (1, 0)
def kQ2z : KQ2 := (kQ0, kQ0)

/-- Denominator product on predecessors: `(a+1)*(b+1) - 1`. -/
@[inline] def dmul (a b : ℕ) : ℕ := a * b + a + b

def kAdd (x y : KQ) : KQ :=
  if x.2 == y.2 then (x.1 + y.1, x.2)
  else (x.1 * ((y.2 : ℤ) + 1) + y.1 * ((x.2 : ℤ) + 1), dmul x.2 y.2)

def kSub (x y : KQ) : KQ :=
  if x.2 == y.2 then (x.1 - y.1, x.2)
  else (x.1 * ((y.2 : ℤ) + 1) - y.1 * ((x.2 : ℤ) + 1), dmul x.2 y.2)

def kMul (x y : KQ) : KQ := (x.1 * y.1, dmul x.2 y.2)

/-- Exact `toQ x ≤ toQ y` by cross-multiplication (denominators positive;
fast path when they coincide). -/
def kLe (x y : KQ) : Bool :=
  if x.2 == y.2 then x.1 ≤ y.1
  else x.1 * ((y.2 : ℤ) + 1) ≤ y.1 * ((x.2 : ℤ) + 1)

/-- Exact `toQ x < toQ y`. -/
def kLt (x y : KQ) : Bool :=
  if x.2 == y.2 then x.1 < y.1
  else x.1 * ((y.2 : ℤ) + 1) < y.1 * ((x.2 : ℤ) + 1)

/-- Exact `toQ x = 0`. -/
def kEqZero (x : KQ) : Bool := x.1 == 0

/-- Exact `toQ x < 0`. -/
def kNegative (x : KQ) : Bool := x.1 < 0

/-- Exact `0 ≤ toQ x`. -/
def kNonneg (x : KQ) : Bool := 0 ≤ x.1

/-- Reduce a `KQ` by the gcd without changing its value. -/
def kRed (x : KQ) : KQ :=
  let g := Nat.gcd x.1.natAbs (x.2 + 1)
  (x.1 / (g : ℤ), (x.2 + 1) / g - 1)

/-- Scale to denominator `dp+1` when it divides exactly (value-preserving
either way; used to put cumulative sums on a common denominator so the
family loops hit the same-denominator fast paths). -/
def kToDen (dp : ℕ) (x : KQ) : KQ :=
  let q := (dp + 1) / (x.2 + 1)
  if (x.2 + 1) * q == dp + 1 then (x.1 * (q : ℤ), dp) else x

def kToDen2 (dp : ℕ) (u : KQ2) : KQ2 := (kToDen dp u.1, kToDen dp u.2)

/-- Bring a list of vectors to their common (lcm) denominator. -/
def kCommon (l : List KQ2) : List KQ2 :=
  let D := l.foldl
    (fun acc u => Nat.lcm (Nat.lcm acc (u.1.2 + 1)) (u.2.2 + 1)) 1
  l.map (kToDen2 (D - 1))

def kAdd2 (u v : KQ2) : KQ2 := (kAdd u.1 v.1, kAdd u.2 v.2)
def kSub2 (u v : KQ2) : KQ2 := (kSub u.1 v.1, kSub u.2 v.2)
def kSmul (c : KQ) (u : KQ2) : KQ2 := (kMul c u.1, kMul c u.2)
def kNorm2 (u : KQ2) : KQ := kAdd (kMul u.1 u.1) (kMul u.2 u.2)
def kNeg2 (u : KQ2) : KQ2 := ((-u.1.1, u.1.2), (-u.2.1, u.2.2))
def kRed2 (u : KQ2) : KQ2 := (kRed u.1, kRed u.2)

/-! ### `KVec`: a binary trie with logarithmic access

Node at index 0, odd indices `2j+1` in the left subtree (at `j`), even
indices `2j+2` in the right subtree (at `j`).  `modify` never allocates
(out-of-capacity indices are no-ops, matching `Array.modify` out of range);
capacity is fixed by building a full trie up front (`ofList`). -/

inductive KVec (α : Type) where
  | nil  : KVec α
  | node (v : α) (o e : KVec α) : KVec α

namespace KVec

def getD (d : α) : KVec α → ℕ → α
  | .nil, _ => d
  | .node v _ _, 0 => v
  | .node _ o e, n + 1 => if n % 2 == 0 then getD d o (n / 2) else getD d e (n / 2)

def modify (f : α → α) : KVec α → ℕ → KVec α
  | .nil, _ => .nil
  | .node v o e, 0 => .node (f v) o e
  | .node v o e, n + 1 =>
    if n % 2 == 0 then .node v (modify f o (n / 2)) e
    else .node v o (modify f e (n / 2))

/-- Whether index `i` is materialized. -/
def has : KVec α → ℕ → Bool
  | .nil, _ => false
  | .node _ _ _, 0 => true
  | .node _ o e, n + 1 => if n % 2 == 0 then has o (n / 2) else has e (n / 2)

/-- Full trie of depth `h` (indices `0 .. 2^h - 2`), all values `d`. -/
def full (d : α) : ℕ → KVec α
  | 0 => .nil
  | h + 1 => .node d (full d h) (full d h)

def set (x : α) (t : KVec α) (i : ℕ) : KVec α := modify (fun _ => x) t i

/-- Set list elements at consecutive indices starting at `i`. -/
def setFrom (t : KVec α) (i : ℕ) : List α → KVec α
  | [] => t
  | x :: xs => setFrom (set x t i) (i + 1) xs

end KVec

/-- Number of binary digits (fuel-structural, kernel-friendly):
`n < 2^(bits n)`. -/
def bitsAux : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, n => if n == 0 then 0 else bitsAux fuel (n / 2) + 1

def bits (n : ℕ) : ℕ := bitsAux n n

/-- Trie holding the elements of `l` (indices beyond `l.length` read as `d`,
matching `List.getD`); capacity `2^(bits l.length + 1) - 1 > l.length`. -/
def KVec.ofList (d : α) (l : List α) : KVec α :=
  KVec.setFrom (KVec.full d (bits l.length + 1)) 0 l

/-! ### Kernel data structures (emitted by the untrusted converter) -/

/-- Kernel row: mirrors `RowData`. -/
structure KRow where
  coeffs : List (ℕ × KQ2)
  const : KQ

/-- Kernel tree: mirrors `CTree`, multipliers as `KQ`. -/
inductive KTree where
  | pl (m : ℕ) (c0 c1 : KTree)
  | split (cells : List ((ℕ × ℕ × ℕ × ℕ) × KTree))
  | leaf (mu : List (RowKey × KQ))

/-- Kernel context: mirrors `Ctx` (via `decodeCtx`). -/
structure KCtx where
  kR : ℕ
  kL : ℕ
  right : List KQ2
  left : List KQ2
  eRows : List (Option KRow)
  target : KQ

/-! ### Decoding (the direction the bridge consumes) -/

def decodeRow (r : KRow) : RowData :=
  { coeffs := r.coeffs.map (fun lv => (lv.1, toQ2 lv.2)), const := toQ r.const }

def decodeTree : KTree → CTree
  | .pl m c0 c1 => .pl m (decodeTree c0) (decodeTree c1)
  | .split cells => .split (cells.attach.map
      (fun x => (x.1.1, decodeTree x.1.2)))
  | .leaf mu => .leaf (mu.map (fun kv => (kv.1, toQ kv.2)))
decreasing_by
  · simp only [KTree.pl.sizeOf_spec]; omega
  · simp only [KTree.pl.sizeOf_spec]; omega
  · obtain ⟨⟨r, ch⟩, hx⟩ := x
    have := List.sizeOf_lt_of_mem hx
    simp only [KTree.split.sizeOf_spec, Prod.mk.sizeOf_spec] at this ⊢
    omega

/-- `decodeTree` on a split node, in `map` form. -/
theorem decodeTree_split (cells : List ((ℕ × ℕ × ℕ × ℕ) × KTree)) :
    decodeTree (.split cells) =
      .split (cells.map (fun x => (x.1, decodeTree x.2))) := by
  rw [decodeTree]
  congr 1
  exact List.attach_map_val (l := cells) (f := fun x => (x.1, decodeTree x.2))

def decodeCtx (c : KCtx) : Ctx :=
  { T := { kR := c.kR, kL := c.kL,
           right := (c.right.map toQ2).toArray,
           left := (c.left.map toQ2).toArray },
    eRows := (c.eRows.map (Option.map decodeRow)).toArray,
    target := toQ c.target }

/-! ### The kernel checker -/

/-- `LabelTables.normalOf` on the kernel data. -/
def kNormalOf (kR : ℕ) (right left : List KQ2) (l : ℕ) : KQ2 :=
  if l == 0 then (kQ0, (-1, 0))
  else if l == 1 then (kQ0, (-1, 0))
  else if l == 2 then (kQ0, (1, 0))
  else if l < 3 + kR then right.getD (l - 3) kQ2z
  else left.getD (l - 3 - kR) kQ2z

/-- `applyRow` on the kernel data.  The force accumulator is a trie of
`KQ2` (indexed by label); out-of-capacity modifies are no-ops exactly like
`Array.modify` out of range.  Every write is `kRed`-reduced: measured 11x
faster in the kernel than accumulating unreduced fractions (the cost is
dominated by big-number term handling, not op count). -/
def kApplyRow (nLab : ℕ) (ntrie : KVec KQ2) (etrie : KVec (Option KRow))
    (assign : List (ℕ × Fin 2)) (C : KVec KQ2) (LB : KQ) :
    RowKey × KQ → Option (KVec KQ2 × KQ)
  | (key, v) =>
    if kNegative v then none else
    let mult := v
    match key with
    | .s d p =>
      if d == p || d ≥ nLab || p ≥ nLab then none
      else
        let nd := ntrie.getD kQ2z d
        let C := C.modify (fun c => kRed2 (kAdd2 c (kSmul mult nd))) d
        let C := C.modify (fun c => kRed2 (kSub2 c (kSmul mult nd))) p
        some (C, LB)
    | .n =>
      let C := C.modify (fun c => kRed2 (kAdd2 c (mult, kQ0))) 1
      let C := C.modify (fun c => kRed2 (kSub2 c (mult, kQ0))) 0
      some (C, LB)
    | .e m r =>
      if assign.contains (m, r) then
        match etrie.getD none (2 * m + r.val) with
        | none => none
        | some row =>
          let C := row.coeffs.foldl
            (fun C (lv : ℕ × KQ2) =>
              C.modify (fun c => kRed2 (kAdd2 c (kSmul mult lv.2))) lv.1) C
          some (C, kRed (kSub LB (kMul mult row.const)))
      else none

/-- Fold `kApplyRow` over the multiplier rows (the `for`/early-`return` loop
of `checkLeaf` as a structural recursion). -/
def kApplyRows (nLab : ℕ) (ntrie : KVec KQ2) (etrie : KVec (Option KRow))
    (assign : List (ℕ × Fin 2)) :
    List (RowKey × KQ) → KVec KQ2 × KQ → Option (KVec KQ2 × KQ)
  | [], s => some s
  | kv :: rest, s =>
    match kApplyRow nLab ntrie etrie assign s.1 s.2 kv with
    | none => none
    | some s' => kApplyRows nLab ntrie etrie assign rest s'

/-- Cumulative sums (reduced at each step): mirrors the `A`/`B` arrays of
`familyMaxNorm2`; `cum[0] = 0`, `cum[i+1] = cum[i] + red (C[base + i])`. -/
def kCum (C : KVec KQ2) (base : ℕ) : ℕ → List KQ2
  | 0 => [kQ2z]
  | i + 1 =>
    let prev := kCum C base i
    prev ++ [kRed2 (kAdd2 (prev.getD i kQ2z) (kRed2 (C.getD kQ2z (base + i))))]

/-- `if qnorm2 v > best then qnorm2 v else best`. -/
def kUpd (best : KQ) (v : KQ2) : KQ :=
  if kLt best (kNorm2 v) then kNorm2 v else best

/-- Structural `foldl` over `List.range' a n` (kernel-friendly loop). -/
def kFoldN (f : σ → ℕ → σ) : σ → ℕ → ℕ → σ
  | s, _, 0 => s
  | s, a, n + 1 => kFoldN f (f s a) (a + 1) n

/-- `familyMaxNorm2` on the kernel data (exact same ℚ value). -/
def kFamilyMaxNorm2 (kR kL : ℕ) (C : KVec KQ2)
    (pLo pHi qLo qHi : ℕ) : KQ :=
  let k := kR
  let m := kL
  let A := kCommon (kCum C (3 + k) m)
  let B := kCommon (kCum C 3 k)
  let Fm := kRed2 (C.getD kQ2z 0)
  let Fp := kRed2 (C.getD kQ2z 1)
  -- (i) left middle runs
  let best := kFoldN (fun best a =>
      kFoldN (fun best b =>
          kUpd best (kSub2 (A.getD (b + 1) kQ2z) (A.getD a kQ2z)))
        best a (m - a))
    kQ0 qLo (m - qLo)
  -- (ii) left tail ∪ {F-}
  let best := kFoldN (fun best j =>
      kUpd best (kAdd2 (kSub2 (A.getD m kQ2z) (A.getD j kQ2z)) Fm))
    best 0 (min qHi m + 1)
  -- (iii) right prefix ∪ {P₊}
  let best := kFoldN (fun best j =>
      kUpd best (kAdd2 Fp (B.getD j kQ2z)))
    best pLo (k + 1 - pLo)
  -- (iv) right blocks (empty blocks included)
  kFoldN (fun best a =>
      kFoldN (fun best b =>
          kUpd best (kSub2 (B.getD b kQ2z) (B.getD a kQ2z)))
        best a (pHi + 1 - a))
    best 0 (pHi + 1)

/-- Sum of the first `n` labels of the force trie (same order as
`C.foldl qadd` over the array). -/
def kSumTo (C : KVec KQ2) : ℕ → KQ2
  | 0 => kQ2z
  | n + 1 => kRed2 (kAdd2 (kSumTo C n) (kRed2 (C.getD kQ2z n)))

/-- `checkLeaf` on the kernel data. -/
def kCheckLeaf (nLab : ℕ) (ntrie : KVec KQ2) (etrie : KVec (Option KRow))
    (kR kL : ℕ) (target : KQ) (assign : List (ℕ × Fin 2))
    (rect : ℕ × ℕ × ℕ × ℕ) (mu : List (RowKey × KQ)) : Bool :=
  match kApplyRows nLab ntrie etrie assign mu
      (KVec.full kQ2z (bits nLab + 1), kQ0) with
  | none => false
  | some (C, LB) =>
    let s := kSumTo C nLab
    if !(kEqZero s.1 && kEqZero s.2) then false
    else
      let (pLo, pHi, qLo, qHi) := rect
      let maxNorm2 := kRed (kFamilyMaxNorm2 kR kL C pLo pHi qLo qHi)
      kLe maxNorm2 kQ1 && kLe target LB

/-- `splitStruct` (Partition.lean) on the kernel cells (rect data is shared ℕ). -/
def kSplitStruct (cells : List ((ℕ × ℕ × ℕ × ℕ) × KTree))
    (rect : ℕ × ℕ × ℕ × ℕ) : Bool :=
  cells.all (fun x => Partition.insideOK rect x.1) &&
  checkTree.pairwiseOk (cells.map (fun x => x.1)) &&
  ((cells.map (fun x => x.1)).foldl
      (fun acc x => acc + (x.2.1 - x.1 + 1) * (x.2.2.2 - x.2.2.1 + 1)) 0
    == (rect.2.1 - rect.1 + 1) * (rect.2.2.2 - rect.2.2.1 + 1))

/-- `checkTree` on the kernel data (fuel-structural). -/
def kCheckTreeCore (nLab : ℕ) (ntrie : KVec KQ2) (etrie : KVec (Option KRow))
    (esz : ℕ) (kR kL : ℕ) (target : KQ) :
    ℕ → KTree → List (ℕ × Fin 2) → ℕ × ℕ × ℕ × ℕ → Bool
  | 0, _, _, _ => false
  | fuel + 1, .pl m c0 c1, assign, rect =>
    (decide (2 * m + 1 < esz)) &&
    !(assign.any (fun (m', _) => m' == m)) &&
    kCheckTreeCore nLab ntrie etrie esz kR kL target fuel c0 ((m, 0) :: assign) rect &&
    kCheckTreeCore nLab ntrie etrie esz kR kL target fuel c1 ((m, 1) :: assign) rect
  | fuel + 1, .split cells, assign, rect =>
    kSplitStruct cells rect &&
    cells.all (fun x =>
      kCheckTreeCore nLab ntrie etrie esz kR kL target fuel x.2 assign x.1)
  | _ + 1, .leaf mu, assign, rect =>
    kCheckLeaf nLab ntrie etrie kR kL target assign rect mu

/-- Entry point: precompute the label-normal trie and the E-row trie, then
run the fuel recursion.  Bridged in `KBridge.lean` to
`checkTree (decodeCtx c) fuel (decodeTree t) assign rect`. -/
def kCheckTree (c : KCtx) (fuel : ℕ) (t : KTree)
    (assign : List (ℕ × Fin 2)) (rect : ℕ × ℕ × ℕ × ℕ) : Bool :=
  let n := 3 + c.kR + c.kL
  let ntrie := KVec.ofList kQ2z
    ((List.range n).map (kNormalOf c.kR c.right c.left))
  let etrie := KVec.ofList none c.eRows
  kCheckTreeCore n ntrie etrie c.eRows.length c.kR c.kL c.target
    fuel t assign rect

/-! ### Frontier decomposition on the kernel data (mirrors `Cert/Partition.lean`) -/

/-- Kernel frontier obligation: subtree, assignment path, rectangle. -/
abbrev KOb := KTree × List (ℕ × Fin 2) × (ℕ × ℕ × ℕ × ℕ)

/-- `Partition.cutFrontier` on the kernel tree. -/
def kCutFrontier : ℕ → KTree → List (ℕ × Fin 2) → ℕ × ℕ × ℕ × ℕ → List KOb
  | 0, t, as, r => [(t, as, r)]
  | d + 1, t, as, r =>
    match t with
    | .pl m c0 c1 =>
      kCutFrontier d c0 ((m, 0) :: as) r ++ kCutFrontier d c1 ((m, 1) :: as) r
    | .split cells => cells.flatMap (fun x => kCutFrontier d x.2 as x.1)
    | .leaf mu => [(.leaf mu, as, r)]

/-- `Partition.cutTop` on the kernel tree (`esz` = number of E-rows). -/
def kCutTop (esz : ℕ) : ℕ → KTree → List (ℕ × Fin 2) → ℕ × ℕ × ℕ × ℕ → Bool
  | 0, _, _, _ => true
  | d + 1, t, as, r =>
    match t with
    | .pl m c0 c1 =>
      (decide (2 * m + 1 < esz)) &&
      !(as.any (fun (m', _) => m' == m)) &&
      kCutTop esz d c0 ((m, 0) :: as) r &&
      kCutTop esz d c1 ((m, 1) :: as) r
    | .split cells =>
      kSplitStruct cells r && cells.all (fun x => kCutTop esz d x.2 as x.1)
    | .leaf _ => true

/-- Check a batch of frontier obligations, sharing the precomputed tries
(one `decide +kernel` of this per generated range module). -/
def kCheckObs (c : KCtx) (fuel : ℕ) (obs : List KOb) : Bool :=
  let n := 3 + c.kR + c.kL
  let ntrie := KVec.ofList kQ2z
    ((List.range n).map (kNormalOf c.kR c.right c.left))
  let etrie := KVec.ofList none c.eRows
  obs.all (fun ob =>
    kCheckTreeCore n ntrie etrie c.eRows.length c.kR c.kL c.target
      fuel ob.1 ob.2.1 ob.2.2)

end MoserWorm.UpperBound.Certificate.Kernel
