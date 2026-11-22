/- Exact certificate arithmetic and its kernel-checked proof interface. -/
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Rat.BigOperators
import Mathlib.Tactic.NormNum

namespace MoserWorm.UpperBound.Certificate

/-- Rational plane vector. -/
abbrev Q2 := ℚ × ℚ

@[inline] def qdot (u v : Q2) : ℚ := u.1 * v.1 + u.2 * v.2
@[inline] def qcross (u v : Q2) : ℚ := u.1 * v.2 - u.2 * v.1
@[inline] def qadd (u v : Q2) : Q2 := (u.1 + v.1, u.2 + v.2)
@[inline] def qsub (u v : Q2) : Q2 := (u.1 - v.1, u.2 - v.2)
@[inline] def qsmul (c : ℚ) (u : Q2) : Q2 := (c * u.1, c * u.2)
@[inline] def qnorm2 (u : Q2) : ℚ := u.1 * u.1 + u.2 * u.2

/-- `((1 - t²)/(1 + t²), 2t/(1 + t²))`: exact rational unit vector. -/
def unitFromHalftan (t : ℚ) : Q2 :=
  ((1 - t * t) / (1 + t * t), 2 * t / (1 + t * t))

/-! ### The fixed quadrilateral -/

/-- Half-angle parameters of the four normals. -/
def tLit : Fin 4 → ℚ := ![-631/58, -1, 7/16, 37/56]
/-- Offsets of the four supporting lines. -/
def hLit : Fin 4 → ℚ := ![0, 0, 130783/250000, 446199/1000000]
/-- The four outward normals (computed from `tLit`). -/
def nLit (i : Fin 4) : Q2 := unitFromHalftan (tLit i)

/-- Ray `a = (a₀, a₁, 1, 0)` of (K2). -/
def rayA : Fin 4 → ℚ := ![5541045/8027539, 24427652/40137695, 1, 0]
/-- Ray `b = (b₀, b₁, 0, 1)` of (K2). -/
def rayB : Fin 4 → ℚ := ![47299645/118570699, 502233812/592853495, 0, 1]

/-- The two rays as a function of the ray index (0 = a, 1 = b). -/
def ray (r : Fin 2) : Fin 4 → ℚ := if r = 0 then rayA else rayB

/-- Support of ray r: indices with positive coefficient. -/
def raySupp (r : Fin 2) : List (Fin 4) :=
  if r = 0 then [0, 1, 2] else [0, 1, 3]

/-- Escape constants: `D_a = Σ a_i h_i = h_2`, `D_b = h_3`. -/
def Dray (r : Fin 2) : ℚ := if r = 0 then hLit 2 else hLit 3

/-! ### Placements -/

/-- A placement spec, as in the certificate: `flush s flip mirror`,
`rot t mirror`, `vrot t mirror`. -/
inductive PSpec
  | flush (s : Fin 4) (flip : Bool) (mir : Bool)
  | rot (t : ℚ) (mir : Bool)
  | vrot (t : ℚ) (mir : Bool)
deriving Repr, DecidableEq, Inhabited

def PSpec.isReal : PSpec → Bool
  | .vrot _ _ => false
  | _ => true

/-- 2×2 rational matrix, rows (a b; c d) as ((a,b),(c,d)). -/
abbrev QMat := Q2 × Q2

@[inline] def mApply (M : QMat) (v : Q2) : Q2 :=
  (M.1.1 * v.1 + M.1.2 * v.2, M.2.1 * v.1 + M.2.2 * v.2)

/-- Mirror `x ↦ -x` composed AFTER the rotation: negates the first row. -/
@[inline] def mMirror (M : QMat) : QMat := ((-M.1.1, -M.1.2), M.2)

/-- The exact matrix of an orientation specification. -/
def specMap : PSpec → QMat
  | .flush s flip mir =>
      let n := nLit s
      let R : QMat := if flip then ((n.2, -n.1), (n.1, n.2))
                      else ((-n.2, n.1), (-n.1, -n.2))
      if mir then mMirror R else R
  | .rot t mir | .vrot t mir =>
      let c := (unitFromHalftan t).1
      let s := (unitFromHalftan t).2
      let R : QMat := ((c, -s), (s, c))
      if mir then mMirror R else R

/-- Exact orthogonality test. -/
def isOrtho (M : QMat) : Bool :=
  M.1.1 * M.1.1 + M.2.1 * M.2.1 == 1 &&
  M.1.2 * M.1.2 + M.2.2 * M.2.2 == 1 &&
  M.1.1 * M.1.2 + M.2.1 * M.2.2 == 0

/-- The four directions `u^M_i = M n_i` of a spec. -/
def specDirs (p : PSpec) : Fin 4 → Q2 := fun i => mApply (specMap p) (nLit i)

/-! ### Labels

Directions of REAL placements only.  `N^R` = directions with x > 0 sorted by
increasing y; `N^L` = x < 0 sorted by decreasing y; vertical must be (0, ±1).
-/

/-- Insert into a sorted list w.r.t. a strict comparator, no deduplication. -/
def insertSorted (lt : Q2 → Q2 → Bool) (u : Q2) : List Q2 → List Q2
  | [] => [u]
  | v :: rest => if lt u v then u :: v :: rest else v :: insertSorted lt u rest

structure LabelTables where
  kR : ℕ
  kL : ℕ
  right : Array Q2   -- R_0 .. R_{kR-1}, increasing y
  left : Array Q2    -- L_0 .. L_{kL-1}, decreasing y
deriving Repr

/-- Total number of labels. -/
def LabelTables.nLab (T : LabelTables) : ℕ := 3 + T.kR + T.kL

/-- The direction of a label (for S-rows): F- and F+ ↦ (0,-1), C ↦ (0,1). -/
def LabelTables.normalOf (T : LabelTables) (l : ℕ) : Q2 :=
  if l == 0 then (0, -1)
  else if l == 1 then (0, -1)
  else if l == 2 then (0, 1)
  else if l < 3 + T.kR then T.right.getD (l - 3) (0, 0)
  else T.left.getD (l - 3 - T.kR) (0, 0)

/-- Label of a direction u (with the convention `lab (0,-1) = F+ = 1`),
`none` if u is not a named direction. -/
def LabelTables.labOf (T : LabelTables) (u : Q2) : Option ℕ :=
  if u == ((0 : ℚ), (-1 : ℚ)) then some 1
  else if u == ((0 : ℚ), (1 : ℚ)) then some 2
  else if u.1 > 0 then
    (T.right.findIdx? (· == u)).map (3 + ·)
  else
    (T.left.findIdx? (· == u)).map (3 + T.kR + ·)

/-- Build the label tables from the list of specs; `none` if a vertical
direction other than (0, ±1) occurs. Collect the directions of real
placements, remove duplicates, and sort each half-plane. -/
def buildLabels (specs : List PSpec) : Option LabelTables := Id.run do
  let mut dirs : List Q2 := []
  for p in specs do
    if p.isReal then
      for i in [0, 1, 2, 3] do
        let u := specDirs p ⟨i % 4, by omega⟩
        if !dirs.contains u then dirs := u :: dirs
  -- vertical check
  for u in dirs do
    if u.1 == 0 && !(u == ((0 : ℚ), (-1 : ℚ)) || u == ((0 : ℚ), (1 : ℚ))) then
      return none
  let rightL := dirs.filter (fun u => u.1 > 0)
  let leftL := dirs.filter (fun u => u.1 < 0)
  let right := (rightL.foldl (fun acc u => insertSorted (fun a b => a.2 < b.2) u acc) []).toArray
  let left := (leftL.foldl (fun acc u => insertSorted (fun a b => a.2 > b.2) u acc) []).toArray
  return some { kR := right.size, kL := left.size, right, left }

/-! ### Angular order (exact), for virtual-placement decomposition

Angles in [0, 2π) as produced by `atan2(y,x) % 2π`: sector 0 = positive x-axis,
sector 1 = upper half (y > 0), sector 2 = negative x-axis, sector 3 = lower
half (y < 0); within sectors 1 and 3, `u` before `v` iff `cross u v > 0`.
-/

def sector (u : Q2) : ℕ :=
  if u.2 == 0 then (if u.1 > 0 then 0 else 2)
  else if u.2 > 0 then 1 else 3

/-- Exact "angle of u < angle of v" (angles in [0,2π)). -/
def angLt (u v : Q2) : Bool :=
  let su := sector u
  let sv := sector v
  if su ≠ sv then su < sv
  else qcross u v > 0

/-- All named directions (labels 1..nLab-1, i.e. every label except F-,
which shares its direction with F+), sorted by angle. -/
def namedByAngle (T : LabelTables) : Array Q2 := Id.run do
  let mut all : List Q2 := [((0 : ℚ), (-1 : ℚ)), ((0 : ℚ), (1 : ℚ))]
  for u in T.right do all := u :: all
  for u in T.left do all := u :: all
  return (all.foldl (fun acc u => insertSorted angLt u acc) []).toArray

/-- Decompose `u` as `α·w₁ + β·w₂` on the two named directions adjacent in
cyclic angular order (or `[(u, 1)]` if u is itself named).
Returns `none` when the exact checks fail (degenerate/negative decomposition).
-/
def decompose (T : LabelTables) (named : Array Q2) (u : Q2) :
    Option (List (Q2 × ℚ)) :=
  if (T.labOf u).isSome then some [(u, 1)]
  else
    -- i2 = first index (cyclically) with angle(named[i2]) > angle(u)
    let n := named.size
    if _h : n = 0 then none else
    let i2 := (named.findIdx? (fun w => angLt u w)).getD 0
    let i1 := (i2 + n - 1) % n
    let w1 := named.getD i1 (0, 0)
    let w2 := named.getD i2 (0, 0)
    let det := qcross w1 w2
    if det == 0 then none
    else
      let α := qcross u w2 / det
      let β := qcross w1 u / det
      if α ≥ 0 && β ≥ 0 &&
         α * w1.1 + β * w2.1 == u.1 && α * w1.2 + β * w2.2 == u.2 then
        some [(w1, α), (w2, β)]
      else none

/-! ### Rows

A row is a linear inequality `Σ_l ⟨coeff l, P_l⟩ + const ≥ 0` over the points
`P_0 .. P_{nLab-1}`.  We keep coefficients as an association list
(label, vector); repeated labels are summed on interpretation.
-/

structure RowData where
  coeffs : List (ℕ × Q2)
  const : ℚ
deriving Repr

/-- S-row for ordered pair of distinct labels (d, P):
`⟨P_d - P_P, dir d⟩ ≥ 0`. -/
def rowS (T : LabelTables) (d P : ℕ) : RowData :=
  let nd := T.normalOf d
  { coeffs := [(d, nd), (P, (-nd.1, -nd.2))], const := 0 }

/-- N-row: `x(P_{F+}) - x(P_{F-}) ≥ 0`. -/
def rowN : RowData :=
  { coeffs := [(1, ((1 : ℚ), (0 : ℚ))), (0, ((-1 : ℚ), (0 : ℚ)))], const := 0 }

/-- E-row of a spec (real or virtual) for ray r:
`Σ_{i ∈ supp r} λ_i ⟨decomposed contact coeffs⟩ - D_r ≥ 0`.
`none` if a direction is unnamed (real) or the decomposition fails (virtual),
or the coefficient sum does not vanish. -/
def rowEPieces (T : LabelTables) (named : Array Q2) (p : PSpec) (r : Fin 2)
    (i : Fin 4) : Option (List (ℕ × Q2)) :=
  let u := specDirs p i
  match p with
  | .vrot _ _ =>
      (decompose T named u).bind fun parts =>
        parts.mapM (fun wc =>
          (T.labOf wc.1).map (fun l => (l, qsmul (ray r i * wc.2) wc.1)))
  | _ => (T.labOf u).map (fun l => [(l, qsmul (ray r i) u)])

/-- E-row of a spec (real or virtual) for ray r; `none` if a direction is
unnamed (real) or the decomposition fails (virtual), or the coefficient sum
does not vanish. -/
def rowE (T : LabelTables) (named : Array Q2) (p : PSpec) (r : Fin 2) :
    Option RowData :=
  ((raySupp r).mapM (rowEPieces T named p r)).bind fun pieces =>
    let coeffs := pieces.flatten
    let s := coeffs.foldl (fun acc lv => qadd acc lv.2) ((0 : ℚ), (0 : ℚ))
    if s = ((0 : ℚ), (0 : ℚ)) then some ⟨coeffs, -(Dray r)⟩ else none

/-- Sanity of the label tables, checked at run time so that soundness proofs
can read the properties off the boolean: right directions have x > 0, unit
norm and strictly increasing y; left directions x < 0, unit norm, strictly
decreasing y. -/
def labelsOK (T : LabelTables) : Bool :=
  (List.range T.kR).all (fun i =>
    let u := T.right.getD i (0, 0)
    decide (0 < u.1) && decide (qnorm2 u = 1)) &&
  (List.range (T.kR - 1)).all (fun i =>
    decide ((T.right.getD i (0, 0)).2 < (T.right.getD (i + 1) (0, 0)).2)) &&
  T.right.size == T.kR &&
  (List.range T.kL).all (fun j =>
    let u := T.left.getD j (0, 0)
    decide (u.1 < 0) && decide (qnorm2 u = 1)) &&
  (List.range (T.kL - 1)).all (fun j =>
    decide ((T.left.getD (j + 1) (0, 0)).2 < (T.left.getD j (0, 0)).2)) &&
  T.left.size == T.kL

/-! ### The prefix-set family of Lemma 3.7 and cumulative sums -/

/-- Force accumulation state: total coefficient vector per label. -/
abbrev Forces := Array Q2

/-- `familyMaxNorm2 C rect`: max over S ∈ F(rect) of |Σ_{l∈S} C_l|², by exact
cumulative sums. `C` is indexed by label. -/
def familyMaxNorm2 (T : LabelTables) (C : Forces)
    (pLo pHi qLo qHi : ℕ) : ℚ := Id.run do
  let k := T.kR
  let m := T.kL
  -- cumulative sums over L (A) and R (B)
  let mut A : Array Q2 := Array.mkEmpty (m + 1)
  A := A.push (0, 0)
  for i in [0:m] do
    A := A.push (qadd (A.getD i (0,0)) (C.getD (3 + k + i) (0,0)))
  let mut B : Array Q2 := Array.mkEmpty (k + 1)
  B := B.push (0, 0)
  for i in [0:k] do
    B := B.push (qadd (B.getD i (0,0)) (C.getD (3 + i) (0,0)))
  let Fm := C.getD 0 (0,0)
  let Fp := C.getD 1 (0,0)
  let mut best : ℚ := 0
  let upd := fun (best : ℚ) (v : Q2) =>
    let n2 := qnorm2 v
    if n2 > best then n2 else best
  -- (i) left middle runs {L_a..L_b}, qLo ≤ a ≤ b < m (0-based)
  for a in [qLo:m] do
    for b in [a:m] do
      best := upd best (qsub (A.getD (b+1) (0,0)) (A.getD a (0,0)))
  -- (ii) {L_j..L_{m-1}} ∪ {F-}, 0 ≤ j ≤ min(qHi, m)
  for j in [0:(min qHi m)+1] do
    best := upd best (qadd (qsub (A.getD m (0,0)) (A.getD j (0,0))) Fm)
  -- (iii) {P₊, R_0, ..., R_{j-1}}, pLo ≤ j ≤ k
  for j in [pLo:k+1] do
    best := upd best (qadd Fp (B.getD j (0,0)))
  -- (iv) {R_a, ..., R_{b-1}}, 0 ≤ a ≤ b ≤ pHi
  for a in [0:pHi+1] do
    for b in [a:pHi+1] do
      best := upd best (qsub (B.getD b (0,0)) (B.getD a (0,0)))
  return best

end MoserWorm.UpperBound.Certificate
