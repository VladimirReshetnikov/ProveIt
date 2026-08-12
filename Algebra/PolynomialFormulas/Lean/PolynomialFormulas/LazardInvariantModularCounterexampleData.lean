import Mathlib.Tactic

/-!
# Executable finite data for the modular C6 obstruction

This proof-free module isolates the definitions used by the separately
compiled finite certificates.  Semantic theorems remain in their public
modules.
-/

namespace LeanProofs.PolynomialFormulas.LazardInvariantModularCounterexample

open scoped BigOperators
open Finset

set_option autoImplicit false

/-! ## A finite degree-seven orbit calculation -/

abbrev Exponent := Fin 6 → ℕ
abbrev F3 := ZMod 3

/-- Weak compositions of `total` into `slots` entries. -/
def weakCompositions : (slots total : ℕ) → List (List ℕ)
  | 0, 0 => [[]]
  | 0, _ + 1 => []
  | slots + 1, total =>
      (List.range (total + 1)).flatMap fun first =>
        (weakCompositions slots (total - first)).map (first :: ·)

def exponentOfList (values : List ℕ) : Exponent :=
  fun i => values.getD i.1 0

def degreeExponents (degree : ℕ) : List Exponent :=
  (weakCompositions 6 degree).map exponentOfList

/-- Rotation by `k` places, the regular `C₆` permutation action. -/
def rotateExponent (a : Exponent) (k : ℕ) : Exponent :=
  fun i => a ⟨(i.1 + k) % 6, Nat.mod_lt _ (by decide)⟩

def exponentCode (a : Exponent) : ℕ :=
  ∑ i : Fin 6, a i * 8 ^ i.1

def exponentMin (a b : Exponent) : Exponent :=
  if exponentCode b < exponentCode a then b else a

def cyclicOrbit (a : Exponent) : List Exponent :=
  ((List.range 6).map (rotateExponent a)).eraseDups

def canonicalExponent (a : Exponent) : Exponent :=
  (cyclicOrbit a).foldl exponentMin a

/-- One representative for every cyclic orbit of degree-`d` monomials.
The base-eight code is injective in all degrees used here (`d ≤ 7`). -/
def orbitRepresentatives (degree : ℕ) : List Exponent :=
  ((degreeExponents degree).map canonicalExponent).eraseDups

def addExponent (a b : Exponent) : Exponent :=
  fun i => a i + b i

def elementaryExponents (degree : ℕ) : List Exponent :=
  (degreeExponents degree).filter fun a => ∀ i, a i ≤ 1

def productMonomials (source : Exponent) (elementaryDegree : ℕ) :
    List Exponent :=
  (cyclicOrbit source).flatMap fun a =>
    (elementaryExponents elementaryDegree).map (addExponent a)

def f3OfNat (n : ℕ) : F3 := n

def f3Add (a b : F3) : F3 := a + b
def f3Neg (a : F3) : F3 := -a
def f3Sub (a b : F3) : F3 := a - b
def f3Mul (a b : F3) : F3 := a * b
def f3Inv (a : F3) : F3 := a⁻¹

/-- The coefficient of a target monomial in
`e_i · (the orbit sum of source)`, reduced modulo three. -/
def productCoefficient (source : Exponent) (elementaryDegree : ℕ)
    (target : Exponent) : F3 :=
  f3OfNat ((productMonomials source elementaryDegree).count target)

abbrev Vector3 := List F3

def vectorSub (v w : Vector3) : Vector3 :=
  (List.range (max v.length w.length)).map fun i =>
    f3Sub (v.getD i 0) (w.getD i 0)

def vectorScale (a : F3) (v : Vector3) : Vector3 :=
  v.map (f3Mul a)

def pivotIndex (v : Vector3) : Option ℕ :=
  v.findIdx? (· != 0)

def eliminateBy (v row : Vector3) : Vector3 :=
  match pivotIndex row with
  | none => v
  | some p =>
      let factor := f3Mul (v.getD p 0) (f3Inv (row.getD p 0))
      vectorSub v (vectorScale factor row)

def reduceByBasis (basis : List Vector3) (v : Vector3) : Vector3 :=
  basis.foldl eliminateBy v

def insertBasisVector (basis : List Vector3) (v : Vector3) : List Vector3 :=
  let reduced := reduceByBasis basis v
  match pivotIndex reduced with
  | none => basis
  | some _ => basis ++ [reduced]

/-- Number of pivots returned by the executable elimination procedure.
No semantic rank theorem for this procedure is asserted in this file. -/
def rowRank (rows : List Vector3) : ℕ :=
  (rows.foldl insertBasisVector []).length

abbrev ProductSource := ℕ × Exponent

def productSources (targetDegree : ℕ) : List ProductSource :=
  (List.range (min 6 targetDegree)).flatMap fun k =>
    let elementaryDegree := k + 1
    (orbitRepresentatives (targetDegree - elementaryDegree)).map
      (elementaryDegree, ·)

def productRow (targetDegree : ℕ) (source : ProductSource) : Vector3 :=
  (orbitRepresentatives targetDegree).map fun target =>
    productCoefficient source.2 source.1 target

def productRows (targetDegree : ℕ) : List Vector3 :=
  (productSources targetDegree).map (productRow targetDegree)

def invariantOrbitCount (degree : ℕ) : ℕ :=
  (orbitRepresentatives degree).length

def executableProductPivotCount (degree : ℕ) : ℕ :=
  rowRank (productRows degree)

def executableCodimensionDiagnostic (degree : ℕ) : ℕ :=
  invariantOrbitCount degree - executableProductPivotCount degree
/-! ## The Hilbert numerator forced by graded freeness -/

def elementaryWeight (a : Exponent) : ℕ :=
  ∑ i : Fin 6, (i.1 + 1) * a i

/-- Dimension in degree `d` of the polynomial coefficient ring
`𝔽₃[e₁,…,e₆]`, where `deg(e_i)=i`. -/
def symmetricMonomialCount (degree : ℕ) : ℕ :=
  ((List.range (degree + 1)).flatMap degreeExponents |>.filter
    fun a => elementaryWeight a = degree).length

def appendForcedFreeCount (counts : List ℕ) (degree : ℕ) : List ℕ :=
  let oldContribution := (List.range counts.length).foldl
    (fun total j => total + counts.getD j 0 *
      symmetricMonomialCount (degree - j)) 0
  counts ++ [invariantOrbitCount degree - oldContribution]

def forcedFreeGeneratorCountsUpTo (degree : ℕ) : List ℕ :=
  (List.range (degree + 1)).foldl appendForcedFreeCount []

def forcedFreeGeneratorCount (degree : ℕ) : ℕ :=
  (forcedFreeGeneratorCountsUpTo degree).getD degree 0

end LeanProofs.PolynomialFormulas.LazardInvariantModularCounterexample
