import PolynomialFormulas.GaussianPolynomialApproximationCore
import PolynomialFormulas.GaussianPolynomialContractionCertificate

/-!
# Exhaustive rational search for quartic root certificates

`RawCertificate` contains four bounded monic factors and four proposed root
centers for each factor.  Its validity test uses only finite data and exact
Gaussian-rational arithmetic.  A proof that some certificate is valid turns
the exhaustive decoding of natural numbers into a terminating executable
search.
-/

namespace LeanProofs.PolynomialFormulas

namespace GaussianPolynomialApproximationSearch

open GaussianPolynomialApproximationCore
open GaussianPolynomialApproximationCore.QPoly
open GaussianPolynomialContractionCertificate

/-- Four bounded factors, each supplied with four possible root centers. -/
structure RawCertificate where
  factors : Fin 4 → QPoly4
  centers : Fin 4 → Fin 4 → GaussianRat
deriving DecidableEq, Encodable

/-- The harmless decoded value used for malformed natural-number codes. -/
def defaultRawCertificate : RawCertificate where
  factors := fun _ => one 4
  centers := fun _ _ => 0

instance : Inhabited RawCertificate := ⟨defaultRawCertificate⟩

/-- Product of all four degree-at-most-four factors. -/
def factorProduct (raw : RawCertificate) : QPoly 16 :=
  by
    simpa only [Nat.reduceAdd] using
      mul (mul (raw.factors 0) (raw.factors 1))
        (mul (raw.factors 2) (raw.factors 3))

/-- Exact coefficient comparison of the product with the input, including all
coefficients from degree zero through degree sixteen. -/
def ProductMatches (p : QPoly4) (raw : RawCertificate) : Prop :=
  ∀ i : Fin 17, factorProduct raw i = coeff p i

/-- Sum of the four actual factor degrees. -/
def factorDegreeSum (raw : RawCertificate) : ℕ :=
  degree (raw.factors 0) + degree (raw.factors 1) +
    degree (raw.factors 2) + degree (raw.factors 3)

/-- A center slot is active exactly when its index is below the actual degree
of its factor. -/
def Active (raw : RawCertificate) (i j : Fin 4) : Prop :=
  (j : ℕ) < degree (raw.factors i)

instance decidableActive (raw : RawCertificate) (i j : Fin 4) :
    Decidable (Active raw i j) :=
  inferInstanceAs (Decidable ((j : ℕ) < degree (raw.factors i)))

/-- Automatically computed contraction radius of a center slot. -/
def radius (raw : RawCertificate) (i j : Fin 4) : ℚ :=
  newtonRadius (raw.factors i) (raw.centers i j)

/-- A fully rational certificate.  Every quantified index has a finite type,
so this proposition has an executable decision procedure. -/
structure IsValid (p : QPoly4) (ε : ℚ) (raw : RawCertificate) : Prop where
  monicFactors : ∀ i : Fin 4, leadingCoeff (raw.factors i) = 1
  productMatches : ProductMatches p raw
  degreeSum : factorDegreeSum raw = degree p
  activeAutoValid : ∀ i j : Fin 4, Active raw i j →
    AutoValid (raw.factors i) (raw.centers i j)
  activeAccuracy : ∀ i j : Fin 4, Active raw i j →
    2 * radius raw i j ≤ ε
  activeSeparated : ∀ i j j' : Fin 4,
    Active raw i j → Active raw i j' → j ≠ j' →
      radius raw i j + radius raw i j' <
        GaussianRat.linf (raw.centers i j - raw.centers i j')

/-- Boolean validity test, evaluating only finite comparisons and rational
arithmetic. -/
def valid (p : QPoly4) (ε : ℚ) (raw : RawCertificate) : Bool :=
  decide (∀ i : Fin 4, leadingCoeff (raw.factors i) = 1) &&
  decide (∀ i : Fin 17, factorProduct raw i = coeff p i) &&
  decide (factorDegreeSum raw = degree p) &&
  decide (∀ i j : Fin 4, Active raw i j →
    autoValid (raw.factors i) (raw.centers i j) = true) &&
  decide (∀ i j : Fin 4, Active raw i j → 2 * radius raw i j ≤ ε) &&
  decide (∀ i j j' : Fin 4,
    Active raw i j → Active raw i j' → j ≠ j' →
      radius raw i j + radius raw i j' <
        GaussianRat.linf (raw.centers i j - raw.centers i j'))

@[simp] theorem valid_eq_true (p : QPoly4) (ε : ℚ) (raw : RawCertificate) :
    valid p ε raw = true ↔ IsValid p ε raw := by
  simp only [valid, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨⟨⟨⟨hmonic, hproduct⟩, hdegree⟩, hauto⟩, haccuracy⟩, hseparated⟩
    refine ⟨hmonic, hproduct, hdegree, ?_, haccuracy, hseparated⟩
    intro i j hactive
    exact (autoValid_eq_true _ _).mp (hauto i j hactive)
  · rintro ⟨hmonic, hproduct, hdegree, hauto, haccuracy, hseparated⟩
    refine ⟨⟨⟨⟨⟨hmonic, hproduct⟩, hdegree⟩, ?_⟩, haccuracy⟩, hseparated⟩
    intro i j hactive
    exact (autoValid_eq_true _ _).mpr (hauto i j hactive)

/-! ## Exhaustive coding and search -/

/-- Decode a natural number as a possible raw certificate. -/
def decodeRaw (n : ℕ) : Option RawCertificate :=
  Encodable.decode n

/-- Encode a raw certificate as a natural number. -/
def encodeRaw (raw : RawCertificate) : ℕ :=
  Encodable.encode raw

/-- Total enumeration: malformed codes denote `defaultRawCertificate`. -/
def rawAt (n : ℕ) : RawCertificate :=
  (decodeRaw n).getD defaultRawCertificate

@[simp] theorem rawAt_encodeRaw (raw : RawCertificate) :
    rawAt (encodeRaw raw) = raw := by
  simp [rawAt, decodeRaw, encodeRaw]

theorem rawAt_surjective : Function.Surjective rawAt := by
  intro raw
  exact ⟨encodeRaw raw, rawAt_encodeRaw raw⟩

/-- Exact root used by the fast seed when `p` is monic linear.  For other
degrees this harmless rational is simply ignored or rejected. -/
def linearSeedCenter (p : QPoly4) : GaussianRat :=
  -coeff p 0 / coeff p 1

/-- Input-dependent first candidate.  It is already valid for monic constant
and linear polynomials, making those common cases terminate before the generic
enumeration begins. -/
def seedRaw (p : QPoly4) : RawCertificate where
  factors := ![p, one 4, one 4, one 4]
  centers := fun i j => if i = 0 ∧ j = 0 then linearSeedCenter p else 0

/-- A second fast seed tries the four small rational centers
`1, -1, 2, -2`.  It makes common split quadratic and quartic examples execute
immediately while remaining just another certificate candidate. -/
def smallIntegerSeedRaw (p : QPoly4) : RawCertificate where
  factors := ![p, one 4, one 4, one 4]
  centers := fun i => if i = 0 then ![1, -1, 2, -2] else fun _ => 0

/-- Enumeration with two input-specific seeds followed by every encoded raw
certificate. -/
def candidateAt (p : QPoly4) : ℕ → RawCertificate
  | 0 => seedRaw p
  | 1 => smallIntegerSeedRaw p
  | n + 2 => rawAt n

/-- Boolean predicate tested by the unbounded natural-number search. -/
def validAt (p : QPoly4) (ε : ℚ) (n : ℕ) : Bool :=
  valid p ε (candidateAt p n)

theorem exists_validAt {p : QPoly4} {ε : ℚ}
    (h : ∃ raw, IsValid p ε raw) : ∃ n, validAt p ε n = true := by
  obtain ⟨raw, hraw⟩ := h
  refine ⟨encodeRaw raw + 2, ?_⟩
  rw [validAt, candidateAt, rawAt_encodeRaw, valid_eq_true]
  exact hraw

/-- Index of the first valid decoded certificate.  `Nat.find` executes a
sequential search because `validAt` is decidable. -/
def firstValidIndex (p : QPoly4) (ε : ℚ)
    (h : ∃ raw, IsValid p ε raw) : ℕ :=
  Nat.find (exists_validAt h)

/-- First valid raw certificate in the exhaustive enumeration. -/
def search (p : QPoly4) (ε : ℚ)
    (h : ∃ raw, IsValid p ε raw) : RawCertificate :=
  candidateAt p (firstValidIndex p ε h)

theorem firstValidIndex_spec (p : QPoly4) (ε : ℚ)
    (h : ∃ raw, IsValid p ε raw) :
    validAt p ε (firstValidIndex p ε h) = true := by
  exact Nat.find_spec (exists_validAt h)

theorem search_isValid (p : QPoly4) (ε : ℚ)
    (h : ∃ raw, IsValid p ε raw) :
    IsValid p ε (search p ε h) := by
  rw [← valid_eq_true]
  exact firstValidIndex_spec p ε h

/-! ## Active centers -/

/-- Embed an index below a factor's actual degree into one of its four stored
center slots. -/
def layerSlot (raw : RawCertificate) (i : Fin 4)
    (j : Fin (degree (raw.factors i))) : Fin 4 :=
  ⟨j, lt_of_lt_of_le j.isLt (degree_le_bound (raw.factors i))⟩

@[simp] theorem layerSlot_val (raw : RawCertificate) (i : Fin 4)
    (j : Fin (degree (raw.factors i))) : (layerSlot raw i j : ℕ) = j := rfl

theorem layerSlot_active (raw : RawCertificate) (i : Fin 4)
    (j : Fin (degree (raw.factors i))) : Active raw i (layerSlot raw i j) :=
  j.isLt

/-- The active stored centers for one factor, indexed directly by
`Fin (degree factor)`. -/
def layerCenters (raw : RawCertificate) (i : Fin 4) : List GaussianRat :=
  List.ofFn fun j : Fin (degree (raw.factors i)) =>
    raw.centers i (layerSlot raw i j)

@[simp] theorem layerCenters_length (raw : RawCertificate) (i : Fin 4) :
    (layerCenters raw i).length = degree (raw.factors i) := by
  simp [layerCenters]

/-- Compatibility name for the active centers of one factor. -/
def factorCenters (raw : RawCertificate) (i : Fin 4) : List GaussianRat :=
  layerCenters raw i

theorem factorCenters_length (raw : RawCertificate) (i : Fin 4) :
    (factorCenters raw i).length = degree (raw.factors i) := by
  simp [factorCenters]

/-- All active centers, explicitly concatenated in layer order. -/
def centersList (raw : RawCertificate) : List GaussianRat :=
  layerCenters raw 0 ++ layerCenters raw 1 ++
    layerCenters raw 2 ++ layerCenters raw 3

theorem centersList_length (raw : RawCertificate) :
    (centersList raw).length = factorDegreeSum raw := by
  simp only [centersList, List.length_append, layerCenters_length, factorDegreeSum]

/-- Compatibility name emphasizing that only active slots occur. -/
def activeCentersList (raw : RawCertificate) : List GaussianRat :=
  centersList raw

theorem activeCentersList_length (raw : RawCertificate) :
    (activeCentersList raw).length = factorDegreeSum raw := by
  exact centersList_length raw

/-- A validity proof turns the active-center list into a vector whose length
is exactly the degree of the input polynomial. -/
def activeCentersVector {p : QPoly4} {ε : ℚ} {raw : RawCertificate}
    (h : IsValid p ε raw) : List.Vector GaussianRat (degree p) :=
  ⟨activeCentersList raw, (activeCentersList_length raw).trans h.degreeSum⟩

/-- Root-approximation vector extracted from the first valid certificate. -/
def searchCenters (p : QPoly4) (ε : ℚ)
    (h : ∃ raw, IsValid p ε raw) : List.Vector GaussianRat (degree p) :=
  activeCentersVector (search_isValid p ε h)

end GaussianPolynomialApproximationSearch

end LeanProofs.PolynomialFormulas
