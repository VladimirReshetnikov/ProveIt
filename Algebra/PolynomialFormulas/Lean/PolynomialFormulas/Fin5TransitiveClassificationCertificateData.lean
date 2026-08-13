/-
This file is generated.  Do not edit it directly.

Regenerate with `Algebra/PolynomialFormulas/Tools/generate_fin5_transitive_classification_certificates.py` and verify with
`Algebra/PolynomialFormulas/Tools/generate_fin5_transitive_classification_certificates.py --check`.  Python supplies data only; every theorem
below is checked by Lean using ordinary kernel reduction.
-/

import PolynomialFormulas.Fin5DihedralCore
import Mathlib.GroupTheory.SpecificGroups.Alternating

namespace LeanProofs.PolynomialFormulas.Fin5TransitiveClassificationCertificates

open Equiv

abbrev S5 := Fin5DihedralCore.S5
abbrev fiveCycle : S5 := Fin5DihedralCore.fiveCycle
abbrev reflection : S5 := Fin5DihedralCore.reflection
abbrev multiplierTwo : S5 := FrobeniusDummitResolvent.multiplierTwo
abbrev standardC5 : Subgroup S5 := Fin5DihedralCore.standardC5
abbrev standardD5 : Subgroup S5 := Fin5DihedralCore.standardD5
abbrev standardF20 : Subgroup S5 := Fin5Solvable.standardF20
abbrev c5Elements : Finset S5 := Fin5DihedralCore.c5Elements
abbrev d5Elements : Finset S5 := Fin5DihedralCore.d5Elements
abbrev f20Elements : Finset S5 := Fin5TransitiveC5.f20Elements

def evenElements : Finset S5 :=
  Finset.univ.filter (fun g ↦ Equiv.Perm.sign g = 1)

def oddElements : Finset S5 :=
  Finset.univ.filter (fun g ↦ Equiv.Perm.sign g ≠ 1)

inductive GeneratedClass
  | cyclic
  | dihedral
  | frobenius
  | alternating
  | symmetric
  deriving DecidableEq, Fintype, Repr

def classElements : GeneratedClass → Finset S5
  | .cyclic => c5Elements
  | .dihedral => d5Elements
  | .frobenius => f20Elements
  | .alternating => evenElements
  | .symmetric => Finset.univ

/-- One representative for each `C5` double coset in `S5`. -/
def representative : Fin 8 → S5 := ![
    1,
    reflection,
    multiplierTwo,
    multiplierTwo⁻¹,
    Equiv.swap (2 : Fin 5) 3 * Equiv.swap 3 4,
    Equiv.swap (1 : Fin 5) 2 * Equiv.swap 3 4,
    Equiv.swap (3 : Fin 5) 4,
    Equiv.swap (2 : Fin 5) 4]

def representativeClass : Fin 8 → GeneratedClass :=
  ![.cyclic, .dihedral, .frobenius, .frobenius, .alternating, .alternating, .symmetric, .symmetric]

def representativeDepth : Fin 8 → ℕ :=
  ![2, 3, 3, 3, 6, 9, 10, 10]

def representativeDoubleCosetCard : Fin 8 → ℕ :=
  ![5, 5, 5, 5, 25, 25, 25, 25]

/-- The five-class membership bucket used by normalized classification. -/
def elementClass (g : S5) : GeneratedClass :=
  if g ∈ c5Elements then .cyclic
  else if g ∈ d5Elements then .dihedral
  else if g ∈ f20Elements then .frobenius
  else if Equiv.Perm.sign g = 1 then .alternating
  else .symmetric

/-- The finite double coset `C5 * representative i * C5`. -/
def doubleCosetElements (i : Fin 8) : Finset S5 :=
  (Finset.univ : Finset (Fin 5 × Fin 5)).image (fun ab ↦
    fiveCycle ^ (ab.1 : ℕ) * representative i *
      fiveCycle ^ (ab.2 : ℕ))

/-- Injective base-five code on permutations of five letters. -/
def permCode (g : S5) : ℕ :=
  (g 0).val + 5 * (g 1).val + 25 * (g 2).val +
    125 * (g 3).val + 625 * (g 4).val

/-- Reconstruct an explicit finite permutation table from generated codes. -/
def elementsWithCodes (codes : Finset ℕ) : Finset S5 :=
  Finset.univ.filter (fun g ↦ permCode g ∈ codes)

end LeanProofs.PolynomialFormulas.Fin5TransitiveClassificationCertificates
