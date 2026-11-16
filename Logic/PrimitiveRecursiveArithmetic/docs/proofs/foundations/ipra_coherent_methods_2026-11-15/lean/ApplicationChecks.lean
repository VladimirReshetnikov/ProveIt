import ApplicationTargets
import WeightedNormTargets

/-! A kernel-reduced modular example and exact rational executable checks.
These test particular inputs, not the general `...Goal` propositions. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace IPRAFramework.ApplicationChecks

open FiniteAlgebra

def residue64 (n : Nat) : Fin 64 := ⟨n % 64, Nat.mod_lt _ (by decide)⟩

def scalarTerm {R : Type} (c : R) (n : Nat) : Monomial R 1 :=
  { coefficient := c, exponents := Vector.replicate 1 n }

def compositePolynomial : System (Fin 64) 1 :=
  Vector.replicate 1
    [scalarTerm (residue64 62) 0, scalarTerm (residue64 63) 1,
      scalarTerm (residue64 1) 3]

def compositeRoot : Point (Fin 64) 1 :=
  residueProducer 4 3 (by decide) compositePolynomial
    (Vector.replicate 1 (residue64 2))
    (Vector.replicate 1 (Vector.replicate 1 (residue64 3)))

theorem compositeRoot_eq : (compositeRoot.get 0).val = 22 := by decide

def catalanPolynomial : System (Jet 5) 1 :=
  Vector.replicate 1
    [scalarTerm (jetConstant 5 (-1)) 0, scalarTerm (jetConstant 5 1) 1,
      scalarTerm ((jetOps 5).neg (jetVariable 5)) 2]

def catalanJet : Point (Jet 5) 1 :=
  jetProducer 5 catalanPolynomial (Vector.replicate 1 (jetConstant 5 1))
    (Vector.replicate 1 (Vector.replicate 1 (jetConstant 5 1)))

-- Executed diagnostics, deliberately not presented as kernel proofs.
#eval decide ((catalanJet.get 0).toList = [1, 1, 2, 5, 14])

def mixedCurve : WeightedNorm.Curve :=
  { m := 3, d := 4, c := 1, lower := [[-1, -1], [0, -1]] }

#eval decide (WeightedNorm.norm mixedCurve [[], [1]] = [1, 1, 0, 0, 1])

theorem basis_three_four_eight :
    (WeightedNorm.weightedBasis 3 4 8).length = 6 := by decide

end IPRAFramework.ApplicationChecks

#print axioms IPRAFramework.ApplicationChecks.compositeRoot_eq
