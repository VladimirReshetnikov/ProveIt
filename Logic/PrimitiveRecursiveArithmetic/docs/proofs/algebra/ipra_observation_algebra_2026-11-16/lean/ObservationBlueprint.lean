/-!
Blueprint (NOT COMPILED): finite-observation algebra targets for ProveIt.
No theorem below is asserted via axiom/sorry; the missing theorems are
represented in comments. This file is a dependency specification, not proof.

Dependencies to implement in actual ProveIt checkout:
  import IPRADerivations.Core.LinearAlgebra
  import IPRADerivations.Core.Search
  import IPRADerivations.Core.MultiSums
  import IPRADerivations.Core.Definitions

At host level, start with the following pure mathematical data:
  f : Fin (d+1) -> Int, with f ⟨d, _⟩ = 1
  companion f : Matrix (Fin d) (Fin d) Int
  evalMat g B : Matrix (Fin d) (Fin d) Int
  obs f g : Fin (d+1) -> Int,
    coefficients of det (T*I - evalMat g (companion f)).

Required theorem sequence, as *object-language* goals:
  1. companion_defining_relation
     matrixPolynomial f (companion f) = 0
  2. companion_charpoly
     det (T*I - companion f) = f(T)
  3. matrix_eval_comp
     evalMat (compose h g) M = evalMat h (evalMat g M)
  4. obs_comp
     obs f (compose h g) = coefficients of det (T*I - evalMat h (evalMat g M))
  5. newton_no_division
     p_k - e_1*p_(k-1) + ... + (-1)^k*k*e_k = 0
  6. obs_precision_transfer
     fixed polynomial circuit with explicitly calculated rational bounds

Every theorem should eventually be represented by a term with type
  ([] : List (Fm PTm n)) ⊢[PRAAx] φ
for a concrete open quantifier-free object formula φ.

Construct characteristic coefficients using bounded determinant expansion
instead of invoking an ambient mathlib theorem; ambient calculations may
help generate proofs but are not the proofs in PRAAx.
-/

namespace ObservationBlueprint

/-- Constant-size semantic illustration; object-level coding is pending. -/
def quadraticCompanion (c : Int) : (Fin 2 → Fin 2 → Int) :=
  fun i j => if i = 0 && j = 1 then c else if i = 1 && j = 0 then 1 else 0

/-- For Y²=c, its characteristic polynomial has coefficient vector (-c,0,1). -/
def quadraticCoefficients (c : Int) : Fin 3 → Int :=
  fun i => if i = 0 then -c else if i = 2 then 1 else 0

/-- The square of the quotient generator acts as scalar multiplication by c. -/
def squareObservationCoefficients (c : Int) : Fin 3 → Int :=
  fun i => if i = 0 then c*c else if i = 1 then -(2*c) else 1

-- These definitions are ordinary Lean functions and can support unit tests.
-- Their equality to determinant constructions must be proved, first at
-- host level and subsequently within the embedded PRAAx calculus.

end ObservationBlueprint
