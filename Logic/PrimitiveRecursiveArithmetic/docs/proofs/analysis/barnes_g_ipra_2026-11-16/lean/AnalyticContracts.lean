import Std

/-!
# Certificate interfaces for Barnes-G analysis

These are host-Lean data structures.  They do not quantify over arbitrary
functions inside iPRA.  In the object development, each field is instantiated
by a fixed primitive-recursive symbol and each universal precision statement
is compiled as a theorem schema.

No analytic theorem is asserted here.  The structures make all hidden side
conditions -- compactness, branch choice, apartness, truncation and error --
visible as finite certificate fields.
-/

namespace BarnesGIPRA.Contracts

structure CQ where
  re : Rat
  im : Rat
  deriving Repr, DecidableEq

namespace CQ

def zero : CQ := ⟨0,0⟩
def one : CQ := ⟨1,0⟩
def add (z w : CQ) : CQ := ⟨z.re+w.re,z.im+w.im⟩
def neg (z : CQ) : CQ := ⟨-z.re,-z.im⟩
def sub (z w : CQ) : CQ := add z (neg w)
def mul (z w : CQ) : CQ :=
  ⟨z.re*w.re-z.im*w.im,z.re*w.im+z.im*w.re⟩
def conj (z : CQ) : CQ := ⟨z.re,-z.im⟩
def norm1 (z : CQ) : Rat :=
  (if z.re < 0 then -z.re else z.re) +
  (if z.im < 0 then -z.im else z.im)
end CQ

/-- A dyadic complex ball, with radius `2^{-prec}` in the `norm1` metric. -/
structure CBall where
  center : CQ
  prec : Nat
  deriving Repr

/-- Host-level presentation of a fixed primitive-recursive fast Cauchy name. -/
structure FastName where
  approx : Nat → CQ
  regular : ∀ p, CQ.norm1 (CQ.sub (approx (p+1)) (approx p)) ≤ (1 : Rat) / 2^p

/-- Quantitative nonzeroness: at precision `p`, a lower dyadic bound is known. -/
structure ApartCert (z : FastName) where
  witnessPrec : Nat
  lowerNumerator : Nat
  positive : 0 < lowerNumerator
  -- Object-level meaning: |z| >= lowerNumerator / 2^witnessPrec.

/-- A compact disc requested by rational data. -/
structure Disc where
  center : CQ
  radius : Rat
  radiusNonneg : 0 ≤ radius

/-- A continuation path together with a rational separation from a branch cut. -/
structure BranchPath where
  vertices : List CQ
  cutGap : Rat
  cutGapPos : 0 < cutGap

/-- The elementary canonical logarithmic factor
`q_k(z)=k Log(1+z/k)-z+z^2/(2k)` is not evaluated here; this
structure records the finite theorem needed by the product compiler. -/
structure ProductTailCert where
  R : Nat
  N : Nat
  p : Nat
  large : 2*R ≤ N
  bound : 2 * R^3 * 2^(p+2) ≤ 3*N
  -- Consequence proved in the paper: sum_{k>N}|q_k(z)| ≤ 2^{-p}
  -- uniformly for |z|≤R.

/-- Taylor tail on |z|≤rhoNum/rhoDen<1. -/
structure TaylorTailCert where
  rhoNum rhoDen : Nat
  M p : Nat
  denPos : 0 < rhoDen
  inside : rhoNum < rhoDen
  -- Finite cross-multiplied version of
  -- 2 rho^(M+1)/((M+1)(1-rho)) <= 2^{-p}.
  clearedBound :
    2 * rhoNum^(M+1) * rhoDen * 2^p ≤
      (M+1) * (rhoDen-rhoNum) * rhoDen^(M+1)

/-- Fixed-order, fixed-sector asymptotic request. -/
structure AsymptoticRequest where
  order : Nat
  precision : Nat
  radiusLower : Nat
  sectorNumerator sectorDenominator : Nat
  sectorGapPos : 0 < sectorNumerator
  sectorDenPos : 0 < sectorDenominator

/-- A finite-query normal-form contract, matching ProveIt's framework. -/
structure FQNF where
  Query : Type
  Cert : Type
  pre : Query → Bool
  budget : Query → Nat
  verify : Cert → Query → Bool
  goal : Cert → Query → Bool
  producer : Query → Cert
  producerValid : ∀ q, pre q = true → verify (producer q) q = true
  sound : ∀ c q, verify c q = true → goal c q = true

/-- Dependency bundle for a constructive Barnes-G evaluator. -/
structure BarnesGDependencies where
  gammaName : FastName
  eulerConstant : FastName
  piName : FastName
  logTwoPi : FastName
  glaisherA : FastName
  expEvaluator : FQNF
  logEvaluator : FQNF
  gammaEvaluator : FQNF
  productEvaluator : FQNF

end BarnesGIPRA.Contracts
