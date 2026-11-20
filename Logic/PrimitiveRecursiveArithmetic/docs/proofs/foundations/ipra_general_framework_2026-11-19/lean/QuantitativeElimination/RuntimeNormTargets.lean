import IPRADerivations.Analysis.GaussianPolynomialMonicNorm
import IPRADerivations.Analysis.GaussianRationalTranslation
import IPRADerivations.Core.Gcd

/-!
# Explicit targets for completing the runtime norm bridge

STATUS: definitions of proof obligations, NOT proved theorems, and NOT
elaborated in the preparation environment. `Target` below means exactly
an unfilled metatheoretic obligation. No `axiom` or admitted proof is used.

The numerical m is an object term. Replacing it with a host-level
`k : Nat` indexing `Matrix (Fin k) (Fin k)` would change the target.
-/

set_option autoImplicit false

namespace QuantitativeElimination.RuntimeNormTargets

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis
open GaussianRationalHorner (qzero qmul evaluate)
open GaussianRationalSyntheticDivision (qone)
open GaussianRationalMetric (qnegative)
open GaussianPolynomialMonicCompanion (values monicValues)
open GaussianPolynomialMonicNorm (input norm degreeBound)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus pred)

variable {n : ℕ}

def commonZeroFormula (F G m a c x y : PTm n) : Fm PTm n :=
  input F G m a c ⟶
  (evaluate (monicValues F m x) y ≐ qzero) ⟶
  (evaluate (values G m x) y ≐ qzero) ⟶
  (evaluate (norm F G m a c) x ≐ qzero)

/-- Missing runtime-dimensional determinant-kernel implication, with the
matrix generated from the original polynomial data. -/
def CommonZeroNormTarget : Prop :=
  ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (commonZeroFormula (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))

/-- Insert two fresh bound variables. -/
def shiftTwo (t : PTm n) : PTm (n + 2) := Syn.shift (Syn.shift t)

/-- Canonical recoding by multiplication by rational one. The upstream
identifier `canonical` is a formula, not a term-valued normalizer. -/
def recode (q : PTm n) : PTm n := qmul q qone

/-- A row array is descending in Y, and each coefficient row descending
in X. Test semantic zero after canonicalization of the coefficient code.
For row i and slot j the monomial weight is
wx*(c-j)+wy*(m-1-i). -/
def supportAt (F m c wx wy D i j : PTm n) : Fm PTm n :=
  lt i m ⟶ le j c ⟶
  lt D (wx * monus c j + wy * monus (pred m) i) ⟶
  (recode (entry (entry F i) j) ≐ qzero)

/-- Finite weighted support, represented by a formula whose quantifiers
are bounded by the displayed implications. Its Booleanized form is the
required quantifier-free induction invariant. -/
def weightedRows (F m c wx wy D : PTm n) : Fm PTm n :=
  .all (.all (supportAt (shiftTwo F) (shiftTwo m) (shiftTwo c)
    (shiftTwo wx) (shiftTwo wy) (shiftTwo D) (var 1) (var 0)))

/-- P has stored degree cap cap. Its first cap-cutoff descending slots
vanish. This says actual degree <= cutoff, without shrinking its buffer.
If cutoff >= cap the condition is vacuous, as it should be. -/
def leadingZeros (P cap cutoff : PTm n) : Fm PTm n :=
  .all (lt (var 0) (monus (Syn.shift cap) (Syn.shift cutoff)) ⟶
    (recode (entry (Syn.shift P) (var 0)) ≐ qzero))

def weightedDegreeFormula (F G m a c wx wy D : PTm n) : Fm PTm n :=
  input F G m a c ⟶ le one wx ⟶
  weightedRows F m c wx wy (m * wy) ⟶
  weightedRows G m a wx wy D ⟶
  leadingZeros (norm F G m a c) (degreeBound m a c) (quo (m * D) wx)

/-- Sharp weighted support for the actual returned norm, not merely its
coarse storage length. The coefficient convention is fully specified. -/
def WeightedNormDegreeTarget : Prop :=
  ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (weightedDegreeFormula (var 0) (var 1) (var 2) (var 3)
      (var 4) (var 5) (var 6) (var 7))

/-! ## Finite-place Newton data, entirely in existing numeric codecs -/

/-- Coefficient of T^i in P(z+T). The guard i<=cap is part of every
meaningful use. `translated` has descending coefficient order. -/
def localCoefficient (P cap z i : PTm n) : PTm n :=
  entry (GaussianRationalTranslation.translated P cap z) (monus cap i)

/-- Exact finite-place order, including the nonzero leading coefficient.
No infinity-valued valuation and no series object is introduced. -/
def exactOrder (P cap z order leading : PTm n) : Fm PTm n :=
  le order cap ⋏ (neg (recode leading ≐ qzero) ⋏
    ((localCoefficient P cap z order ≐ recode leading) ⋏
      .all (lt (var 0) (Syn.shift order) ⟶
        (localCoefficient (Syn.shift P) (Syn.shift cap) (Syn.shift z) (var 0) ≐ qzero))))

/-- Row carrying the coefficient of Y^j, for j<m. -/
def yRow (F m j : PTm n) : PTm n := entry F (monus (pred m) j)

/-- Every lower nonconstant Y coefficient has strictly larger local
weight than the Newton edge joining Y^m and -c0*T^e. -/
def localStrictAt (F m cap z e j i : PTm n) : Fm PTm n :=
  lt j m ⟶ le one j ⟶ le i cap ⟶
  le (m * i + e * j) (m * e) ⟶
  (localCoefficient (yRow F m j) cap z i ≐ qzero)

def localNewton (F m cap z e c0 : PTm n) : Fm PTm n :=
  le one e ⋏ ((gcd m e ≐ one) ⋏
    (exactOrder (yRow F m zero) cap z e (qnegative c0) ⋏
      .all (.all (localStrictAt (shiftTwo F) (shiftTwo m) (shiftTwo cap)
        (shiftTwo z) (shiftTwo e) (var 1) (var 0)))))

/-- All coefficients of G of weight below s vanish. This is a bounded
coefficient check, not a premise about an unspecified valuation. -/
def lowerWeightAt (G m cap z e s j i : PTm n) : Fm PTm n :=
  lt j m ⟶ le i cap ⟶ lt (m * i + e * j) s ⟶
  (localCoefficient (yRow G m j) cap z i ≐ qzero)

/-- The first nonzero weighted coefficient is b*T^v*Y^k.
The local coprimality m,e makes its pair (v,k) unique among k<m. -/
def firstWeight (G m cap z e s k v b : PTm n) : Fm PTm n :=
  lt k m ⋏ (le v cap ⋏ ((s ≐ m * v + e * k) ⋏
    (neg (recode b ≐ qzero) ⋏
      ((localCoefficient (yRow G m k) cap z v ≐ recode b) ⋏
        .all (.all (lowerWeightAt (shiftTwo G) (shiftTwo m) (shiftTwo cap)
          (shiftTwo z) (shiftTwo e) (shiftTwo s) (var 1) (var 0)))))))

/-- b^m * (((-1)^(m-1))*c0)^k, with the actual Gaussian-rational power
program. The sign belongs to the product of the m conjugate Y values. -/
def localLeading (b c0 m k : PTm n) : PTm n :=
  qmul (GaussianRationalReciprocal.power b m)
    (GaussianRationalReciprocal.power
      (qmul (GaussianRationalReciprocal.power (qnegative qone) (pred m)) c0) k)

/-- The local certificate proves nonvanishing and exact order of the
actual norm. The optional global support assumptions simultaneously
prove a degree bound. All inputs are ordinary finite rational codes. -/
def localNewtonNormFormula (F G m a c z e c0 s k v b d W : PTm n) : Fm PTm n :=
  input F G m a c ⟶
  localNewton F m c z e c0 ⟶
  firstWeight G m a z e s k v b ⟶
  weightedRows F m c m d (m * d) ⟶
  weightedRows G m a m d W ⟶
    (exactOrder (norm F G m a c) (degreeBound m a c) z s (localLeading b c0 m k) ⋏
      leadingZeros (norm F G m a c) (degreeBound m a c) W)

def LocalNewtonNormTarget : Prop :=
  ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 14
    (localNewtonNormFormula (var 0) (var 1) (var 2) (var 3) (var 4)
      (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12) (var 13))

/-
Completion path (see FORMALIZATION.md for loop invariants):

1. Canonical rational row support -> weighted support after one monic
   companion step, via bounded coefficient convolution.
2. QF induction over the original runtime column j, keeping weighted
   support of every stored row after j multiplications by Y.
3. For each numeric permutation word, sum row weights and cancel the
   permutation's sum against the column sum. Bound every product's
   X degree by floor(m*D/wx).
4. QF induction over the actual filtered word scan proves leadingZeros
   for the actual determinant code, using coefficient_leibniz.
5. Separately derive runtime cofactor/row operations or a normalized
   left-kernel determinant lemma; combine returned_zero_action and the
   zero-th evaluation-vector coordinate 1 to prove CommonZeroNormTarget.

Neither target is assumed by an exported theorem in this file.

Additional LocalNewtonNormTarget completion:
* Reuse the actual rational polynomial translation program to obtain
  finite T=X-z coefficients, not a Puiseux-series representation.
* Prove uniqueness of a minimal weight modulo m from gcd(m,e)=1 and k<m.
* Propagate the lowest-weight monomial through companion multiplication.
  At the initial form the relation is Y^m=c0*T^e; all other F terms have
  strictly greater weight.
* In the actual determinant, the unique initial monomial pattern has
  coefficient b^m*((-1)^(m-1)*c0)^k and T order m*v+e*k.
* Booleanized finite-support inductions certify no lower coefficient.
  Gaussian-rational field laws and the displayed nonzero b,c0 certify
  that the leading coefficient is nonzero.
* The independent weighted-degree target supplies the global cap W.
-/

end QuantitativeElimination.RuntimeNormTargets
