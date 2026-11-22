import IPRADerivations.Core.Tactic
import IPRADerivations.Core.Evaluation
import IPRADerivations.Core.Search
import IPRADerivations.Core.PolynomialInequalities
import IPRADerivations.Geometry.SphericalTrigonometry

/-!
# Exact object-language endpoint for Platonic projection extrema

STATUS: uncompiled interface. This file states the required proof objects;
it does not pretend to have constructed them. No axiom or sorry is introduced.

Use inside ProveIt, pinned for the source audit at
09fe17194da14cdd100947737952e44100bb71b8.
The imported source modules are not bundled with all transitive dependencies.
Build against the repository workspace, not the small provenance snapshot.
-/

namespace PlatonicProjection.ObjectTarget

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (num)

/-- Programs still to be constructed by the explicit PR coding described in the report. -/
structure Programs where
  /-- One exactly when the input codes three valid Q(phi) elements. -/
  validDirection : PR 1
  /-- Both squared bounds for this direction; the solid data are fixed constants. -/
  directionBounds : PR 1
  /-- All fixed signed-sum, cross-product, span, and attainment checks. -/
  tableCheck : PR 0
  /-- Closed check for the explicitly supplied smallest attaining direction. -/
  minAttainment : PR 0
  /-- Closed check for the explicitly supplied largest attaining direction. -/
  maxAttainment : PR 0

def unary (f : PR 1) (x : PTm n) : PTm n := PTm.app f (fun _ => x)
def closed (f : PR 0) : PTm 0 := PTm.app f Fin.elim0

def boundsOpen (p : Programs) : Fm PTm 1 :=
  (unary p.validDirection (var 0) ≐ num 1) ⟶
    (unary p.directionBounds (var 0) ≐ num 1)

/-- This is the desired universal numerical theorem, not a finite sample statement. -/
def boundsSentence (p : Programs) : Fm PTm 0 := allN 1 (boundsOpen p)

def tableSentence (p : Programs) : Fm PTm 0 := closed p.tableCheck ≐ num 1
def minSentence (p : Programs) : Fm PTm 0 := closed p.minAttainment ≐ num 1
def maxSentence (p : Programs) : Fm PTm 0 := closed p.maxAttainment ≐ num 1

/-- A completed development must construct this record for every one of the five tables. -/
structure CompletedDerivations (p : Programs) where
  tables : ([] : List (Fm PTm 0)) ⊢[PRAAx] tableSentence p
  bounds : ([] : List (Fm PTm 0)) ⊢[PRAAx] boundsSentence p
  minimum : ([] : List (Fm PTm 0)) ⊢[PRAAx] minSentence p
  maximum : ([] : List (Fm PTm 0)) ⊢[PRAAx] maxSentence p

/-!
Completion sequence:
1. Implement signed integers, positive-denominator rationals, and Golden pairs as
   numerical codes. Define +,-,*, inverse, comparison, dot, cross, finite sums,
   mask bits, and the fixed table programs. Prove exact encoding correspondence.
2. Derive order laws by the sign cases in the arithmetic section of report.tex; prove the squarefree-5
   lemma by the explicitly clocked descent. The existing QuadraticExtension
   module supplies ring identities but does not supply the ordered-field result.
3. Compile the Lagrange and barycentric variance identities with derive_rel.
   Preserve denominator nonzero/positivity guards on every rational division.
4. Derive bounded scans and the two-stage cone splitting invariant. All bounded
   universal assertions become zero sums of failure indicators before QF induction.
5. Derive the universal implication tableSentence -> boundsSentence, using the
   sign selector, signed-sum bound, and cone decomposition; no real sign test occurs.
6. Use eval_ground/eval_closed, or generated polynomial certificates, for the
   closed table and attaining-direction checks; compose to obtain bounds.
7. Separately prove the finite polygonal geometry bridge and effective modulus.
   For each fixed PR name, specialize the numerical theorem at its finite queries.
8. Audit #print axioms on each completed proof and use pra_iff_native only after
   the ordinary Prf PRAAx object derivation has been constructed.
-/

end PlatonicProjection.ObjectTarget
