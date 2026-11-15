/-!
# Blueprint for the three construction impossibilities in iPRA

This file is an interface mock, not the completed formalization.

It is intentionally written in ordinary Lean's constructive core and marks each
major object-level iPRA milestone as an `axiom`.  The final three theorems use no
classical reasoning: they merely compose the milestone interfaces.  A completed
project must replace every axiom below by a theorem producing a derivation under
`PRAAx`, and then transport that derivation with `pra_iff_native`.
-/

namespace IPRAConstructionBlueprint

abbrev Code := Nat

/-! ## Coded specifications -/

opaque ValidConstructionTrace : Code -> Prop
opaque CubeDoublingOutput : Code -> Prop
opaque TrisectsSixtyOutput : Code -> Prop
opaque SquaresUnitCircleOutput : Code -> Prop

opaque QuadraticTowerCertificate : Code -> Code -> Prop
opaque IrreducibleCubicInTower : Code -> Prop
opaque NonzeroPolynomialAtPi : Code -> Prop
opaque PiPolynomialRelationFromTrace : Code -> Prop

/-! ## Milestone interfaces to be replaced by object-level proofs -/

/-- Replay a valid trace and compute a quadratic-tower certificate. -/
axiom trace_to_quadraticTower
    (trace : Code) :
    ValidConstructionTrace trace ->
      Exists fun tower => QuadraticTowerCertificate trace tower

/-- A cube-doubling output yields a root of the irreducible cubic X^3 - 2
    inside the extracted power-of-two tower. -/
axiom cube_trace_to_irreducible_cubic
    (trace : Code) :
    ValidConstructionTrace trace ->
    CubeDoublingOutput trace ->
    IrreducibleCubicInTower trace

/-- A 60-degree trisector yields a root of X^3 - 3X - 1 inside the same
    kind of tower. -/
axiom trisect_trace_to_irreducible_cubic
    (trace : Code) :
    ValidConstructionTrace trace ->
    TrisectsSixtyOutput trace ->
    IrreducibleCubicInTower trace

/-- Constructive finite-dimensional degree divisibility: an irreducible cubic
    cannot lie in a field whose Q-dimension is a power of two. -/
axiom no_irreducible_cubic_in_powerTwo_tower
    (trace : Code) :
    IrreducibleCubicInTower trace -> False

/-- A square-circle trace gives a nonzero integer polynomial relation for the
    fixed primitive-recursive Cauchy real pi. -/
axiom square_trace_to_pi_polynomial
    (trace : Code) :
    ValidConstructionTrace trace ->
    SquaresUnitCircleOutput trace ->
    PiPolynomialRelationFromTrace trace

/-- Finitistic Hermite-Lindemann contradiction, formalized in PRAAx. -/
axiom pi_transcendence_ipra
    (trace : Code) :
    PiPolynomialRelationFromTrace trace -> False

/-! ## Final intuitionistic composition -/

theorem cube_doubling_impossible
    (trace : Code)
    (hvalid : ValidConstructionTrace trace)
    (hout : CubeDoublingOutput trace) : False :=
  no_irreducible_cubic_in_powerTwo_tower trace
    (cube_trace_to_irreducible_cubic trace hvalid hout)

theorem trisect_sixty_impossible
    (trace : Code)
    (hvalid : ValidConstructionTrace trace)
    (hout : TrisectsSixtyOutput trace) : False :=
  no_irreducible_cubic_in_powerTwo_tower trace
    (trisect_trace_to_irreducible_cubic trace hvalid hout)

theorem square_circle_impossible
    (trace : Code)
    (hvalid : ValidConstructionTrace trace)
    (hout : SquaresUnitCircleOutput trace) : False :=
  pi_transcendence_ipra trace
    (square_trace_to_pi_polynomial trace hvalid hout)

/-!
## Intended ConciseIPRA bridge

After replacing the milestone axioms by object-level proofs, the endpoint should
have the following shape (names schematic):

```
import ConciseIPRA.NativeBiInterpretation

open LeanProofs.ConciseIPRA

 theorem all_three_pra :
   ([] : List (Fm PTm 0)) |- [PRAAx] allThreeFormula := ...

 theorem all_three_native :
   NPrf [] (NFm.ofPRA allThreeFormula) :=
   (pra_iff_native.mp all_three_pra)
```

The exact notation and direction should be synchronized with the pinned
`NativeBiInterpretation.lean` API.
-/

end IPRAConstructionBlueprint
