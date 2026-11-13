# The missing exact 86-parent bridge

The eta-unshift client needs `PolynomialBridge` for the **exact generated
86-operation natural graph**, at `ports K`. This is not the existing
`Natural86Endpoint` for an unrelated 14-variable chain, nor the 87-operation
positive free-J endpoint. No source found in this bounded inventory supplies
the required 86 bridge directly.

The closest documented retained compact endpoint is
`IPRAOrdinary13.expression = (FreeJ13.graph CompactSymbolicModelIff.p).output`,
a 13-positive-input, 87-operation, degree-51 Lean expression. Its source
`IPRAOrdinary13.positiveBridge` is a positive-zero/machine-halts interface;
`IPRAOrdinary12.bridge_of_positive` supplies a `PolynomialBridge` for its
positive shift, and `IPRAExpressionNative.equivalence_of_bridge` supplies the
mapped native proof statement. The retained endpoint's historical author-side
build and external JSON/port binding have not been independently replayed or
fully authenticated here.

For the compact natural tuple, `Residue90CompactTupleDraft.chosen_integer_ports`
is a separate unelaborated proposed equality between `ports chosenKernel`
cast to integers and `CompactSymbolicModelIff.p`. `chosenKernel` is the
symbolic `paramKernel rho`. This source equality does not prove physical
bytes, a PDF, or a different displayed tuple. K is specialized in the
conditional client; the standalone 85-to-86 draft accepts arbitrary K.

The externally reviewed path from the exact 86 graph to the retained endpoint
has the following distinct edges (the row counts identify each literal, not
an already Lean-checked chain):

1. **86 natural → 87 natural:** the 86 graph unshifts w; reverse transport
   needs its own all-model `w>0` proof from the actual signed norms. The
   eta-natural X-zero argument concerns the *85 child* and cannot simply be
   applied to the 86 literal without its own graph binding.
2. **87 natural → 88 natural:** unshifts gamma; reverse transport needs
   all-model gamma positivity, compact rank/window and Pell bounds for the
   actual graph. The current residue-90 gamma client is a different carrier.
3. **88 natural → 89 natural:** unshifts J; reverse transport needs actual
   all-model J positivity and natural K0. The three exact input-shift edits
   are reconstructed and checked by `check.py`; they are not model proofs.
4. **89 natural → positive 80 unit-product:** align the ten shifted inputs,
   then derive or replace the direct f/r/y coordinates as required by the
   all-model zero map. The standard root-switch argument does not by itself
   supply a Lean model transport.
5. **Positive 80 product → positive 81 four-square:** use the four signed
   unit exclusions, actual factor evaluation, sum-of-squares zero and their
   converse in arbitrary IΣ₁ models. External integer proofs are not an
   all-model Lean theorem.
6. **Positive 81 → 83 → 84 → 87/36:** respectively a residue-adjusted first
   carrier and positive-root switch, q*w main-carrier substitution/calibration,
   and q³ first-carrier unscaling. Their sign/quotient/positivity hypotheses
   and both zero directions require exact model-level bindings; the existing
   residue-82/90 source drafts use different literal graphs and do not supply
   these edges automatically.
7. **Positive 87/36 → 88/30 → 88/46 → retained 87/51:** the direct auxiliary
   substitution needs a positive offset and matching actual roots. The
   `ordinary13-freej88-four-square-lean-draft` and `ordinary13-freej88-lean-draft`
   propose the latter two model/source interfaces, but both are explicitly
   unelaborated with unresolved provider/axiom ancestry.

The source `Eta86ConditionalBridge` offers only the strongest honest shortcut:
it assumes a single all-model `SameNoZero` from the exact 86 graph to the
positive-shifted retained 87/51 endpoint, derives the 86 `PolynomialBridge`
from the retained positive bridge, and then composes the existing eta-unshift
client under a second explicit all-model `ForcedEta` premise. It does not
prove any of the seven edges above, assert the assumptions, elaborate Lean,
or equate the native mapped predicate with an arbitrary user-facing ZFC
formula. The chosen tuple source, the endpoint's exact proof-theory adapters,
all graph/provider/axiom provenance, external file bindings and the 85 eta
forcing remain open.

From `Computability/DiophantineConsistency`, run
`python3 -I -S -B research/ordinary13-eta86-parent-bridge-inventory/check.py`
and compare with `receipt.json`. The check pins every listed actual graph,
validates the three initial shift edits and source-level bridge signatures,
and does not run Lean.
