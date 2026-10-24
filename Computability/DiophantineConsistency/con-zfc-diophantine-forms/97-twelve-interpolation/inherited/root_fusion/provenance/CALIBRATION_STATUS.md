# Calibration status: ordinary theorem, external endpoint, and encoded ZFC proof

## The theorem used by this packet

Let `Source34` denote the precisely instantiated native source with the six fixed native/cone coefficients bound in this packet, and let `P` be one of the new integer polynomials. The new reduction proves, by ordinary mathematics available in ZFC,

    ZFC proves: (exists integer x, P(x)=0)
                iff (exists source witness u, Source34(u)).

The claimed final equivalence is obtained by composing that theorem with two explicitly imported ordinary results:

    ZFC proves: (exists source witness u, Source34(u))
                iff Halt(K215,blank);

    ZFC proves: Halt(K215,blank)
                iff (exists p, Proof_ZFC(p,contradiction)).

Here `Proof_ZFC` is the standard recursively coded finite proof predicate for the specified syntactic ZFC presentation. Taking negations gives the stated ordinary ZFC-provable equivalence between absence of integer zeros and syntactic consistency. This composition proves neither consistency nor inconsistency.

The two calibration results are imported mathematical theorems, not new verification results of this packet. Their exact ordinary sources are copied verbatim in `upstream_ordinary/`, with repository commit, original path, SHA-256, and byte length in `upstream_ordinary/SOURCES.json`. Some ordinary sources themselves import named earlier Pell, compiler, and model-theoretic lemmas. Their dependencies and internal historical pins have been preserved. Thus the complete proof is a referenced mathematical derivation, not a newly self-contained reconstruction of the entire repository's calibration.

## What the ordinary sources actually say

`upstream_ordinary/ordinary36.md`, also preserved as the source-25 vendored copy `source25_ordinary_blank.md`, supplies the arbitrary signed-witness arithmetic proof. Sections 3–7 recover the norm signs, main and auxiliary indices, power-of-two rank, bit masks, native computation, and canonical positive witnesses. Section 7 explicitly composes this ordinary compiler argument with the established blank-halting/refutation calibration. Section 9 identifies the remaining machine-to-Diophantine obligation as a formalization obligation; it does not represent finite diagnostics as an unbounded proof.

`upstream_ordinary/fixed_blank67.md` supplies the finite-window interpretation. Its Section 6 traces a unique initialized head through a finite strip until a halt row; conversely it pads any finite halting computation and constructs the canonical native witnesses. The source-34 adapter changes the coefficient layout and tuning, so this older coefficient tuple must not be substituted for the tuple used here.

`upstream_ordinary/source34_coefficients.md` supplies the actual coherent four-port instance used in this packet. It proves its mixed-field decoder, exact support geometry, rotation synchronization, carry bounds, mask populations, odd-prime rank controller, and canonical parity promises. Its section “From the compiler interface to the requested logical equivalence” explicitly states that the finite tile argument, Pell compiler, controller, and eliminations are formalizable in ZFC and compose to the requested no-zero/consistency equivalence. The fixed coefficients are not arbitrary parameters.

`upstream_ordinary/k215_ordinary.md` gives the ordinary exact-table machine proof. It identifies the complete source/control-flow correspondence, quantified runtime theorem on arbitrary register values and finite spare lists, exact blank prefix, and dominated-calculus calibration. It explicitly states

    ZFC proves: Halt(K215, blank) iff not Con(ZFC).

This is the ordinary calibration theorem imported here. The file distinguishes it from its separately compiled external Lean/Rocq endpoints and from an internal PA endpoint.

These are genuine ordinary proof texts with unbounded mathematical arguments, not just an assertion that a collection of finite tests passed. The present packet audits the new arithmetic reduction and verifies the relevant inherited interfaces; it does not newly reprove every predecessor theorem in those texts.

## The external Lean endpoint is different evidence

The copied `KEndpoint215.lean` states

    BlankHalts machine215 iff BProv ZFCax_s [] Form.fBot.

This is a theorem in the external Lean metatheory about the literal machine and the external inductive predicate of finite ZFC derivations. The generic `KEndpoint.lean` composes the machine simulation with a semantic lower/upper calibration of the numerical calculus to ZF. `ConstructibleChoice.lean` then passes from ZF refutability to ZFC refutability by the constructible model and first-order soundness/completeness.

These source files are copied to identify the dependency precisely. No new Lean compilation or kernel audit of them was run for this packet. An external Lean theorem with this type, even an unconditional one, does not by itself constitute a proof inside the encoded ZFC calculus of a sentence expressing the same equivalence.

The ordinary calibration can use first-order completeness and the constructible-model theorem inside ZFC as ordinary set-theoretic arguments. Doing so is conceptually different from assuming soundness of ZFC or of Lean. It also differs from providing the repository's requested machine-checked translation of these arguments to its sealed object-language syntax. The latter must handle all internal proof codes, including nonstandard ones in arbitrary models; agreement only on externally standard codes is insufficient.

## What remains open in the repository's object-language project

The copied `FORMALIZATION_BOUNDARY.md` describes a distinct, stricter formal-delivery target: an actual derivation of an internal consistency/unsolvability biconditional in the repository's `SetTheory.Form` calculus. It concerns the existing closed nine-variable expression and explicitly records the target

    BProv ZFCax_s []
      (fIff ObjectCodeSeal.consistencySentence
            ObjectEquation.unsolvabilitySentence).

That target remains open in the cited repository checkpoint. The supplied local internal arithmetic, sealed syntax, quartic compilation, and external equivalences do not close it. Authentic fixed-payload/native tableau calibration also remains an explicit obligation in the machine-checked native route. No file in this packet claims to supply either missing formal composition.

The new polynomial's ordinary proof is not a derivation of the displayed existing nine-variable object sentence, and its existence does not change the status recorded in `FORMALIZATION_BOUNDARY.md`. A formal endpoint for the new polynomial would additionally require quoting its literal circuit and composing the new root-extraction reduction in the same object calculus.

## How to read the final theorem claim

The appropriate reading is: **an ordinary mathematical proof in ZFC, by explicit reduction and composition with the named pinned ordinary calibration theorems**. It is not a newly kernel-checked native calibration or encoded ZFC derivation.

If the imported ordinary source/refutation calibration is regarded as an obligation still to be independently re-established rather than as an accepted theorem, then the unconditional result delivered by the new argument is the exact source-zero equivalence, and the final Con(ZFC) statement is conditional on that calibration. The archive makes that dependency visible instead of using the external Lean endpoint or bounded tests to hide it.

This distinction is material to review. It does not assert a new gap in the ordinary predecessor proofs; it identifies which results are newly proved here, which are imported by mathematical reference, and which encoded proof artifacts are still absent.
