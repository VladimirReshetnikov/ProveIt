# Independent logical review of the source composition and final 237-state machine

## Outcome

The source-reassociation proof is sound, with the consumed-path/zero-tail
semantics verified independently against `RegisterPath.lean` and both literal
source arrays. The requested ordinary ZFC theorem follows from the direct
final-table universal simulation and startup, the source graph identity, and
the explicitly retained logical calibration. This does not require a general
soundness theorem for Lean or completion of the stronger represented PA lane.

The report fragment is `logic_review.tex`. It includes the exact theorem,
positive-segment composition criterion, an explanation of why disjoint edits
alone are insufficient, precise inherited source interfaces, the finite-proof
coding bridge, proof status, and a focused alternative-formalism review. Its
machine numbers, canonical hash, and direct-runtime metrics have been updated
to the final 237-state machine. The initial independent source check is
unchanged, since the final source has not changed.

## Final 237-state local review

`local237_addendum.tex` records the independent mathematical review of the
new235-to98 fold: no flaw found. `review_local237.py` supplies a second finite
verification using partial-assignment entailment for invariant closure, rather
than the supplied verifier's Boolean-window enumeration. The independent
result is `local237_independent_review.json`: all476 old transition implications,
473 ordinary row identities, and all three open-tape blocks pass. The guards
themselves are checked to follow from the invariant and current read bit. The
new blocks have lengths3,5,3, preserve the entire tape throughout, and reach
the exact old endpoint and displacement. The initial invariant is vacuous for
every tape/head at state95, so no register-frame assumption is needed.

Replay is portable:

```sh
python -B review_local237.py OLD238_TABLE NEW237_TABLE \
  --output local237_independent_review.json
```

The new local theorem has ordinary all-tape scope and transfers the238
calibration. The direct final237 runtime is a separate completed validation
route; this branch read its result but did not repeat the entire execution.

## New checks

`check_source_graph.py` is an independent CLI checker, using integer path
arithmetic rather than the incoming checker's reverse-path routines. It
compares the complete descriptor arrays of two literal source files. It checks
full prefix-free source trees, all source operations, both decrement guards,
initial leaf 0, and canonical zero unused tails. It rejects a changed decrement
register, a missing leaf, and a duplicate leaf. It does not import other code.

Run it from any directory:

```sh
python -B check_source_graph.py BASELINE_SITES_JSON CANDIDATE_SITES_JSON \
  --output source_graph_audit.json
```

Actual fresh result `source_graph_audit.json`: PASS, 6,455 leaves; 8,385 guarded
edges; one halt; source depths 51 and 48; all three negative controls reject.
The result stores the original inspection paths and exact byte digests as
provenance. Those absolute historical paths are not required for replay.

## Logical sources actually read

Pinned ProveIt root:
https://github.com/VladimirReshetnikov/ProveIt/tree/ce192939372ac7944fe2a0208c68a96d49fb5e3b

All paths below are relative to that root:

- `Computability/BusyBeaver/Research/ZFC/candidate-rotation240/README.md`
- `Computability/BusyBeaver/Research/ZFC/rotation240_binary.md`
- `Computability/BusyBeaver/Research/ZFC/calibrated_rotation240.md`
- `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/BinaryRotation240.lean`
- `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/RegisterPath.lean`
- `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/CalibratedRotation240.lean`
- `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/CalibratedRotation244.lean`
- `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/WFTheory.lean`
- `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ZFNative.lean`
- `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ConstructibleChoice.lean`
- `Logic/FirstOrder/Lean/FirstOrder/Completeness.lean`, BProv definition
- `SetTheory/ZF/Lean/ZF/Zf.lean`, actual ZF sentence theory
- `SetTheory/BoundedConsistency/Lean/BoundedZFCConsistency/Choice.lean`, actual ZFC sentence theory

Also read the source-reassociation and endpoint fragments, local fold proofs,
and independent checker inside the incoming `ZFC_239_State_Construction_2026-10-19.zip`;
the coordinated169 fold proof, guard specification, and finite equational946
packet note from `BusyBeaver239_Research_2026-10-19.zip`; and the quantified
fourth-logical-input obstruction in `ZFC239_Companion_2026-10-19.zip`.

A primary public source retrieved for the logical-basis discussion:
Frank Pfenning, *Single Axioms in the Implicational Propositional Calculus*,
CADE 1988, https://www.cs.cmu.edu/~fp/papers/cade88.pdf, Section 2.
Web ref if needed: `turn6view0`. Root must retrieve it before using a GenUI
citation. It documents the Tarski–Bernays schemas and the four-variable
Łukasiewicz single axiom. No new historical priority claim is made.

## Mathematical calibration observations

1. `BProv(B,G,phi)` is existence of a finite list of base axioms and a finite
   `Prov` derivation; it is not arbitrary semantic consequence by definition.
   The usual finite-tree coding gives the intended standard refutation predicate.
2. The current native theory is CP + full GIC + irreflexivity, with genuine
   first-order equality. Its numerical false alias is self-membership; equality
   and irreflexivity cannot simply be deleted because another equality-free
   theory has the same consistency strength.
3. `WFTheory` and `ConstructibleChoice` use finite syntax and set-coded models.
   Their ordinary proofs are ZFC-formalizable. Reading their external Lean
   theorem as a ZFC theorem without this content-based justification would be
   insufficient.
4. Source-tree reassociation itself does not transfer the tape guard
   q=169, read1 => right1. That guard was obtained from all instruction frames
   of the old source. The direct 238 checker re-establishes full runtime for the
   changed source and final table, which makes the ordinary endpoint independent
   of silently transferring the old guard. Parent is additionally checking the
   guard in the new boundary239 reference as a second explanatory route.
5. Final construction metrics received from source_encoding and read locally:
   237 states, 474 rows, all8,386 universal guards,2,261,369 symbolic rules,
   minimum duration13,409,835-step boot,351 one-cells,167 value1 spare blocks.
   Parent owns final machine/runtime verification; this branch independently
   verified source equivalence and the final all-tape local237 fold, not a
   second whole-runtime run.

## Attribution and limits

New here: the independent source-control checker/replay, the explicit
joint-composition analysis for the new238 application, and the independent
partial-assignment review of the subsequent new237 fold. The source rotations,
the two input239 ideas, raw EPSC theory,946-bit packet, quantified logical
countermodels, finite-fragment filters, and original CP/GIC calibration are
inherited and identified as such. Positive-segment simulation and finite-model
arguments are standard methods; no claim of global novelty is made for them.

This branch did not run Lean or Rocq. The ordinary theorem is complete using
the stated inherited mathematical calibration and final runtime facts. It is
not a claim of a newly serialized kernel endpoint or completed internal PA
proof-code comparison. Under bare consistency, nonhalting is unprovable; to
exclude proof of halting one additionally needs suitable arithmetic soundness.
