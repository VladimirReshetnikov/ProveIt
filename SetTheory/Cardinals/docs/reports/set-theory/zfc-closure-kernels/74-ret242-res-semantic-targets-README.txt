Research branch: semantic targets and tag-independent MP
Baseline: ProveIt e58338db7545909907e07a7603e8eb88625c527a.

Files:
  semantic_targets.tex          Complete ordinary proof and prior-route audit.
  semantic_targets.py           Standalone exact-integer finite semantic controls.
  semantic-targets-results.json Actual successful execution record.

Main new-to-this-review results:
  1. NIP can halt on any H=1 mod4 (any membership atom), preserving the
     calibrated source halting predicate. No empty-set assumption is needed:
     assign every variable the same object in a nonempty irreflexive model.
  2. MP can replace H=4P(T,D) by floor(H/4)=P(T,D). Its four tags are covered by
     ordinary MP, atomic refutation, universal elimination, and diagonal equality.
     Equality requires CP+IR's >=2-object model property. The rule is about
     validity under every assignment, not truth at one assignment.
  3. The same concrete Enum254 proof-producing blocks remain complete: discard's
     intentionally failing MP1 still fails at cache0, and all other compiled MP
     calls are exact successful implications. Candidate scheduling is unchanged.
  4. In an irreflexive nontrivial model, valid odd codes are exactly
     8*i*(i+1)+3 (reflexive equality), and therefore are 3 mod16.
  5. Reconcile source57's prior decoded-cache MP: its fused groups-of-four
     inverse-pair loop can now let ALL four exhaustion positions exit normally,
     deleting its invalid-tag rejection path. The decodedMP representation and
     dummy-free proof blocks are credited to source57; only tag removal is new.

These results do not provide a new TM table, a measured state count, a Lean
theorem, or the exact PA proof-code/internal machine bridge. They are an
optional alternate source branch, independent of root's new 242-state local
reduction. A four-phase cache drain may cost MORE than the existing NIP check;
the report explicitly charges the unmeasured quotient/comparison changes.

Run:
  python semantic_targets.py

The control models are deliberately only irreflexive finite structures,
not finite models of the native CP/GIC theory. This tests exactly the semantic
lemmas' hypotheses and supplies singleton/pointwise counterexamples.

Provenance of reviewed executable interface:
  SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/
    53-span-semantics-reference-Enum254.lean
    71-qt-research-joint-source-reference-snapshot-ZF-m254-tools-logic-spec.py
  Main prior-result files are linked in the TeX bibliography.

No claim of historical priority is made. Existing raw PSC, EPSC2, EPSC1+BU,
finite assignment kernels, quantified-NAND and equational-carrier proposals
were identified as existing repository work rather than recycled as new.
