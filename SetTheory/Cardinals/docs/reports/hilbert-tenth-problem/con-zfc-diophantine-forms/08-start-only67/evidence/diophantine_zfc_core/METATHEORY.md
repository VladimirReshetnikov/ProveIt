# Why the endpoint can be stated as a theorem in ZFC

## Exact intended statement

Fix a concrete standard recursive first-order presentation of ZFC, for
example the repository's finite-proof predicate `BProv ZFCax_s [] fBot`.
Let Ref_ZFC mean that a natural-number code of such a finite proof exists.
Let Con(ZFC) mean not Ref_ZFC. The desired theorem is

    ZFC proves: (there are no natural-number zeros of the fixed system)
                 iff Con(ZFC).

It is not an assertion that ZFC proves either side unconditionally. It does
not conflict with the second incompleteness theorem. Syntactic consistency
is intended, not soundness, omega-consistency, existence of a transitive
model, or existence of an omega-model.

## What the pinned sources actually state

`KEndpoint.c222_iff_zf_refutation` has the exact conclusion

    KCode222.C222 Code254.F iff BProv ZFax_s [] Form.fBot.

Here F=1. No semantic-model hypothesis occurs in the theorem statement.
`ConstructibleChoice.zf_refutation_iff_zfc_refutation` identifies the right
side with `BProv ZFCax_s [] Form.fBot`. `KEndpoint215` composes this with
the concrete machine chain and yields the same conclusion for blank
halting of `KDense215.machine215`.

The upper argument uses first-order completeness to obtain a set-sized
model of ZF if ZF has no finite refutation, then constructs its internal
constructible submodel and verifies the seed bundle there. The lower
argument uses completeness for the numerical/named calculus, obtains a
seed structure, takes a bisimulation quotient and an internally
well-founded subdomain, and verifies the ordinary first-order ZF axioms.
Gödel's internal constructible-model argument transports ZF to ZFC.

Crucial checked detail: `WellFoundedPart.InternallyWellFounded` says

    for every represented s subset t, if s is nonempty then
    s has a membership-minimal represented element.

It does not quantify over all external subsets, and the module explicitly
states that no external WellFounded relation is assumed. Its subtype is
not advertised as an externally well-founded/transitive set model. Thus
the proof does not strengthen ordinary Con(ZFC) by smuggling in a
transitive-model or omega-model assumption.

## A mathematical formalizability argument

To justify 'provable in ZFC', use the mathematical proofs represented by
the sources, rather than assume that all of Lean's universe hierarchy has
a model in ZFC. For this particular argument:

1. Formulas, finite proof trees, the code constructors and finite machine
   computations are sets built from omega. Their coding and arithmetic are
   definable in ZFC. Finite derivations of the inductively specified
   calculus are exactly finite coded trees satisfying the twelve displayed
   local rules.
2. First-order soundness and the Henkin completeness theorem for a
   countable coded language/theory are theorems of ZFC. They concern
   satisfaction in a set-sized structure, not a truth predicate for the
   ambient universe. The needed term/Henkin model can be coded by a
   quotient of a set of finite strings.
3. All intermediate domains may be sets: a quotient of a set by a
   definable equivalence relation, a definable subset of a set, and
   relations/functions on such sets are supplied by Separation,
   Replacement and Power Set. The internal constructible class of a
   set-sized model is again an externally definable subdomain of that
   model's set domain. 'Internal' in this clause is essential; no ambient
   model of ZFC or externally transitive model is postulated.
4. The infinitude of the ZFC axiom schemes is handled by a set of coded
   formulas and a definable axiom predicate. Verification is uniform in
   formula codes. It is not an appeal to a single truth predicate for all
   formulas of the ambient set universe.
5. The explicit stack proof in direct_stack_core.tex is finite-tree
   induction, integer polynomial arithmetic and finite-path concatenation.
   The independently materialized tape compiler likewise requires only
   arithmetic and finite-computation simulation proofs. Those steps are
   formalizable in ZFC, indeed in much weaker theories once the calibration
   is fixed.
6. A valid explicitly instantiated Diophantine compiler theorem is also
   ordinary arithmetic provable in ZFC. Compose its uniform accepting-run
   equivalence with the preceding equivalences, then negate both sides.

Consequently the ordinary mathematical proof can be carried out in ZFC.
The symbols omega, finite proof and polynomial zero are interpreted
internally when asserting this ZFC theorem. Their external standard-N
interpretation is the corresponding usual metamathematical reading. One
must not silently replace finite proof by truth in the standard universe.

## What is and is not supplied

This is a mathematical formalizability audit, not a newly checked formal
translation of the entire Lean development into a ZFC proof-code calculus.
The pinned README expressly distinguishes external proof-assistant
verification from an internally encoded PA/ZFC derivation. Its reported
Lean dependencies propext/Classical.choice/Quot.sound describe that
verification layer, not extra semantic assumptions to place in the target
arithmetical equivalence. No proof assistant was rerun in this extraction.

A manuscript may accurately give a mathematical theorem 'ZFC proves ...'
with the above argument and the ordinary mathematical calibration proof
as a cited dependency. It should not say 'the provided archive contains a
kernel-checked internal ZFC proof of that sentence' unless such an artifact
has separately been produced. It should also not substitute a raw
variable-length history schema for the final fixed-arity system.
