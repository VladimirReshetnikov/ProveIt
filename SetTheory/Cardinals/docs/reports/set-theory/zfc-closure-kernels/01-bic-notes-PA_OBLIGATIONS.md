# Exact arithmetic and compiler obligations

These are implementation obligations, not claims that serialized proof objects
are supplied. `Ref_T(p)` means that p is a refutation under the fixed recursive
presentation T. Fix coding, proof calculus, universal closure, alpha conversion,
and the contradiction root before serializing any of the following.

## Set-theory and equality translations

| Constructor | Universally quantified PA theorem | Mathematical source |
|---|---|---|
| D | Ref_ZF_noFoundation(p) -> Ref_EBC(D(p)) | Guarded exact images; partial functions; Separation, Power Set, Pairing, singleton-decoding Union, Replacement, successor closure |
| B | Ref_EBC(p) -> Ref_ZF_noFoundation(B(p)) | Unique exact fibers, functional Replacement, omega recursion, union of positive stages |
| Q | Ref_EBC(p) -> Ref_QBC(Q(p)) | Equality atoms replaced by same-members relation; congruence induction |
| J | Ref_QBC(p) -> Ref_EBC(J(p)) | Derive membership congruence from Extensionality and logical equality |
| W | Ref_ZF(p) -> Ref_ZF_noFoundation(W(p)) | Standard well-founded-hierarchy interpretation |
| L | Ref_ZFC(p) -> Ref_ZF(L(p)) | Standard constructible-universe interpretation |

The ZFC-to-QBC constructor is Q o D o W o L. The reverse uses B o J,
followed by inclusion into ZFC. Prove totality and correctness for arbitrary
formula/proof codes, including nonstandard codes in models of PA; separate
proofs only for each standard schema matrix are insufficient.

A matrix generator must treat slots 0 and 1 as input/output, freshen all
schema binders, and universally close all other free variables. A matrix
may depend on a *parameter* later instantiated to the seed, not on the
schema's own freshly bound seed variable.

## Certificate interface

Serialize the soundness and completeness translations between the chosen
first-order proof calculus and the assumption-free constructor certificates.
Check the side condition on Q2, substitution under binders, generalization
from closed theory axioms, alpha conversion, and strict backward references.
The Python code is only an executable reference; its tests are not this proof.

The root is `not (all v0 (E(v0,v0) -> E(v0,v0)))`, a logical contradiction.
Changing it to a self-membership atom requires additional theory or a proved
target reduction. The calculus is classical, not intuitionistic.

## Search and literal machine

Specify a primitive-recursive decoding of integers as finite certificates.
Prove in PA that every finite certificate occurs and that checking terminates.
For the actual deterministic two-symbol blank-tape table, prove both:

1. Every halting run extracts an accepted certificate.
2. Every accepted certificate produces an eventually halting run.

Include initialization, symbol convention, missing transitions/halting state,
state renumbering, all optimizer passes, and a table digest. The compiler
must not attempt to decide the semantic boundedness premise of BIC; it emits
the conditional axiom as syntax.

## Boundary on upstream prover evidence

A theorem accepted by an unrestricted proof-assistant kernel is not by itself
a proof *in PA*. Audit the exact axioms at the endpoint and either provide a
PA syntax development or a separate arithmetic strength reduction. A finite
transition table, its reported state count, and an upstream no-axioms claim
are not substitutes for these interfaces.
