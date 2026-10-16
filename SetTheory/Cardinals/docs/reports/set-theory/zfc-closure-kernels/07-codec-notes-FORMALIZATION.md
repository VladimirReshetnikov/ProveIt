# Formalization and compilation contracts

The target is a theorem in ZFC, for a frozen literal binary blank-tape TM M:

    Halt_blank(M) <-> exists p Prf_ZFC(p, bottom).

Classical negation gives the requested nonhalting/Con(ZFC) equivalence.
PA is a possible strengthening, not silently imposed by this package.

## Syntax and theory

Freeze the first-order calculus, coding, exact ordinary ZFC schema list,
parameter closure, substitution and alpha conventions, and bottom. The
proposed kernel is equality-free. Its matrix slots 0 and 1 are free input
and output labels; all wrapper binders are fresh above all matrix labels.
All other free parameters are universally closed.

Uniform finite derivation constructors are needed for exact constants,
singletons, Power Set, two-cycle Pairing, switch boundedness, transitive
bounds, Separation, Union, Russell-root Replacement, successor Infinity,
and the exact-fiber/positive-orbit converse. The switch-hull constructor
must not assume that the initial seed object is an element of the output.

The equality translation sends x=y to equality of membership profiles.
Prove first-argument membership congruence from the directed congruence
axiom and second-argument congruence from the profile definition. Then
induct on arbitrary formula syntax, including arbitrary schema matrices.

## Refutation reductions

Implement f and g and prove, for arbitrary proof codes:

    Ref_ZFC(p) -> Ref_Q(f(p))
    Ref_Q(p)   -> Ref_ZFC(g(p)).

The Foundation/Choice class interpretations stay off-machine. Do not replace
a class interpretation with existence of a transitive set model. Do not
silently add unrestricted Collection to the foundation-free base.

## Checker and enumerator

Prove implementation soundness and completeness against the certificate
specification. Every finite candidate must terminate, including malformed
candidates. Every finite certificate must eventually be enumerated. An
implementation failure or rejected certificate is not an accepted bottom.

A retained-stack proof-by-program implementation needs completeness from
arbitrary permitted leftovers, not just soundness of reachable values.
Zero can remain a truth padding cell. It must never be treated as bottom.

## Numeric codec

There are four tags; zero is truth, residue 1 is bottom, residue 3 is
membership, residue 2 is forall, and positive residue 0 is implication.
Code 1 is canonical bottom; code 3 is E(0,0). Normalize Top -> Top to Top
before asserting an encode/decode round trip. Prove the zero case of
code-level modus ponens separately. Bottom aliases and fresh-label bounds
must be included in the calculus bridge.

## Table and target

Freeze a single bi-infinite tape, binary alphabet, blank0, L/R moves,
initial state, halt convention, and whether the halt state is counted.
Check boot and simulation of the exact final table, its digest, and all
optimizations. Prove both run-to-certificate and certificate-to-run
implications. No finite sampling of state merges substitutes for an
all-register-values simulation theorem.

## Proof-assistant/metatheory distinction

The repository's new-work preference is Lean. A Lean or Coq theorem over a
semantic set model is not automatically an internal ZFC proof, let alone a
PA proof. Use a syntax-level target development or give an explicit strength
reduction. This package deliberately supplies no placeholder Lean file
that could be mistaken for a checked formalization.
