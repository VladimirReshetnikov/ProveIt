# Closing the propositional hypotheses of the Tarski calculus

16 October 2026. The new Lean module
[`Lukasiewicz.lean`](../../Lean/BusyBeaver/ZFC/Lukasiewicz.lean) closes the
K/S/Peirce gap identified in [the conditional-calculus review](tarski_calculus_review.md).
It also derives ex falso from the original rho6 and supplies an unconditional
wrapper for the existing first-order completeness theorem. This is progress
on the complete original logical frontend, with all eight logical rows and
both gated atomic vacuity families retained.

The finite certificates already exist in the published verification:
[`CD254.v` at commit `297ab8d`](https://github.com/jeff87654/busy-beaver/blob/297ab8df7e5de329605c3875b4934643b371a5e3/ZF/m254/coq/logic/CD254.v).
Mira-Cult designed the machine; Jeff supplies that verification. Its
`cdgen.py` records that the certificates were found by condensed detachment.
The new file is an attributed Lean port of all 107 numbered certificates;
it preserves their numbering and does not relicense the upstream snapshot.
There is one initial rho8 instance and 106 single-detachment lemmas. K is
certificate 16, Peirce 25, implication composition 91 and S 106. No new
search or Coq build was necessary.

The port first works over an arbitrary type, binary operation `imp`, and
predicate `T`. Its `Implicational` structure has exactly modus ponens and
all instances of

```text
((c → u) → a) → ((a → c) → (b → c)).
```

It assumes neither syntactic injectivity nor any interpretation of a
falsity symbol. The original proof generator instantiates proof-only
variables erased from the conclusion with numerical formula `0`. The Lean
port uniformly uses the arbitrary local formula `v0` instead. Every
certificate statement and proof term was checked against that documented
translation, and Lean checked the resulting abstract derivations. Thus no
special property of runtime code zero is used. The source's minor-premise
then major-premise ordering is retained by the explicitly defined `detach`.

Rho8 alone cannot prove ex falso for an arbitrary designated formula.
The separate `Tarski.ex_falso` proof uses the original rho6. For a target
`A`, put

```text
E = ∃0 ∀0 A = (∀0 ((∀0 A) → ⊥)) → ⊥.
```

K proves `⊥ → E`. Rho6 proves `E → A`; K weakens this to
`⊥ → (E → A)`, and S combines the two implications to give `⊥ → A`.
These are actual `Thm Ax` derivations for every theory predicate `Ax`.
No equality or vacuity rule is needed for this propositional step.

`Tarski.classical Ax` therefore constructs all five fields of
`Kalmar.Classical NF.imp NF.bot (Thm Ax)` from the actual rows. The new
`Tarski.complete` applies the existing `Tarski.completeness` with this
structure both for `Ax` and for the empty theory. Its only premise is the
stated semantic consequence under all assignments in all membership
structures with genuine equality and primitive falsity. It has no supplied
K/S/Peirce/ex-falso structure and no extra calculus axiom. The old conditional
theorem remains available unchanged.

All 107 certificates, the structure construction, and a caller using the
unconditional wrapper passed direct Lean 4.32.0 checking. The new module
compiled without warnings in 0.54 seconds. `#print axioms` reports no axioms
for K, S, Peirce, composition, ex falso, or `Tarski.classical`. The complete
first-order wrapper uses only `propext`, `Classical.choice`, and `Quot.sound`,
already used by the existing model construction. There are no admissions,
custom axioms, or unchecked native evaluation steps.

The scoped check reused the source-verified Tarski cache and the prior
38-module dependency cache; all six current Tarski source blobs matched
the cache review. It did not rebuild `Boot253`. Exact commands, source
identities, all seven axiom audits, and the checked caller are preserved in
[results/lukasiewicz-verification.json](results/lukasiewicz-verification.json).
For replay with a normal source-built dependency cache, compile this module
with that cache on `LEAN_PATH`, then compile the audit source recorded in
that JSON. In this run the symlink-merged cache was
`/tmp/zfc-lukasiewicz-check-z6r4piop`; its `compile.log`, `Audit.lean`, and
`Audit.log` retain the local check.

This proves completeness of the named calculus with **primitive falsity**.
The generic pure implication certificates also tolerate numerical aliases,
but that fact alone does not identify the named calculus with a machine's
runtime syntax. The arbitrary-code adapter, relative falsity alias,
literal theory bundle, proof enumeration, register-program compilation,
and binary-table endpoint still need their own bridges. No new machine
size or equivalence with consistency of ZFC is claimed here.
