# The selected checker and a separate explicit proof checker

The existing internal checker theorem uses the **selected** Foundation
refutation predicate `rho` and one bound for the existential witnesses in
`bnd rho`. It says that, for one arity-one primitive-recursive code `c`, native
and standard iPRA prove the negation of that selected predicate equivalent to
`¬∃ b, c(b) = 1`. The native-bit follow-up additionally derives `c(b) = 0 ∨
c(b) = 1` internally for every `b`. The input is a witness bound, not a raw
proof code, and the existential selection of `c` is in Lean's metatheory.
These are statements about the specific representation and theories in the
repo, not an automatically uniform comparison of all ZFC proof codings.

There is also a sharper **external standard-natural comparison** already
available from two distinct Lean source theorems:

1. [`FoundationZFCConsistencyNat.source_nat_iff_no_refutation`](../../Lean/DiophantineConsistency/FoundationZFCConsistencyNat.lean)
   says that Foundation's selected consistency sentence is true in the
   standard naturals iff the repository's sealed ZFC calculus has no
   refutation. Its proof uses a PA theorem, standard-model soundness and the
   stated validator/calculus comparisons.
2. [`AnnotatedRefutationPR.no_refutation_iff`](../../Lean/DiophantineConsistency/AnnotatedRefutationPR.lean)
   says that the explicit unary `refutationProgram` never returns one iff the
   same sealed calculus has no refutation; `refutationProgram_primrec` proves
   the program's primitive recursiveness. Its input is an untrusted numeric
   certificate for that calculus.

Transitivity therefore gives the metatheoretic standard-natural statement

```text
Foundation's selected consistency sentence is true in ℕ
  ↔ no numeric certificate makes AnnotatedRefutationPR.refutationProgram output 1.
```

This semantic composition is not an iPRA derivation. In particular, it does
not, on its own, show that iPRA proves equivalence between the selected
bounded-checker sentence and a sentence representing the explicit annotated
proof-code program. To obtain that stronger comparison one would need, for
example, a formal representation of that exact program in the chosen iPRA
language and iPRA proofs relating its accepted certificates to the selected
Foundation predicate, including the relevant proof-code translations and
witness bounds. A direct internal equivalence of the two **negations** would
also suffice; it need not extract a positive witness. No such comparison is
asserted here merely from the standard-natural theorem. Whether further
comparison is needed depends on the requested meaning of `Con(ZFC)`: the
selected bounded encoding can itself be specified as the consistency
sentence, but identifying a different checker requires its own argument.

The two cited source theorems are different from a newly replayed composition:
the first is present in the audited AQ29 historical parent; the explicit
annotated-checker module was not. A source-declared preflight found 34
additional tracked project modules to rebuild over that parent (plus a new
composition module). Its [guarded author attempt](../../reviews/external-checker-author-failed-attempt/README.md)
stopped because a Mathlib direct import was absent from the pinned parent
guard. The accompanying [`SelectedExternalCheckerComparison.lean`](draft-src/SelectedExternalCheckerComparison.lean)
remains proposed source and has not yet been compiled in a coherent rebuild.
An [isolated reproduction probe](../../reviews/mathlib-primrec-basic-repro-probe/README.md)
did not reproduce the cached object's bytes; it neither proves incompatibility
nor authenticates the original build's transitive ancestry. The comparison
replay remains blocked at this provider boundary, independently of the already
completed native-bit result.

The prepared manifest pins 35 source blobs from commit
`07d55c8b2b0921440cce8b38ff96182973407679`, with SHA-256
`eea1923b96112722f8e2a9151cc870250a5b694bd95d772525fabe8127adcb57`.
The existing guarded runner's source verifier accepted all 35 rows and three
requested reports with actual exit 0. A point-in-time storage estimate found
7.0 GiB free: the 257,263 added source bytes multiplied by the maximum
output/source ratio observed across the audited parent projects approximately
548 MiB of outputs. That extrapolation is not a bound. The launch wrapper
samples free space every two seconds and stops the entire process group if it
observes less than a 4 GiB reserve; changes between observations remain
unobserved. This preflight does not establish the result of the build.
