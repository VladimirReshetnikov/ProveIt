# Replace scheduler resource accounting by occurrence injection

## Result

ZC215's DROP=0 / NIP=1 encoding admits a particularly small scheduler
safety interface: every NIP occurrence has a distinct DROP occurrence in
a strictly earlier candidate. For exhaustive increasing enumeration from
zero, this immediately proves all finite-prefix credit inequalities and
strictly positive credit immediately before each NIP. AX and MP need only
have nonnegative protected-stack contribution. No AX batch-size or density
calculation is needed.

This is a mathematical simplification proposal, not an assertion that
ZC215 already has a machine-checked correctness theorem. It does not change
the machine's state count and does not prove a 214-state construction.

## Reusable theorem and prototype

`PrefixCredit.v` contains a 107-line standard-library Rocq prototype:

1. `NoDup_map_on`: injection restricted to a finite source list preserves
   absence of duplicate occurrences.
2. `finite_prefix_credit`: inject sources into listed destinations, then
   obtain `length pops <= length pushes` from `NoDup_incl_length`.
3. `credit_before_pop`: include the imminent pop as one additional source
   while using only earlier pushes as destinations, obtaining
   `S (length past_pops) <= length past_pushes`.
4. `earlier_candidate_is_in_prefix`: a lexicographic prefix contains every
   occurrence in a strictly earlier candidate.
5. `scheduled_prefix_credit`: combines these facts with a candidate-local
   lowering injection.

The prototype has no Admitted, axioms, or project-specific imports. Its
explicit Section hypotheses must be discharged for the target machine;
they are not certified by writing the generic theorem. No Rocq/Coq or Lean
compiler is installed on PATH or in the inspected standard locations, so
this file has NOT been compiled or kernel checked. The list-library lemma
application and argument inference must be checked with the target Rocq
version before integration.

The same interface in Lean can use finite sets of occurrences and
Finset.card_le_card_of_injOn; the recommended architecture is identical.
Using a list in Rocq avoids importing a new finite-set implementation.

## Only the following codec lemmas are candidate-specific

Let commands be a small inductive type, independent of formula decoding:
Drop, Nip, MP(x), AX(c,x,y). Define fields exactly as in the supplied source:
Drop [0], Nip [1], MP [2,x], AX [c+3,y,x]. Encode nonempty command words
backwards with final residual zero and positive continuation 1+rho(tail).

A. Total parser and two round trips:
   rho(W(n)) = n; W(rho(L)) = L for nonempty L.
   The recursion measure is the positive residual minus one, strictly
   smaller than the original candidate. Keep rho([Drop])=0; do not identify
   this nonempty word with an empty continuation.

B. Single-position strict lowering:
   Replacing Nip by Drop at position j strictly decreases rho.
   At that command P(1,r)-P(0,r)=r+1. Earlier command constructors preserve
   the strict inequality because P is strictly increasing in its second
   coordinate and successor is strictly increasing. These are structural
   lemmas about encodings, not simulation lemmas about tapes or registers.

C. Replacement recovery:
   Raising that same Drop back to Nip recovers the original word. Combined
   with the round trips this proves injectivity on occurrences (n,j).
   Counting command tags alone is incorrect: positions must be retained.

The lowering function can be totalized arbitrarily off NIP occurrences.
The generic theorem requires injectivity only on NIPs, not everywhere.

## Runtime interface and exact boundary

The runtime proof should separately establish that every pre-halt command
history is a prefix of W(0)W(1)...; DROP adds one protected theorem head;
NIP removes one; and MP/AX do not reduce the protected length. Maintain an
explicit logical list of theorem heads above an arbitrary numerical tail
J. Credit_before_pop ensures NIP never reads J, including J=5. Numerical
zero aliases are harmless because the logical list witness, not numerical
magnitude of the stack, records the number of protected heads.

The injection does NOT justify a schedule beginning at a positive cutoff,
skipping failed candidates and continuing, or resetting the resource stack
between candidates. Those variants need a new closure proof or a reserve.
If actual execution halts early, stop the comparison at that finite prefix;
do not count hypothetical commands after the halt. This is an important
explicit interface obligation when connecting the lemma to machine code.

## Expected proof-size effect

Replace bespoke reserve, triangular-block, AX-production, and per-candidate
resource recurrences with the generic theorem and three encoding lemmas.
The reusable part is about 100 source lines in the supplied prototype.
A few short codec lemmas should suffice once Cantor round trips and
monotonicity are already available. A precise reduction in existing proof
lines cannot be claimed without integrating into that repository. This
simplifies only the scheduler/resource portion, not numerical-calculus
soundness/completeness or binary-machine simulation.

## Independent finite smoke test

`check_codec.py` is newly authored here; no scripts from the supplied ZIP
were run. It checks round trips on raw candidates 0 through 99,999, every
NIP's earlier-code image and uniqueness, and positive pre-NIP credit.
`finite_check.json` records 19,566 distinct NIP images, 49,275 DROP commands,
and minimum prefix balance zero. This is a regression test only. The
all-natural mathematical argument is the occurrence injection above.

Source inspected as data: ZC215.zip, proofs/tag_lowering_credit.md, copied
verbatim to tag_lowering_credit.md. No source archive code was executed.
