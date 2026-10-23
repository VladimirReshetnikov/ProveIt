# A Diophantine equation for syntactic consistency of ZFC

Research started 23 October 2026, from repository commit `22e75dd6b8`.
This directory contains active research, its Lean proofs, and the delivered
manuscripts in [con-zfc-diophantine-forms](con-zfc-diophantine-forms/README.md).
The manuscript collection was moved here from the Cardinals reports tree
on 23 October 2026 at the repository owner's request.

The target is one integer-coefficient polynomial, with an exactly stated
witness domain, whose absence of zeros is equivalent to the absence of a
finite derivation of falsity from the repository's ZFC axiom predicate.
Neither consistency nor inconsistency is assumed.

## Approach and comparison

There is no single established meaning of "simplest": number of variables,
total degree, arithmetic operations, and coefficient size give different
answers. We first seek the fewest natural witnesses available from the
repository's proved reductions, while retaining a quartic alternative.
Global optimality is not asserted.

The wave-5 report collection explicitly says its new final equations have
no end-to-end Lean certificate. Its inherited P67 is a particularly short
candidate: 15 strictly positive witnesses, degree 155, and 67 binary
arithmetic operations. Its fixed coefficient tuple and native-window/Pell
compiler still need a formal semantic bridge. Nine-natural-variable forms
use the already formalized Jones reduction but introduce very large powers.
The ten-unrestricted-integer Sun construction is not formalized here.

The first formal route being investigated is:

1. A concrete semidecision procedure halts exactly when ZFC has a finite
   refutation. Reuse the checked K215/program endpoint rather than assume
   that its halting predicate is computable.
2. Apply the proved MRDP theorem and Jones quartic compression.
3. Apply the proved nine-variable reduction and fix the ordinary input to
   1, obtaining one polynomial in nine natural variables.
4. Negate the solvability equivalence.

An existential representation chosen with `Classical.choose` is a useful
checked milestone, but is not a materialized explicit coefficient recipe.
These two levels will be reported separately. Likewise, a Lean theorem
about syntactic ZFC consistency is distinct from a derivation *inside* the
repository's object-level ZFC proof calculus. Portability of an arithmetic
argument to ZFC is not itself a checked object-level derivation.

See [STATUS.md](STATUS.md) for the current evidence and remaining work.

## Source interfaces

* `BusyBeaver.ZFC.KEndpoint215.blank_halts_iff_zfc_refutation`: the literal
  215-state machine halts on blank tape iff `BProv ZFCax_s [] Form.fBot`.
* `Diophantine.Common.MRDPCore`: `MRDP.mrdp`, proved without a DPRM axiom.
* `Diophantine.Paper1982.RecursivelyEnumerableQuartic`:
  `Jones1982.rePred_quartic58`.
* `Diophantine.Paper1982.NineMain`: `Jones1982.nine_unknowns`.

All new mathematical statements must have complete proofs: no `sorry`,
`admit`, or additional axioms. Transitive axiom audits and reproducible
build commands will accompany completed milestones.
