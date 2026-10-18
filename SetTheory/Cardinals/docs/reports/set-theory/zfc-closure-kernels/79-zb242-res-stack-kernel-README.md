# Environment-stack finite frontend

This is a separate research branch accompanying the 242-state machine package.
It is written against ProveIt commit `e58338db7545909907e07a7603e8eb88625c527a`.
It supplies a new compact frontend, **not another binary machine**.

The concrete result is a complete **1,169-bit equational packet** with 14
equations, 16 operation symbols, at most 3 variables per equation and 214 term
nodes. The comparison is source 70's complete 2,324-bit grouped packet, in the
same fixed-opcode format. The new packet saves 1,155 bits (49.7%). The preferred
version has a separate member selector; deriving that selector saves a symbol
but produces a larger 1,201-bit packet, also included.

## Files and replay

- `stack_kernel_note.tex`: complete ordinary mathematical argument, provenance,
  exact packet cost, alternatives audit, and proof/compiler limitations.
- `stack_kernel.py`: standalone standard-library generator and verifier.
- `generated/stack_epsc_explicit_pick.equations`: all 14 preferred equations.
- `generated/stack_epsc_explicit_pick.bits`: complete 1,169-bit packet.
- `generated/stack_epsc_explicit_pick.json`: named signature, equations, source
  groups, endpoints and metrics.
- The corresponding `derived_pick` files record the 1,201-bit control.
- `generated/verification.json`: executed finite verification results.

Run:

```sh
python3 stack_kernel.py --out /tmp/stack-kernel-replay
```

The run checks 2,080 symbolic stack projections, 16,384 finite formula
reifications with quantified binders and descriptor parameters, 72 Boolean
truth assignments for each packet, arity-aware packet round trips, and two
malformed-packet controls per variant. The finite formula comparisons are
syntax/semantics regressions, **not finite models of the full one-sorted theory**.

## Mathematical contribution

Use only the native environment equations

```
V(P(x,s),d) = x
V(P(x,s),A(j,d)) = V(s,j)
```

and reuse the atomic-class constructor `A` to generate selector numerals
`nu(0)=d`, `nu(n+1)=A(nu(n),d)`. The existing indexed-update conditional equality
and its reified equality completion are unnecessary. Classes use NAND, atomic
membership and existential quantification by prepending a value. A descriptor
packs the matrix code and all its finite parameters; the inherited raw EPSC
closure statement then recovers every pure-membership schema instance.

The note supplies an ordinary ZFC-formalizable proof using the existing raw
EPSC calibration as a named dependency. The upper construction handles every
object, selector and class code using increasing, disjoint numerical
constructors on an externally countable ZFC model. The Boolean conversion
preserves native equations by using the **same countably infinite carrier**;
its converse uses an ultrafilter without quotienting the arbitrary native
functions. It does not rely on the generally invalid claim that a
powerset/retraction extension preserves native equations.

No Lean/Rocq check of this calibration or compiled binary proof-search
interpreter is supplied. The parser, substitution engine, context replacement,
fair enumeration and blank-tape initializer must all be charged before this
frontend can imply a TM state bound. The independently established 242-state
machine does not depend on this branch.

## Sources

The literal predecessor packet and metrics, source 40's generator and review,
and source 14's exact empty-seed equivalence review are included under
`reference/`, with their pinned repository paths and Git blob identities.
In particular source 14 is the exact empty-seed EPSC dependency; the separate
point/subset-seeded PSC document is not substituted for it.

0. ProveIt source 14, empty-input EPSC/PSC equivalence:
   https://github.com/VladimirReshetnikov/ProveIt/blob/e58338db7545909907e07a7603e8eb88625c527a/SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-146-source-14.md
1. ProveIt source 40, finite raw EPSC assignment/class kernel, including the
   six exclusive-branch closure clauses:
   https://github.com/VladimirReshetnikov/ProveIt/blob/e58338db7545909907e07a7603e8eb88625c527a/SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-154-source-40.md
2. ProveIt source 70, separate equational branch and the 2,324-bit comparison:
   https://github.com/VladimirReshetnikov/ProveIt/blob/e58338db7545909907e07a7603e8eb88625c527a/SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-166.md
3. McCune, Veroff, Fitelson, Harris, Feist and Wos, *Short Single Axioms for
   Boolean Algebra*, J. Automated Reasoning 29 (2002), 1–16, Theorem 2 (Sh1):
   https://www.cs.unm.edu/~mccune/papers/basax/v12.pdf
4. Berline and Grue, *A kappa-denotational semantics for Map Theory in
   ZFC + SI*, TCS 179 (1997), 137–202, used only for the alternative-formalism
   calibration caution:
   https://hjemmesider.diku.dk/~grue/papers/BerlineGrue97/BerlineGrue97.pdf

The raw EPSC theory, prior assignment/class route, witness sharing, Boolean
basis and packet format are attributed to these sources. The new part is the
environment stack, its selector/class integration, the consequent omission of
conditional equality, and the measured packet.
