# Audit of interval-specialized whole-frame replay

This note records an independent review of `root-research/abstract_program.py`
and `root-research/full_symbolic.py` as first supplied on 2026-10-18. The latter
uses the previously audited `check_macro_inductions.py` from the context246
package. The review found no mathematical defect in the interval transfers or
the local symbolic execution rules. It identified a certificate-validation
integration issue and recommended explicit positivity and provenance checks.
The final packaged version should record the disposition of those changes.

## 1. Finite interval certificate

An abstract register value is an interval `[lo, hi]`. Lower bounds are in
`{0,...,8}`. Upper endpoint `9` denotes infinity, not the singleton value 9.
The abstract state at each literal instruction site is either unreachable or a
product of nine intervals. The join takes the minimum lower endpoint and the
maximum upper endpoint. This is a finite lattice, so the worklist terminates.

The increment transfer saturates the lower endpoint at 8 and the upper endpoint
at the infinity code 9. Those saturations enlarge the exact image. A positive
decrement intersects the selected interval with the positive naturals and
subtracts one; an unbounded upper endpoint remains unbounded. A zero decrement
is admitted precisely when its lower endpoint is zero and sets the selected
register to the singleton zero. These are sound componentwise overapproximations.

The important certificate property is local closure, not the worklist's method
of discovery. It suffices to check that the invariant at the initial decoded
site contains `(3,0,0,0,3,0,0,0,0)` and that every admitted transfer is contained
in its successor's invariant. Induction on the number of source instructions
then proves that every actually reached source configuration is covered. The
all-zero padding used to locate the next leaf agrees with the literal binary
tree decoder and the RM path semantics; trailing nonzero bits are rejected.

`verify_interval_independent.py` checks the supplied certificate without
importing the worklist, capped transfer functions, or path functions from
`abstract_program.py`. It uses exact integer interval images with a genuine
unbounded endpoint, and Jeff's separate `rmpath.py` path semantics. The supplied
certificate passes all 8,384 outgoing edges at 6,456 admitted sites. The unique
halt site has no outgoing edge, explaining the difference from 8,385 replay
cases. An all-unreachable certificate and a certificate with a live successor
removed are both rejected. The result and input hash are recorded in
`interval-independent-audit.json`.

The exact consequences are:

| Site index | Full source path | Instruction | Invariant at selected register |
|---:|---|---|---|
| 6316 | `111010010110001100` | decrement logical register 6 | `[0,0]` |
| 6434 | `111111000` | decrement logical register 1 | `[0,0]` |

Thus both sites always take their **zero** branch. Their positive branches are
the omitted cases. The four unreachable instruction sites are 6317, 6318,
6435, and 6436. No claim that their physical transition rows are globally dead
follows: these rows can still serve other instruction sites.

## 2. Quantification in whole-frame replay

At each admitted instruction, the new replay exposes all nine primary unary
blocks. Every nonconstant primary value is represented as its proved lower
bound plus its own independent natural variable. A finite upper bound is
deliberately discarded. This strengthens the claim checked by replay: it
covers a superset of the interval invariant. A singleton value below the
infinity code is represented exactly. On a positive decrement branch the
selected value becomes `max(1,lo) + n`; on the zero branch it is exactly zero.

The gap is represented by a separate natural variable plus the fixed allowance
needed for a frame distance of at least 40. The spare suffix is encoded as one
explicit block of an arbitrary natural value, followed by an arbitrary finite
list of blocks. This is exactly every nonempty spare list: it includes a
single spare of value zero, arbitrarily long lists, and arbitrary positive
spare values. There is no assumption that spare values remain one. The blank
exterior occurs on both ends of the represented tape; a `Blank` atom denotes
the corresponding outward infinite zero ray.

## 3. Local rules and arbitrary lists

Every step is one of the following:

1. A literal row of the current binary transition table. The checker requires
   a provably nonempty leading run before inspecting its first symbol.
2. Iteration of a same-state self-loop moving in the represented scan
   direction. Induction on the natural run length proves this rule, including
   the zero-length base case.
3. A traversal of an arbitrary finite block list. Each list rule is introduced
   only after its one-block theorem has been checked from literal rows and
   unary inductions with arbitrary untouched contexts. Structural induction on
   the list then proves the advertised whole-list transformation.
4. Associativity of word concatenation, coalescence of adjacent equal-symbol
   runs, removal of an exterior finite zero run, and the checked encoding
   identity `C(A)1 = 1B(A)` (or its reversal).

The four list traversals preserve their state and orientation and cross each
block exactly once. Their widths are the actual sums of encoded block
lengths. Treating those widths as formal affine variables is safe: the
checked equalities hold for all values and therefore for those actual sums.
It does not assert that every assignment of unrelated width variables is a
real tape. The representations of primary values, spare values, gap width,
and list contents remain distinct.

The new replay does not invoke the register-operation macro oracle used by
the older all-site checker. It composes the four small traversal inductions
and literal rows over the complete exposed register frame. Its reliance on
ordinary mathematical induction and the Python checker remains explicit; it
is not a new Rocq or Lean endpoint.

## 4. Endpoint and divergence argument

For a nonhalting source instruction, successful replay gives literal TM
reachability of the expected next frame, with the exact changed primary
register, unchanged other primaries and spare suffix, the proved spare append
for increment, the proved gap increase for positive decrement, and the exact
program-counter overflow displacement. A halt instruction instead gives
reachability of the distinguished halting state. A halt reached in another
case cannot be silently passed, because it has no transition row.

Every segment used for an infinite-execution simulation must contain at least
one literal TM step. The original all-site proof checks this explicitly. The
new checker should also assert that the affine step count has constant term
at least one, which implies positivity for every natural instantiation. Its
actual decoder begins with a literal transition, so this is a validation
strengthening, not a discovered zero-step counterexample.

The finite interval closure proof plus the positive whole-frame segment proof
supports induction over every finite source execution prefix. It consequently
supports both directions of the halting correspondence, including divergence.
It still requires the independently checked finite blank bootstrap and the
dirty-root equivalence already identified in the original audit. This proof
does not establish a smaller state count by itself.

## 5. Integration issue identified

The first supplied `full_symbolic.py` read `interval-invariants.json`, indexed
its entries by the current source-site order, and skipped entries marked
unreachable without checking the file's initial inclusion or closure. As an
isolated verifier it would therefore accept an all-unreachable file
vacuously. The generated certificate is independently valid, as established
above, so this does not invalidate the supplied generated analysis. It is a
real gap in a claim that the replay script alone validates arbitrary supplied
certificates.

The final checker should validate the input certificate before replay: exact
source association and length; nine well-formed intervals per admitted site;
initial inclusion; every admitted successor's existence and enclosure; and
positive segment cost. It should record the exact table, source, invariant,
and checker hashes. A full result must be distinguished from a `--limit`
smoke-test result and should not be overwritten by one. These recommendations
were sent to the author during the review.

### Disposition in the packaged checker

The subsequently reviewed portable version in
`output/zfc-below246-research/code/full_symbolic.py` validates the invariant's
source hash, interval dimensions and domain, initial inclusion, and all
successor closures before replay. It checks the exact expected case count,
positive affine time with constant term at least one, and distinct filenames
and `PASS_LIMITED` status for partial runs. The corresponding
`abstract_program.validate_invariants` implements the advertised closure
check. These changes resolve the integration issue identified above; no
additional semantic execution rule was introduced.

The reviewed full output reports all 8,385 cases, 2,005,266 symbolic rules,
all 492 transition rows, and a minimum of 13 actual steps per instruction.
The portable interval file independently passes the separate exact-interval
checker and both mutation checks. At this review, the portable full checker
had SHA-256
`c689f2dc2583e11491bd496ca902da2f13dfec781a3ed1612eb09cd224a19887`
and the interval producer/validator had SHA-256
`a88d789b96101f3b127474538d55f4e267a36a1e0d54c93b0ec06973600b8ff4`.
Later nonsemantic packaging edits should be covered by the final manifest.
