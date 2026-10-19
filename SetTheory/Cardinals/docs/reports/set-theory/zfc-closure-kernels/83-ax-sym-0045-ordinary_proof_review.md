# Independent review of the source transfer and 246-state composition

Review date: 18 October 2026. This note distinguishes the theorem proved by
the new source transformation from the inherited theory calibration and the
separate literal binary implementation.

## 1. The precise source theorem

Fix a permutation sigma of the eight complete logical rows. Fix, independently
for each row, a bijection of its parameter roles as described in
`axiom_row_permutation.md`; for rho8 the allowed four-role maps put the new
single-read u in either of the two roles occurring once. Let E_sigma,tau be
the abstract enumerator with these changes, the original command decoder,
GEN using the incoming cache, the original bundle and gate, and the same
numeric formula constructors. Let Deriv254(d,1) be the original, fixed
code-level derivation predicate.

For every sound command-boundary seed s, the source proof establishes

    Halts(E_sigma,tau, s) <-> exists d, Deriv254(d,1).

This equivalence is an ordinary theorem that can be proved inside ZFC.
Its proof uses finite natural-number sequences, arithmetic identities for
Cantor pairing, induction on a derivation tree, and the natural-number
well-ordering argument that each candidate drains and the counter eventually
enumerates a long enough successful word. It does not require Con(ZFC).
Its coding-level details remain meaningful for all natural parameter codes,
including the special truth code zero. Permutations of a tuple of naturals
remain surjective when a role is a variable label in one position and a
formula code in another.

The selected-row argument is particularly useful: soundness uses the fact
that every output is an instance of an original schema; completeness chooses
an inverse tuple separately for each axiom leaf, then discards the other
outputs with the exact selection block. Different parameter maps on different
rows therefore do not require a simultaneous inverse tuple for the whole
AX call. The bundle freshness gate remains attached to its unchanged tuple.

The result is refutation equivalence. It does not assert equality of the
original and transformed register instruction traces, equality of their
intermediate numeric states, or exact identity of their complete AX words.

## 2. The endpoint in ZFC

To conclude an equivalence for a particular literal binary table M, three
additional interfaces must be connected to that source theorem:

1. The emitted numeric macros and their scratch-register contracts implement
   exactly E_sigma,tau, including read placement, parameter cleanup, and gate
   behavior. A symbolic formula-stack comparison alone does not establish
   this register implementation.
2. The literal table simulates the resulting register source on complete
   well-formed frames, with finite positive simulation intervals and a
   checked blank initialization reaching a sound seed.
3. The fixed original derivation predicate is internally calibrated to the
   chosen ordinary ZFC proof predicate: existence of a Deriv254 refutation
   is equivalent to existence of a ZFC proof of contradiction.

If these three statements are available as ordinary proofs formalizable in
ZFC, composition gives the user's requested

    ZFC proves (M does not halt on blank tape <-> Con(ZFC)).

This is not a proof of Con(ZFC) or unconditional nonhalting. The new source
permutation proof supplies a reusable step of this composition; it does not
silently discharge the other three interfaces.

The upstream closed Rocq endpoint and the ProveIt external Lean endpoint are
valuable evidence for the inherited calibration. Merely importing their
theorem statements, however, does not supply a serialized internal ZFC or
PA proof. The full ordinary mathematical calibration argument can be reused
with its actual hypotheses. In particular, the upstream literal ZFc omits
Foundation, so the standard-ZFC endpoint retains the separate Foundation
consistency bridge described in `prior_art_audit.md`.

## 3. Review of the composed 246-state packet

The reviewed packet is `agent_reduction/delivery/README.md`, together with
`code/verify_composed246.py`, `code/verify_whole_frame.py`, and the substantive
induction/source routines in its retained vendor files. The complete-frame
runtime argument has the right structure: each accepted guarded source
instruction has the prescribed finite positive literal execution interval;
the target is another complete valid frame or the unique source halt; and
the blank prefix reaches the stated safe frame. Induction concatenates the
finite intervals. Their positive lengths rule out infinitely many source
steps within bounded binary time. Determinism and the complete successor
frames support the reverse halting comparison.

The retained direct replay checks all 8,391 guarded cases, with independent
quantified register values, an extra gap, and a nonempty spare suffix. Its
block-list acceleration rules derive from single-block proofs and preserve
an arbitrary surrounding tape context. The reviewed implementation only
consumes a symbolic run wholesale when the literal transition is a same-state,
same-direction loop; otherwise it consumes a known positive unit. These are
ordinary induction arguments, rather than extrapolation from sampled values.

The source reassociation is different from the new row-role transformation:
the composed 246-state packet checks exact old/new guarded source-graph
equality and independently identifies the old tree with literal Prog254.v.
That bridge is valid for the reassociation. It must not be reused as a claim
of unchanged-source equality for a changed AX formula word.

No mathematical overstatement was found in the reviewed composition README's
explicit scope. It states 246 working states, names its inherited source and
safe-root calibration, supplies an ordinary certificate argument, and leaves
the exact-table Lean endpoint and arithmetized PA proof separate. Its changed
row sets being disjoint is correctly not treated as sufficient proof; the
all-case replay closes that compatibility question. Its rejection search is
also correctly restricted to the searched family and is not a lower bound.

This review inspected the proof structure and checker source. It did not
repeat the archived exhaustive whole-frame checks or recompile the upstream
Rocq/Lean development. The recorded finite outputs remain claims of their
identified checkers, whose soundness is justified by the displayed ordinary
induction arguments; they are not new kernel-checked proofs.

## 4. Final report and the distinct role201 source

Sections 3--6 of the final draft `report/report.tex` were independently
reviewed. The selector exponents, Discard/GEN/MP compiler blocks, successful
word padding for an advanced counter, four-role occurrence count, and
inverse parameter tuple are correct. The DROP/NIP argument was clarified
as the encoded input x=0, so it cannot be confused with the retained
additive register d. No substantive mathematical repair was needed.

The distinct source in the accompanying source-search packet is
`focused_milp_results/dictionary_max24_freq2_zero7_depth64_old1.json`, SHA-256

    5a46a9f287b77dcdb2c6b51959efdc4a1677fd466d60a134b3e2b7f4babde19f.

It changes only rho8 by exchanging a and b, giving

    ((c -> u) -> b) -> ((b -> c) -> (a -> c)).

The change is one of the proved safe role maps. The source checker compares
the complete closed-association normal form with that exact replacement,
and validates all source nodes and operation tags. Its recorded 201 reachable
nodes, 6,460 leaves, 1,931 decrement occurrences, maximum zero run 7, and
maximum leaf depth 39 are consistent with the delivered source fixture.
The time-limited solver's feasible incumbent is not an optimality result.

The source-search packet additionally supplies `check_macro_bridge.py` and
`macro_bridge.json`: all 15 reused AX helpers are compared with the original
219-node helper program, through 292 finite related pairs. This review
inspected that checker and its result. Between decrement tests, its segments
contain only increments and control movement. Matching increment
multiplicities therefore gives equal complete register vectors at matching
tests for every natural initial vector. Matching tested registers makes the
same guard hold, and both successor pairs are checked. The explicit halt
continuation compares complete helper return behavior. This is a sound
ordinary all-natural-register bisimulation argument and strengthens the
formula-stack check; it is still a source-level result.

The report correctly distinguishes this changed source from the prior
202-node reassociation used by the composed 246-state table. Its diagnostic
count of 168 inherited modal entries plus 24 novel node normal forms gives
192; adding a particular inherited 55-state contribution gives the quoted
247 estimate. Reuse of inherited entries still depends on their input tape
contexts. Neither that estimate nor the 201-node source count bounds the
states of every correct compilation. No sub-246 machine or exact binary
simulation certificate is inferred from them.
