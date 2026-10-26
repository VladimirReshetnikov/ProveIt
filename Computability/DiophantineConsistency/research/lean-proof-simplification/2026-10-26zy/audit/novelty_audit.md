# Exclusion audit for a further Lean proof-simplification iteration

Source pin: `3299f4aa4c9ae38b0f5a1c00a1f0d23f6cbdb114` (26 October 2026).

## Scope and standard

The designated research directory contains 41 packets, `2026-10-26a` through
`2026-10-26zo`, and 2,507 tracked files in total. `docs/incoming` currently
contains its README retirement/index ledger, not loose ZIPs. The index explicitly
lists all 41 packets and also summarizes older K215 proof-simplification work.
The audit reads the principal report heading inventories, latest cumulative
exclusion taxonomies, current packet READMEs, relevant proposal sections and
candidate-specific text searches. It does not claim a semantic verification of
every old baseline snapshot, compiler log or transitively linked historical
report. The exact read/review scope should be stated in the final report.

All prior mechanisms count whether adopted, uncompiled, deferred, optional or
merely stated as future work. The repository's ADOPTION ledger is useful for
current source status but does not reduce the exclusion set. A new application
of the same generic prior contract is not independently new. A distinct exact
theorem reuse or a stronger contract can qualify if the earlier proposed APIs do
not already settle the same obligation. Avoid interpreting generic advice to
search for stronger lemmas as excluding every future local simplification.

There is no unique compiled checkout containing every mutually alternative
historical proposal. Savings can be measured against the pinned actual source;
counterfactual additional benefit must be argued separately and must not reclaim
old patch reductions.

## Principal exclusion taxonomy

1. **PR programs and scanners.** Nat.rec and iterator congruence; extensional PR
   composition automation; fixed-state and scanner simulation laws; generic
   invariant-preserving history folds with separate input/output types; exact
   numeric Boolean interfaces; finite tag dispatch; a shared rule-schedule DSL
   with numeric and primitive-recursive interpretations. Relevant packets: a-h,
   i, n, r.
2. **Syntax, decoding, and certificates.** Standard list lookup APIs and
   Encodable list codec identification; successful Option elimination; exact
   decoder graphs; quotation/depth invariant fusion; raw/typed parent decoding
   equivalence; known-constructor BoundStep views; fused internal unique
   existence; internal recursive-graph preservation/fusion; formula constructor
   minima; list-head bounds from constructor equations. Relevant: h-j, n, t, x,
   y. Also count the less visible constructor-view and zero-pair suggestions in
   h/evidence/syntax/findings.txt.
3. **Representations and witness administration.** Assignment naturality;
   prefix/suffix witness layouts; early witness-count projections; canonical
   pairing certificates; inverse graphs from product equivalences;
   composition arithmetic budgets and max-plus depth certificates; exact
   Boolean-certificate consumption; arbitrary-premise proof fragments;
   deterministic function-witness elimination. Relevant: a-h, j, k, m, p, ze.
4. **DAGs, compilers, and polynomial syntax.** Shared topological invariant,
   power-label certificates, semantic blocks and indexed facades; generic gate
   semantics; finite residual-square aggregation; translations and commutative
   swaps; structural/cancellation-aware degrees; sparse row reflection;
   coefficient naturality under ring maps; shared free-carrier tail;
   interpretation of monomial lists as a list sum; direct homogeneous
   antidiagonal enumeration. Relevant: a-h, t, ze, zg, zk.
5. **Object arithmetic and logic.** Completeness/sealing bridge, ZFC-model to
   ZF-axioms reuse, arity-polymorphic closed transport, explicit definable
   induction; remove induction with unused induction hypothesis; compositional
   exact object-formula specifications; closure of certificate sets; internal
   semiring evaluator; strict order from additive differences; reconstruct
   order from strict part; discrete order from successor membership;
   polynomial split-zero transport over cancellative semirings; surjective
   environment restriction. Relevant: a-h, j, l, q, s, x, y, zf, zg.
6. **Pell and finalizer arithmetic.** Exact signed rational-root descent;
   integer norm nonvanishing; product units; small-ordinate minimality; parity
   theorem reuse; positive pair recurrence and base comparison; positive scale,
   parameterized error factors and power-sandwich budgets; compositional signed
   congruence; exact half-binomial integer rounding; fixed index-six anchor;
   positive margin interpreted as interval bounds; common-power quadratic
   threshold reductions; affine carrier domination/reflection; algebraic
   two-radicand identity before evaluation. Relevant: i-m, p-u, w, z, zb, zc,
   ze, zf, zk, zo.
7. **Coefficient/support algebra.** Shared row envelopes and finite majorant
   certificates, finite chunk assembly, copied-field bounds; local coefficient
   fiber identity, pushforward/fiber sums; support envelope before individual
   coefficients; quotient-hom support separation; multiplication as a linear
   coefficient action, compose twice for squares and extend to powers. Relevant:
   a-h, i, p, t, y, zc, zf.
8. **Words, carries and masks.** Exact local carry decomposition and derived
   recurrence; finite maximum/least or greatest global carry characterization;
   conditional padding; cyclic residue APIs and scaled div/mod; half-radix
   identity; origin correction; point-mass rotation; binary-word congruence;
   sufficient color statistics for signal masses; exact signed-prefix borrow;
   independent numeric control-slot invariants; weighted point updates; marker
   terminal response; selected-digit source positivity; per-cell synchronized
   reset fold and edit locality. Relevant: a-h, i, j, n, z, zb, zd, zh, zj, zn,
   zo.
9. **Wang/machine geometry.** Finite invariant predecessor, finite-state ranking
   and SCC certificates; first failure with valid prefix; centered/translated
   integer interval induction; reflect halt through injectivity; split machine
   cases only at write site; exact absolute-value views; shared horizontal bond
   fields/pulse; period lattice and period-one helical orbits; helical band
   coordinate equivalence; whole receive-tile recognition and canonical
   operating rows; canonical quotient decoder; finite ordinal rigidity;
   halted pass/finish shared witness. Relevant: h, i, l, n, o, t-za, zc, zh-zi.
10. **Controller/residue arithmetic.** CRT and divisibility transport,
    finite-prime exact-order certificates, direct canonical-representative
    lemmas, guarded power-cast fusion, weaker fixed-power facts and exact-order
    endpoint reuse; exponent-map fixed points; common-modulus literal K table
    certificates; whole-polynomial Gamma residue certificates; LTE full
    prime-power divisibility spectrum; translated fixed-cardinality subset-sum
    interface. Relevant: n, zd, zg, zh, zj-zo.

## Packet-by-packet addition ledger

The following lists the principal additions rather than repeating every shared
mechanism from the preceding taxonomy. A packet can itself contain duplicates
of an earlier one; every listed mechanism is nonetheless excluded now.

| Packet suffix | Principal mechanisms or additions |
|---|---|
| a | PR congruence, list API, assignment naturality, residual aggregation, generated circuit certificates, scanner iteration, half-radix, local carry decomposition, object semantic bridge |
| b | Witness layouts and early projections, validated history folds, finite chunk assembly, recurrence as a derived field, copied-field bounds |
| c | Coefficient majorants/naturality, shared 99-node free-carrier tail, simulation/row reflection, coherent current-window facts |
| d | Finite-fiber folded stencil identity, coefficient envelopes, cyclic-block API and shared circuit soundness |
| e | DAG and carrier algebra simplifications, standard library checker cleanups, shared semantic interfaces |
| f | Nine-coordinate packaging, named conjunction views, source/scalar-window coherence, degree profiles, staged coefficient-expression centralization |
| g | Pointwise zero-set lifting, generic scanners, shared origin correction, arbitrary folding versus injective placement |
| h | Successful decoder elimination, arbitrary raw-input soundness, internal evaluator reuse, finite-state ranking/SCC directions |
| i | Exact root descent, product units, exact tree decoder graph, finite invariant predecessor, support envelope, rotation impulse, canonical carry maximum |
| j | Compositional signed congruence, internal constructor views/unique existence, recursive-graph preservation/fusion, max-plus depth, explicit extremal carries |
| k | Finite-support classification, Pell parity reuse, inverse product graph, Euclidean certificate uniqueness/coherence, composition budget |
| l | Delete unused internal inductions, retain abstract divisibility witnesses, Pell parameter comparison, integer norm proof, inverse finite-set invariance |
| m | Small-ordinate Pell minimality, exact root descent and inverse pairing, consume Boolean certificates, physical permutation as positive tail |
| n | Total parent decoding, quotation/depth fusion, zero-cycle specialization, South-prefix reuse, binary-word congruence, north-boundary equality views, CRT/depth bookkeeping |
| o | Reuse South prefix/cycle witness, classify high-color fibers, selector-based assignment characterization |
| p | Error-factor Pell bound, arbitrary-premise proof fragments, successor-first fork, quotient-hom support separation, canonical square pairing |
| q | Negative Pell obstruction from positive units, residue obstruction reuse, coupled minimum saturation, monotone local certificate calculus |
| r | Positive Pell pair recurrence, natural perturbation/power sandwich, exact half-binomial quotient, shared rule-schedule DSL |
| s | Compositional exact object specifications, scaled Pell comparison, discrete recovery from two error budgets, observed-certificate closure |
| t | Encodable list codec, local coefficient fibers, Pell second-coordinate magnitude, first-exit theorem |
| u | Sharp native rank lower envelope, centered integer induction, first failure with valid prefix, shared Wang bond signal, absolute-value bounds |
| v | Halt-last equivalence and action reflection, write-site cases, translated interval induction, edge pulse |
| w | Helical period lattice, algebraic two-radicand identity, canonical band equivalence, shared-edge row construction |
| x | Constructor-minimum formula threshold, strict multiplication before discreteness, period-one functions, retain exact band witness |
| y | Span cutoff before support cases, 2D helix and strip-width period bound, pairing branch from square shell, list-head constructor bound, geometric-sum reuse, strict order, Sidon polarization |
| z | Fixed-anchor Pell threshold, signal masses through color statistics, canonical operating-row recognition |
| za | Direct wall bounds, actual receive-tile causality, extraction/construction equality |
| zb | Coprime-divisibility interface, exact geometric bound, quadratic margin intervals, signed-prefix borrow, scalar affine native rank |
| zc | Compose coefficient action twice, scalar power threshold shifts, computable canonical tile index |
| zd | Selector-tail logical duality, prime-divisor order certificates, bounded complement injectivity, independent control-slot update invariants |
| ze | Shared Jones evaluation, positive carrier norm gap/affine bound, list-sum monomial semantics, deterministic function-witness elimination |
| zf | Multiplication-at-zero specialization, successor-based discrete order, coefficient action, quadratic power substitution |
| zg | Cancellative-semiring split-zero transport, list sums, environment restriction, residual-exponent order obstruction and block-power classification |
| zh | Finite ordinal rigidity/Fin.pred, direct coprime cardinality, inline small residues, exact marker-only terminal response |
| zi | Shared halted-color allowedness for pass/finish; superseded period and band ideas still excluded |
| zj | Finite ordinal rigidity, canonical residue APIs, integer square positivity, source positivity from selected digit with API migration |
| zk | Jones evaluation, affine carrier reflection, direct homogeneous antidiagonal enumeration, fixed powers instead of exact-order dependencies |
| zl | Guarded power-cast fusion, exact-order endpoints, bit-test residue transport, Gamma positivity from coprimality |
| zm | Sidon injectivity endpoints, controller order-one endpoint, definitional iterator depth |
| zn | Common-modulus K certificate, exponent fixed point, weighted point update, reflected-origin theorem reuse |
| zo | Gamma universal residue certificate, full LTE spectrum, synchronized per-cell carry reset/locality, quadratic Pell threshold |

## Less visible exclusions and candidate search guidance

Read `2026-10-26h/evidence/syntax/findings.txt`, j's prior-idea notes,
q's prior-proposal audit, t's exclusion ledger, v's assumed baseline, and the
latest zn/zo taxonomies before endorsing an apparently new generic structure.
Latest zn explicitly mentions Grothendieck/ordered-ring completion and a
noncoprime affine-fiber equivalence as possible directions. They cannot now be
advertised as previously unexplored solely because no patch was delivered.

The incoming index also mentions K215 common macros, collection-first assembly,
native replacement, proof fusion/boundaries, checked affine cores, quotient
detachment, semantic normal forms, ordinary bisimulation, automatic certificates
and composition-address bounds. A report should avoid rebranding these general
architectures as new DiophantineConsistency ideas without a materially different
contract and concrete target.

For each proposed new candidate, record: exact current declaration; earlier
closest contract; whether that contract immediately discharges the proof; the
new mathematical statement or normal form; helper/import/client cost; preservation
of data and public theorem type; and actual checking scope. Search both narrative
and proposal/source artifacts for the mechanism, then inspect each close match.

## No unsupported novelty endorsements

This audit identifies exclusions, not a proved absence of all possible prior art.
No new candidate is endorsed merely because its theorem name is absent from a
report. Candidate-specific gate decisions should be appended after the other
review agents supply exact proposals.

## Candidate gates during this iteration

### S1: derive primitive recursiveness from the existing direct scalar realizer

**Decision: provisionally retain the narrow mechanism, subject to dependency and
exact-data checks.** The proposed target is the private extensional `pr_*`
chain in `Computability.lean`, culminating in `haltingTest_natPrimrec`.
`DirectScalarEnumerator.program` already realizes the same `haltingTest`.
The proposal moves the raw semantic definitions/bridges into a lower module,
lets the direct scalar program depend on that module, and then derives
`Nat.Primrec haltingTest` using `ScalarPRCode.primrec` and the realization
equality. It thereby deletes an independent certification pipeline.

Closest prior: packet i, report lines 313-346, proposes using `fun_prop` for
the constructor composition proofs in the same `Computability.lean`. That
proposal maintains the extensional chain and explicitly leaves recursive
program construction and realization proofs explicit. S1's contribution is
to make the existing concrete realizer the sole source of the extensional
primitive-recursiveness theorem. It is not another automation proposal.

Targeted searches of narrative/technical-note/proposal files found no earlier
`DirectScalarEnumerator` or `haltingTest_natPrimrec` dependency-reversal
proposal; occurrences outside current sources were inventories and endpoint
axiom checks. This is bounded absence evidence, not a universal originality
claim. Verify the full import closure for cycles, preserve all computation
definitions and exact program syntax, retain theorem types, and charge the
new semantic split. Report actual source savings separately from hypothetical
post-`fun_prop` savings.

### A1: polynomial row-operation traces for triangular source elimination

**Decision: exclude as a new mechanism.** The proposed elementary shears and
invertible polynomial row combinations for `NativeArithmetic52.eq_lift_of_zero`
are covered by packet c, report lines 774-808 and `notes/arithmetic.txt`
around line 112. The report gives elementary row-addition zero-set equivalence
and explicitly suggests arbitrary invertible linear combinations as a later
matrix-based extension. Packet z records this as exclusion L51. Applying that
same algebraic structure to a triangular native-source system does not meet
the user's non-repetition requirement.

### B1: use only the needed lower bound in `source_Y_ge_two`

**Decision: retain only a narrowly stated residual simplification.** Packet b,
report lines 617-641, already names this exact target and proposes shared
semantic equations `q=1+J*beta`, `L=q^2-1`, and `N=q*(1+L)=q^3`.
Consequently removal of repeated row unfolding and casts is not new.

The stronger standalone observation is that positivity of N and L and row 1, namely
`N = q * (1 + L)`, force the integer q to be positive. Therefore `q >= 1`
and `N >= 2`; positivity of the final multiplier then gives `N*s >= 2`.
No sign hypothesis on beta is needed. Row 0, `q >= 2`, `L >= 3`, and the
cubic consequence `N >= 8` are not needed.
After the old semantic equation interface is assumed present, this remains a
contraction of the mathematical dependency set rather than a new equation
decoding API. A minimal-premise standalone lemma can document the stronger
contract; full helper costs and client costs must be counted. Keep the old
public statement if offering a proof-only patch. Distinguish savings against
the current 21-physical-line declaration from the smaller, implementation-dependent
residual saving after packet b's promised interface. The supplied compatibility
patch uses 13 physical declaration lines, an eight-line reduction against this
actual pin. That shorter compatibility proof still consumes `hβ.le` in
`mul_nonneg`; its improvement is removing row 0 and the unnecessarily strong
intermediate bounds. Only the stronger standalone variant eliminates all
beta-sign dependence. The 21-to-13 measurement does not measure that variant.

### C1: finite radix prefix bound via the digit-length library theorem

**Decision: exclude.** Replacing `CurrentWordTopBounds2011.range_word_lt`
with `Nat.ofDigits_lt_base_pow_length` and `ofDigits_map_range` is covered
by packet zo's explicit rejected candidate C9 in `audit/novelty_decisions.json`
and `audit/NOVELTY_DECISIONS.md`: finite radix prefix bounds by generic digit
length, range or library geometry. Packet i's `proposed/SelectiveCarry.lean`
also already uses the library inequality. A new exact target name does not
change this mechanism.

### C2: additive structure on aligned cells

**Decision: exclude.** Recasting the aligned-cell type as a subgroup/kernel,
strengthening its equivalence to `ZMod N` into an additive equivalence, and
obtaining translations or orbit proofs from a group action have already been
proposed or explicitly excluded: packet b report lines 613-615, i report near
117, k's novelty audit E35, r's report, and u's audit E34. The current
`CurrentCellCoordinate2011` and `CurrentCellCycle2011` proofs may be clients
of this idea but cannot make the idea new.

### C3: project the whole kernel modulo two for copy parity

**Decision: exclude.** Packet zj's
`evidence/current_controller_findings.md` near line 129 explicitly records
whole-kernel reduction modulo two as a repeat of earlier scalar projection
and carry-parity proposals. Applying it to `CurrentCopyParity2011` is
therefore not a new proposal. The same note also records a noncoprime affine
projection-fiber equivalence as an explored extension; its lack of an adopted
patch does not erase the prior mention.

### B2: discharge the beta guard from positive source zeros

**Decision: provisionally retain, as a second application of B1's arithmetic
family rather than an independent family.** The old and gap source systems
both imply `L = q^2 - 1`, where `q = 1 + beta*J`. Their second rows give,
respectively, `N = q*(1+L)` and `Ngap = q*L`. Positivity of the coordinates
forces `q > 0`, then `q > 1`, and therefore `beta > 0`. The external beta
guard is redundant on either positive-zero subtype. The concrete proposal
is to expose the corresponding `GapSource66` equivalence and existence
equivalences for every port tuple, recovering the guard from the input
solution in each direction.

Packet b's source-register decoding already supplies the identities and
must be credited for them. It does not state that positive zeros force the
external beta port positive. Packet f's derived `PortBounds.beta_pos`
projects an already stronger external bound, so it does not discharge a
guard from the defining equations. Packet zj strengthens assembled-word
positivity by using a selected digit without a marked-origin assumption;
that concerns a different source-construction theorem and supplies neither
this port-sign fact nor an unconditional zero-set equivalence.

Targeted narrative and technical-note searches found no earlier endogenous
beta-sign recovery or elimination of this positive-zero equivalence guard.
The generic guard-discharge equivalence is routine transport, not a novelty
claim. Do not weaken `toOld_positive` for arbitrary positive tuples: without
the zero equations there is no solution-dependent sign proof. Preserve old
guarded wrappers where compatibility matters, and report their complete
helper cost rather than claiming an automatic net line decrease.

## Final machine-readable evidence and independent static check

`novelty_decisions.json` records the three retained proposals in two disclosed
families, their closest earlier passages with exact pinned paths and line spans,
explicit non-claims, five rejected directions, and bounded review language.
`source_inventory.json` derives packet and file counts from Git's tracked tree
at the source pin: 41 packet directories, 2,507 research files, one incoming
README, and 702 maintained Lean files. It lists every packet with aggregate
counts rather than dumping all historical file paths.

The independent static S1 review follows the proposed imports through 19
project modules and finds no cycle or unresolved project import. Mathlib and
Lean imports are explicit graph boundaries. The proposed
`DirectScalarEnumerator.lean` equals the pinned file with exactly one import
replacement; every byte after its import block is unchanged. Fourteen project
dependency sources missing from the sparse checkout were retrieved at the
exact source pin and checked against their Git blob identifiers. The evidence
is `s1_independent_static_review.json`; `audit_inventory.py` replays this check.
This proves neither elaboration of moved declarations/private instances nor
compilation of the three-file split. Those remain integration gates.
