# Novelty audit for the 2026-10-26 additional Lean review

## Pinned scope and method

Repository pin: `9d9d1123b39927d30363f1dcd53c23f0575c30ee`.
Scope: every tracked file under `Computability/DiophantineConsistency/research/lean-proof-simplification` and all five ZIPs currently in `docs/incoming`. There are 36 dated placed packets, a through zj. The initial tracked-path census gave 2,175 paths across both requested locations. Text extraction (including ZIP source snapshots and data) yielded 3,768 entries, 2,874 distinct SHA-256 hashes, 76,335,006 total uncompressed bytes. These counts include duplicate earlier reports bundled inside later packets and are not a count of new ideas.

All `.tex`, `.md`, `.txt`, `.lean`, `.patch`, `.json`, `.csv`, and `.tsv` members were inventoried with provenance. Full prose is in `audit/corpus.txt`; direct report prose in `audit/reports.txt` (127 component files, about 1.56 MB); report headings in `audit/headings.txt` and `audit/report_sections.txt`; hashes in `audit/manifest.json`. A redundant full JSON corpus was removed to reduce disk use. Scripts in old packets were not executed. No applicable AGENTS.md exists in these paths (the repository has only three unrelated AGENTS files).

Review method: inspect complete title/section census, read closest report mechanisms and candidate source when screening a new idea, and distinguish source snapshots from actual proposals. A reference to a module in a bundled source list alone does not make every later edit to it a duplicate. Conversely, an old proposal counts as excluded even when never compiled, not adopted, or suggested as future work. Semantic novelty is relative to this pinned inspected corpus, not an assertion of mathematical originality.

## Saturated families

1. **Generic proof administration:** assignment naturality, witness-block transport, finite sum/sum-of-squares facts, graph projections, list lookup library reuse, PR congruence, scanner/iterator invariants, and finite-state verified histories.
2. **Circuit architecture:** generated Steps proof compression, indexed wrappers, power certificates, shared free-carrier tail, DAG invariant induction, cutpoints, shared translation dispatch, native row normalizers, structural degree and representation-depth budgets.
3. **Object arithmetic:** shared ZFC-model extraction, compositional exact formula specs, zero/successor reuse, internal unique existence and preservation/fusion, multiplication order before discreteness, Boolean idempotence by cancellation, order from its strict part, successor membership as discreteness, internal polynomial identity transfer, quantification by restriction surjectivity.
4. **Native arithmetic:** coefficient envelopes, linear coefficient bound applied twice for squares, isolated coefficient fibres, support degree before coefficient vanishing, convolution/rotation via impulses, quotient/remainder local normalization, exact signed prefix borrowing, coherent word/window/carry records, fixed-point carry existence/uniqueness and local reset-based characterization.
5. **Pell/large powers:** sign-congruence relation, parity reuse, base comparison using positive recurrence, common error-factor upper estimate, positive scale factoring, natural perturbation/power sandwich, fixed index-six anchor, quadratic substitution for scalar power inequalities, exact integer quotient recovery, small-ordinate minimality.
6. **Finite tilings:** finite invariant inverse, classifier/fibre interfaces, first failure/first exit, period-one and two-dimensional helical periodicity, canonical quotient construction, shared-edge rows, receiver causality, exact extracted/construction tile equality, temporal seam normalization and shared halted-color witnesses.
7. **Recent controller/word work:** literal modular kernel certificate and unit derivation, exact-order/LTE interface, power fixed-point iteration, canonical residue APIs, physical support rigidity, finite weighted point mutation, reflected-source at zero, scalar depth definitional equality, direct homogeneous Jones-star enumeration.

## Packet-by-packet proposal map

Paths below are relative to the lean-proof-simplification root; a letter denotes `2026-10-26<letter>/`.

| Packet | Main actual ideas that are already baseline |
|---|---|
| a | PR congruence, assignment map, list lookup, residual sums, generated Steps, circuit invariant, scanner/Boolean APIs, exact carry/phase primitives, object semantic bridge. |
| b | Witness layouts, validated folds, circuit/power certificate dispatch, exact finite fixture assembly, shared native geometry, object semantic boundary. |
| c | Expression renaming, half-radix identity, coefficient majorants, register cuts, 99-node tail, scanner/fragment iteration, residual compilers, row operations, object transport. |
| d | Assignment naturality, coefficient-envelope schema, scaled division, finite-fibre folded stencil identity, scanner soundness, circuit certificates. |
| e | ArithmeticDAG/FirstPell/Carrier local cleanup; exact algebra instead of repeated search; generic induction/domain transport; scanner bridge; finite rule dispatch; shared tail; coherent native facts. |
| f | Local coefficient specialization, finite support facts, predecessor powers, nine-coordinate packaging, named conjunctions, current-window interface, generated circuit schemas, audits. |
| g | Half-radix, residual zero-set lift, exact carries/moduli, scanner simulation, circuit certificates, origin correction, injective sparse placement, object induction infrastructure. |
| h | Coefficient schema, list/sum/cast API reuse, decoder outcomes, assignment transport, residual degree sharing, scanner/history, semantic sealing, cyclic boundary. |
| i | Exact rational-root descent, product units, exact decoder graph, finite invariant predecessor, degree before coefficient, rotation as point-mass convolution, PR composition, finite-max normalization. |
| j | Decoder graph, sign ambiguity relation, constructor views and internal unique existence, definable recursive preservation/fusion, depth certificates, explicit cyclic carries. |
| k | Finite-support classification, Pell parity, inverse pairing via product equivalence, shared external natural Euclidean certificate, depth/composition budget, signed congruence. |
| l | Two internal induction deletions, parity, abstract divisibility witnesses, Pell-base comparison, integer norm, inverse finite invariance. |
| m | Rational-root preservation, small-ordinate Pell, parity/sign relation, pairing existential projections, Boolean certificate consumption in representations, positive-tail physical permutation. |
| n | Total raw parent decoder, joint quote/depth decoder invariant, South prefix specializations, binary word congruence, north boundary classification, bounded quantification. |
| o | Existing binary prefix and cycle witness, high-color classifier, exact boundary fibres, original-selector characterization of marked assignment. Contains copies of i/j/k/g reports too. |
| p | Pell error-factor estimate; arbitrary-premise proof fragments; successor-first fork certificates; quotient support separation; canonical pairing witnesses. |
| q | Unused internal induction deletion, negative Pell obstruction from positive units, residue obstruction reuse, minimum saturation, monotone local certificates. |
| r | Positive pair recurrence, Pell natural perturbation/power sandwich, exact integer quotient recovery, rule schedule with two interpreters. |
| s | Compositional exact object specs, scaled Pell comparisons, error-budget integer recovery, observed internal certificate closure. |
| t | List codec identification, local coefficient fibres, second Pell coordinate magnitude, first-exit minimality. |
| u | Parameterized Pell allowance, stronger native rank envelope, integer induction at a point, first failure and valid prefix, structural horizontal matching, absolute trace bounds. |
| v | Reflection through encoding injectivity; local machine direction cases; translated integer induction; shared edge pulse. |
| w | Helical lattice-period algebra, formal two-radicand polynomial identity, twisted-band equivalence, shared-edge rows. |
| x | Constructor-minimum formula bound, strict multiplication before discrete arithmetic, Boolean idempotence by cancellation, period-one rigidity, exact canonical quotient before existential erasure. |
| y | Span-before-support, helix period, strip-width period lower bound, output-based pairing branch, constructor equation in list-head bound, geometric sums, strict-order foundation; Sidon polarization supplement. |
| z | Helical orbits, fixed index-six Pell anchor, signal-mass color statistics, canonical operating-row recognition. |
| za | Direct wall bounds, actual receiver causality without temporal matching, exact interior row tile equality with constructed stepTile. |
| zb | Signed periodic orbit, coprime divisibility, geometric bound from identity, positive quadratic margin interval, signed finite-prefix borrow, native affine scalar rank. |
| zc | Coefficient bound composition rather than square expansion; scalar power inequalities without induction; computed allowed-tile index. |
| zd | Selector cutoff by logical duality; prime-divisor order certificates; bounded color complement cancellation; conditional numeric control-slot invariant. |
| ze | Five existing Jones eval lemmas, thirteen-coordinate carrier cleanup, helical periodicity, list-sum monomial semantics, eliminate determined function witnesses. |
| zf | Multiplication zero via law; discrete order from set successor membership; ObjectDivision **existence** successor/value bridges; linear coefficient bound twice; quadratic power threshold. |
| zg | Internal polynomial identity transport, sparse monomial-sum view, quantifier restriction surjectivity, residual exponent order obstruction. |
| zh | Finite-ordinal physical rigidity, controller cardinality divisibility, delete one-use Hs helper, exact marker response in terminal band. |
| zi | Shared halted-color witness; old period/band/seam ideas explicitly withdrawn by late audit. |
| zj | Finite-order rigidity, canonical residue APIs for controller proofs, nonzero integer certificate without sign split, source positivity from selection without marking. |

## Five pending ZIPs, all excluded

| ZIP | Distinct proposals |
|---|---|
| `Lean_Proof_Simplification_Power_And_Masks_2026-10-26.zip` | Guarded power cast fusion; CRT order clients and removal of order_transport; optional Gamma positivity via unit/coprimality; bit3 residue-to-bit simplifier. |
| `ProveIt_Lean_Simplification_Round5_2026-10-26.zip` | Sidon injectivity endpoint normalization; exact order at exponent zero; direct definitional depth equality. |
| `diophantine-lean-new-obligations-2026-10-26.zip` | Share Jones finalizer evaluation; one affine floor lemma with reflected soundness; generate homogeneous Jones star directly; fixed powers rather than least orders for controller clients. |
| `lean-proof-simplifications-2026-10-26.zip` | Common fixed modular kernel/unit certificate; LTE spectrum primary; characterize carries between resets; quadratic substitution in sixteen_pow_bound. |
| `proveit-lean-additional-certificates-2026-10-26.zip` | Common residue-ring kernel certificate; power fixed-point iteration; finite weighted point update; reflected source at offset zero; controller-unit synthesis. |

## Candidate novelty judgments for this iteration

### Retain: ObjectDivision.quotient_not_lt by cancelling the common quotient block

Existing proof introduces q'-q-1 and d-r-1 slack witnesses and manufactures an impossible equation n=n+positive. The retained proof uses only the first gap q'=q+s+1. From the two division equations, cancel the common q*d term to obtain r=s*d+d+r'. Nonnegativity gives d≤r, contradicting the existing r<d. It needs neither multiplication monotonicity nor a second remainder-gap witness. This is a residual simplification of internal quotient uniqueness, **not** another Euclidean certificate proposal. k handles external ℕ RegisterDivMod/QuadraticDivMod through Nat.div_mod_unique; zf alters internal existence, not uniqueness. Check source variants confirms all earlier ObjectDivision candidates retain original quotient_not_lt. Preserve arbitrary/nonstandard internal omega; no Archimedean or Nat-isomorphism premise.

### Retain: ObjectZeroTest.certificate_sound from its product and reconstruction rows

Old proof consumes bit²=bit to split zero/one. New proof consumes bit*n=0 and n+bit*(slack+1)=slack+1 directly: if n≠0, zero-product forces bit=0; if n=0, cancel the nonzero successor to get bit=1. Thus Booleanity is unnecessary for this proof (literal encoded row stays). x's idempotent simplification and m's existential Boolean certificate consumption do not subsume this row dependency elimination; zg transports algebraic identities, not zero-set dependency. All prior ObjectZeroTest.lean copies (two, identical) retain old Boolean-root split. Need successor nonzero and cancellativity in actual internal model.

### Retain: CurrentDummySafety2011.nonwrap_of_short from two strict window bounds

With rho≥2, m≥1, R=rho^(m-1), F<R and delta<R, strict natural slack gives F+delta+2≤2R≤rho*R=rho^m. Hence F+delta<rho^m-1. Original delta<rho^(m-2), m≥2 imply the relaxed bound. Removes quadratic rho+1<rho² detour and unnecessary extra empty field from the generic lemma. Existing incoming reports retain nonwrap as a guard; none supplies this discharge. Novelty credit is for this current-client stronger capacity fact, not generic power cancellation. Radix two endpoint matters.

### Small optional delta: CurrentControllerPositions2011.position_ne_three

The new affine progression is exactly 2+120198*j.val. Direct linear arithmetic (or residue 2 modulo 120198) excludes 3 without a zero/nonzero split and nonlinear arithmetic. Body `change 2 + 120198 * j.val ≠ 3; omega` and the analogous injectivity proof compiled in an exact-domain pilot. Together they remove six physical lines in the complete module (178 to 172), with no helpers/imports. Full production dependency chain was not rebuilt. Generic embeddings or finite injection packages would repeat previous architecture; keep this precise local deletion, not inflated API novelty.

### Caution: CurrentWordRephase2011 normalization transfer

No report mentions this new module, but generic coherent Facts/derived recurrence and transport is already baseline. A new smart constructor that merely assembles Facts is duplicate. A genuinely marginal new statement would need to remove a fresh replay of actual rotation congruence while retaining exact source/carry/digit identities and allowing ordinary multipliers/quotient witness to change. Charge helper cost and reject if previous generic constructor already solves the same obligation for free.

## Recent source areas checked

CurrentDummySafety2011, CurrentControllerPositions2011, CurrentPackingRank2011, CurrentWordRephase2011, and NativePackingPopulation are absent by basename from direct report prose and were inspected. The last module's current 57-line population proof is already compact; a generic sum/aggregation abstraction would largely repeat older ideas. CurrentPackingRank's cast bookkeeping is concrete but existing natural-cast and polynomial identity infrastructure already covers most tempting refactors; no strong additional proposal identified there.

### Retain: exact raw binaryRotation exponent normalization

The algebra agent proved binaryRotation v (W % (v*n)) c = binaryRotation v W c by existing division/remainder identities, with no Boolean/bounded digit, nonzero width or nonzero length premises. This is exact operation-level equality, including total-definition v=0,n=0, unlike packet i packed-word impulse/convolution congruence and unrelated helical tiling periodicity. It yields a new shorter proof of current CurrentWordRephase2011.rotation_eq. Generic modular arithmetic is baseline; novelty is this exact unrestricted raw operation contract and fresh client.
