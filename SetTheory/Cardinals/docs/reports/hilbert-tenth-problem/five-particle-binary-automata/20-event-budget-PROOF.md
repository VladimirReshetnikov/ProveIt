# Event-budgeted quartic schemas for exact finite CA iteration

## Status

This is a new theorem-level finite circuit construction, plus an implemented **mass-two specialization** and a general finite-slot scheduler reference. It is not a completed arbitrary-mass coefficient exporter. The distinction is substantive: the general macro bounds below are proved from explicit bounded loops, whereas the sample coefficient counts are emitted and checked mechanically. No earlier report is altered, and no novelty or minimality claim is made.

The dependency is the frozen CA and its all-finite-support lazy evaluation theorem in `dependencies/report19-proof.md`. The checked evaluator SHA-256 is `42e8aa65c05fcf373a03a02be51ebb89a4fdcb1f1070ad776ffe1e8e99049c61`; its pinned original compiler SHA-256 is `f95a6028c9d3cc6f8b0b497cfc0cad68104da6d70e55205df04ad234e5d0c76f`.

The arithmetic layer is the direct canonical comparison/SOS method already present in `dependencies/report8-core.tex`, together with the signed constant-divisor construction in `dependencies/report8-semilinearity.tex`. No MRDP theorem or external existence result is needed.

## 1. Precise finite theorem

Fix one accepted finite source S. Use its original m controls, p moving and a direct branches, b=p+a, guard cutoff J, and constants

D=2m+4p, S0=2D+2, L0=3D+4, B3=4D+5,
Z=10B3+10+2J, F=8pD+29p+m+a.

Write Delta for the maximum length of a signed home-mode incidence list: outgoing dispatch/direct entries or incoming commit/direct entries. There are exactly 2b actual incidence records in total. Write c=(J+2)^2 and S_tab=m+b+2bc+1. Source names/guard syntax and their actual byte lengths are additional setup data, not zero-cost constants.

Fix an exact particle count n, finite CA horizon T, and total **changing-factor** budget K, all as compiler parameters. For T>0 the construction uses R=T+K rounds. Initial input is a strictly increasing tuple of n integer coordinates, represented externally by canonical natural pairs x_i=x_i^+−x_i^- with x_i^+x_i^-=0. Those 2n coordinates are inputs, not existential auxiliaries. An endpoint, if requested, is another prescribed sorted n-tuple of integer coordinates.

There is an effectively generated ordinary integer polynomial P=sum rho_j^2, with all rho_j of degree at most two, having the following properties for each fixed admissible input:

1. P has one complete natural auxiliary witness exactly when the literal ordered CA product can be iterated T times with at most K changing factors in total, and, if requested, the endpoint is the specified target.
2. Otherwise its natural auxiliary fiber is empty.
3. The witness uniquely reconstructs each changing factor, every complete pre-factor snapshot, all candidate/guard/isolation decisions, the distinct no-future-change check completing each CA step, and deterministic idle padding.
4. No witness array, constant truth table, or source lookup is indexed by all F factors. F is stored as an ordinary binary integer. The actual source records and guard tables are charged explicitly.
5. Quantified dimension grows with n,T,K and source size. This is not one fixed-arity polynomial with an unknown horizon, a finite-fold theorem for arbitrary recursively enumerable sets, or a certificate for infinite-support configurations.

For T=0, on the stated externally admissible sorted input domain, one can use just endpoint equations and no existential witness. If arbitrary input tuples must also be rejected internally, strict-order checks add comparison auxiliaries; that version is not witness-free. For n=0 or n=1, every factor is the identity because every endpoint has at least two particles; a zero-witness identity specialization is available. The uniform scheduler also handles these cases with zero candidate slots and T completion rounds.

The event budget is fixed syntax, not an existential choice. Different choices of K produce different polynomials; they do not create different witnesses inside one fiber.

## 2. Canonical quadratic primitive compiler

Every signed integer wire is represented by a pair v^+,v^- of natural variables with value v=v^+−v^-. Signed arithmetic assignment v=f, for a binary-fanin addition, subtraction, multiplication, multiplication by a fixed integer, or Boolean selection, emits

v^+−v^-−f=0,  v^+v^-=0.

For fixed preceding wires this has exactly one natural solution. Selection is f=u+e(w−u), where e is an already determined Boolean wire. Each f has degree at most two in previously materialized wires. Long sums are expanded into binary-fanin assignments; multiplication of already quadratic expressions requires a new materialized wire first.

Comparison of two signed integer wires x,y uses natural b,d and residuals

b(b−1),  y−x−(2b−1)d−b+1.

The unique values are b=1,d=y−x if y>=x, and b=0,d=x−y−1 otherwise. Signed inputs cause no difficulty. Equality is obtained by the two comparisons y>=x and y>=x+1 and by materializing the difference of their flags as a Boolean wire. Ties therefore have a prescribed outcome. Order is not an implicit polynomial primitive.

Constant division by d>=1 uses natural q^+,q^-,r,h and residuals

q^+q^-,  v−d(q^+−q^-)−r,  r+h−(d−1).

These uniquely impose the Euclidean quotient and 0<=r<d, including negative inputs and d=1. Floor and remainder are not implicit primitives, and the bit length of d is charged. Only division by fixed source constants is used.

A Boolean AND, OR, NOT, or affine-copy gate has one natural output z and one defining residual z−uv, z−u−v+uv, z−1+u, or the appropriate affine equation. Its operands are already determined Boolean wires. Their Booleanity follows inductively; nothing is left existentially free. An equality-flag copy has residual z−b_weak+b_strict. No large-arity Boolean gate is costed as one operation.

Let A,I,Dv,G be the actual numbers of signed arithmetic assignments, comparisons, constant divisions, and Boolean gates in this fully unfolded circuit. Let Q be the number of final acceptance or external-input admissibility residuals. Then the exact compiler ledger is

V=2A+2I+4Dv+G natural auxiliary variables,
E=2A+2I+3Dv+G+Q residual slots.

With each signed operand stored as a two-variable wire, Boolean operands as single wires, and checks with at most four monomial terms, an explicit coefficient-list bound is

residual monomial slots <=9A+10I+9Dv+4G+4Q,
ordered expanded-square term occurrences <=65A+68I+35Dv+16G+16Q.

The first row of an arithmetic assignment has at most eight terms, its sign-separation row one. A comparator has row lengths at most two and eight. Division has row lengths one,five,three. Boolean rows have at most four terms. Zero/canceling slots may be retained; actual collected counts can be smaller. External sign-separation checks have one term. Thus the quartic is an ordinary coefficient-explicit finite polynomial even before collecting equal monomials.

All gates, including gates below a false mask, are totalized and evaluated. A false mask is not permission to remove the defining equations of its internal wires. Exposed inactive candidate indices equal F, unused descriptor positions equal zero, and idle state equals the previous state. Internal dummy computations have their uniquely forced canonical values; they need not all equal zero.

## 3. A fixed, duplicate-allowed candidate list

For each occupied pair x_i<x_j, inspect d=x_j−x_i. Do not enumerate any integer coordinate interval. Allocate precisely

Delta+3+4 max(n−2,0)

slots per pair, in this fixed order:

- one home-phase slot
- Delta home-incidence slots, padded in the pinned incidence order
- moving free-E and phase-free-P slots
- for each k other than i,j, four slots: behind, ahead, phase-near, interaction

Consequently

C=binom(n,2)[Delta+3+4 max(n−2,0)].

Each slot is (enable,index); disabled indices are fixed to F. The enabled **set** is exactly the candidate set in the pinned evaluator. Duplicates are retained with their fixed slot ranks.

Here are the predicates and arithmetic, with h=x_i, z=x_k, H=h−z, and epsilon=0 for odd d and 1 for even d. For a home gap 1<=d<=2m, q=floor((d−1)/2). The phase slot and its signed incidence list are enabled only when h−S0 is occupied. Incidence records use the pinned order: moving branches in their order-preserving source filter, followed by direct branches in their order-preserving source filter. This need not be the original interleaved source order. For a moving gap 2m<d<=D, divmod(d−2m−1,4) gives the moving branch and O/I/sign. Decode w=e.side for O and −e.side for I. There are always the two free slots. Triple-slot tests are

behind: S0<=wH−epsilon<=L0,
ahead: S0+1<=−wH+epsilon<=L0,
phase-near: S0<=abs(H)<=L0.

The single interaction slot uses the mutually exclusive cases

O plus,H=−e.side*S0: endpoint;
O minus,H=e.side*S0: dispatch;
I plus,H=e.side*S0: commit;
I minus,H=−e.side*S0: endpoint.

Use the exact factor-index formulas from the pinned evaluator proof, section 1. A disabled mode is masked to a dummy mode before division, source lookup, or range-dependent index arithmetic. If p=0, use an explicit constant dummy moving record (side +1) rather than attempting to select a nonexistent record; its enabling bit is false. Similarly, a disabled travel parameter is masked to S0. This avoids partial arithmetic and unnecessary growth from invalid guesses. Abs is a comparator and signed selection, not a primitive.

There is no hidden m*Delta or F table. The 2b incidence records carry their fixed control, sign, rank, and index. Compute the control/sign equality bits for each actual record, then route its contribution to its fixed rank accumulator. Each rank receives either its unique matching index or the sentinel; all additions and masks are charged. Moving-branch attributes are obtained from a linear-size finite multiplexer over p records.

Candidate completeness is the already proved close-pair lemma: every two-particle endpoint contains an occupied close pair; every triple endpoint has exactly one close pair, and its other particle is enumerated as z. Therefore every nonidentity factor is enabled in at least one slot. Factors outside the list have no raw occurrence. The slot construction does not pre-assume isolation, context, well-formed encoding, or a unique head.

## 4. One simultaneous factor evaluation, with every absence test paid

For a candidate slot, decode its actual factor by the arithmetic partitions in gate_at. Quotient/remainder by the fixed E/P block lengths, finitely many comparisons, and source-record selection suffice. This takes source-linear circuit size, not an F-entry lookup. A disabled slot selects gate zero as a dummy and masks its result out. A valid source has F>=1.

A descriptor has two shapes of equal size two or three, their sorted coordinates, B, isolation radius 3B+1, competing-key radius max(4B+1,T_context+B)+1, and the branch/domain-or-image guard identifier. Represent the variable shape length with fixed three-position arrays, masking and zeroing the unused third entry. Sort the three records by presence first and then coordinate using a fixed three-element compare-exchange network, so the unused zero-padded record stays last even when actual coordinates are negative. When b=0, every gate is noncontextual and the unused guard lookup has a fixed true dummy result; no nonexistent table row is accessed.

For each label ell in {0,1} and occupied x_i, form the possible key u=x_i−shape_ell[0]. There are exactly 2n key slots. Its raw bit is the conjunction of:

- presence of all required two/three sites, using equality against every occupied coordinate
- exactly shape_size particles in the inclusive interval [u−B,u+B], using two comparisons per particle and a binary sum

Because the endpoint shapes are not translates, there cannot be two raw labels at one key. Within one label distinct x_i give distinct keys. Thus valid raw keys have no duplicate representation; no existential enumeration or arbitrary choice is involved.

For each raw slot, compute isolation by the same inclusive count over [u−(3B+1),u+(3B+1)]. Compare against all 2n raw slots and reject precisely if a *different* raw key lies within the competing-key radius. These competitor tests use every raw key, including ones that fail isolation or context. Dropping failed competitors would be unsound.

For each contextual side count the occupied sites in [u−Z−J,u−Z] or [u+Z,u+Z+J]. More than one rejects the guard; zero gives class J+1; exactly one gives its exact offset. A stable first-hit scan with Boolean selects constructs that unique offset. The class is set to a valid dummy on a rejected multi-particle context before lookup. The chosen table value is computed by a finite multiplexer over the actual 2bc domain/image truth-table entries. Both class coordinates and the branch/domain-image identifier are compared fieldwise against each explicit table row. Do not form a flattened arithmetic class address c0*(J+2)+c1: that unnecessary J^2-valued wire would require a larger height bound. Both table dimensions and the branch/guard identifier are paid. No lookup scans the J+1 physical coordinates.

Active bits are computed entirely from this one pre-factor snapshot. Do not update one occurrence before deciding another.

To construct the simultaneous output without ambiguous particle labeling, sort each endpoint shape and pair its r-th old site with its r-th new site. For old particle x_j set

y_j=x_j+sum_(raw slot a,shape rank r) [active_a AND x_j=u_a+old_shape_(a,r)]*(new_shape_(a,r)−old_shape_(a,r)).

Each sum has at most 6n terms; use binary additions and lifted products. By the isolated-swap lemma the active endpoint unions are disjoint, so at most one displacement applies to each old particle. This yields exactly the factor's set output with no multiplicity, mass loss, or serial-rewrite error. Sort the n resulting coordinates with a fixed adjacent compare-exchange network of binom(n,2) comparators; ties keep the earlier record. Valid factor semantics ensure no equal output coordinates. The canonical sorted list is therefore unique.

Compare this output coordinatewise to the input to determine the changing bit. It is safe to use the nonempty-active-list equivalent, but the coordinatewise version avoids relying on that additional inference.

## 5. Least future change, full absence, and T+K scheduling

The state at round r consists of current sorted support X_r, CA-step counter t_r, and cursor c_r, the least unprocessed factor index. Initially t=0,c=0. Every round computes the full fixed candidate list and the effect of every slot from X_r. It then scans slots in their fixed order, retaining the least index i satisfying

enabled, i>=c, factor_i(X_r)!=X_r, t<T.

Initialize the best index to sentinel F and replace it only on strict improvement. This forces the earliest slot among duplicate minimum indices. There is no order/minimum oracle: each replacement is a comparator plus coordinatewise selection. Store the winning factor's already computed output.

If a winner exists, set X to that output and c=i+1, keeping t unchanged. Candidate generation is redone from this new snapshot next round. Previously passed indices are never revisited.

If t<T and no winner exists, every candidate future factor is the identity. Every noncandidate factor is also the identity by completeness. Thus the entire remaining ordered suffix is the identity on this unchanged snapshot. This is the explicit absence certificate completing exactly one CA step: set t:=t+1,c:=0, keeping X.

If t=T, keep X,t and the canonical idle cursor zero. Mask every eligible candidate false. All internal circuits are still fully determined. Require t_R=T after exactly R=T+K rounds.

Induction over the true ordered factor sequence proves that changing rounds execute precisely the next nonidentity factor of the current CA step; no identity step changes the snapshot on which a later factor is checked. Each completed CA step requires its own no-future-change round, **including the step containing the last allowed changing event**. An execution with k changes uses exactly k+T nonidle rounds and then forced idle padding. Hence completion by R is equivalent to k<=K. In particular K alone cannot pay for the final suffix check, and the +T term is indispensable.

The state and every dummy branch are functions of earlier wires. Induction through the arithmetic circuit proves that the entire pre-acceptance natural fiber has exactly one assignment for each admissible input. Final completion and target equations retain that assignment or remove it. This is the proof of complete witness uniqueness; single-coordinate mutation tests are corroboration only.

## 6. Fully charged size bounds

The exact ledger for any emitted circuit is the A,I,Dv,G,Q ledger in section 2. The following intentionally generous concrete upper bound specifies a finite implementation size before an arbitrary-mass emitter exists.

Put U=10000*(T+K)*(C+1)*(n+1)^2*S_tab for T>0. There is an implementation of the stated binary-fanin construction with

A+I+Dv+G <= U.

One way to audit the slack in this bound is the following per-round macro allocation, with the unit being one primitive of section 2:

- candidate generation, source-record/incidence selection, and all C index/descriptor decoders: at most 1000*(C+1)*(n+1)*S_tab
- all C factor evaluations (2n raw records, all-pairs raw competitors, two n-particle context scans, explicit 2bc table selection per raw record, 6n displacement terms per particle, and binom(n,2) sorting comparisons): at most 1000*(C+1)*(n+1)^2*S_tab
- stable minimum selection of C n-coordinate outputs, completion/idle flags, and state updates: at most 1000*(C+1)*(n+1)*S_tab

The total is at most 3000*(C+1)*(n+1)^2*S_tab, leaving slack for input wiring, finite descriptor cases and final wiring within the displayed 10000 bound. More concretely, a lookup row needs at most eight comparisons, a fixed AND tree, one mask, and one accumulator addition; a required-site test needs two comparisons and its Boolean fold; a two-ended interval test needs two comparisons, one AND and one addition; a compare-exchange needs one comparison and two signed selects. Each loop ranges only over a fixed set of size n,2n,3,Delta,m,p,b or 2bc. All large sums are those binary folds. No loop ranges over F or over coordinate extent. These generous constants are theorem-level upper bounds, not measured optimum counts or claims that each macro has exactly that many gates.

Consequently the conservative ledger is

V<=4U,
E<=3U+Q,
residual monomial slots<=10U+4Q,
ordered expanded-square term occurrences<=68U+16Q.

Canonical external signs, initial strict order and a prescribed endpoint can be checked using O(n) primitives/checks. At most Q<=3n+1 checks suffice: n sign checks, n−1 order checks, n target checks, and one completion check. The order comparisons and their materialized flags are included in U. If admissible sorted canonical inputs are the externally specified domain, those admissibility checks can be omitted. In the T=0 specialization they are accounted separately.

Preprocessing is separate. The current pinned validator explicitly visits b*c branch/class pairs, evaluates guard syntax, and constructs full truth tables and incidence metadata. Retaining its implementation gives the already disclosed guard-program work O(c*G_src+bc) scalar operations and coarse growing-mask cost O(bc^2) bit work, plus actual source parsing and integer-comparison costs. Large binary J is not cheaply normalized. Storage includes the actual source syntax and 2bc table bits/entries. No claim of polynomial preprocessing in log J is made.

For the pinned universal source, m=122622,b=141561,J=0, Delta=2, F=269291358255. At n=5 the formula gives C=170 and S_tab=1396672. This is **170 candidate slots, not 170 witnesses, constraints, or operations**. Generic per-use multiplexers still incur the full source/table costs. The crude U is consequently enormous; the theorem does not claim a practical universal quartic exporter. It does remove an obligatory block indexed by every local factor and every literal physical CA step factor position.

## 7. Coordinate, coefficient, and bit costs

No coordinate bound is required in the polynomial's syntax. It accepts arbitrarily large positive and negative input coordinates through their canonical pairs. Let H0=max_i |x_i|, with H0=0 for empty input.

On an accepting trace, actual changing-factor displacements are at most 2B3 per matched particle. True snapshots have magnitude at most H0+2KB3. Hypothetical candidate outputs evaluated from a snapshot need at most one further 2B3 displacement. Keys and context endpoints add at most O(B3+Z+J). All indices are explicitly bounded by F; time/cursor are bounded by T and F; sums of indicator bits are bounded by 2n. Bad modes/indices/travel parameters are totalized before their dependent arithmetic, as specified above.

A deliberately coarse height bound for this particular straight-line construction is

H_* = 100*(n+1)*(H0+2*(K+2)*B3+Z+J+F+T+K+1).

It covers comparison slacks, constant quotients/remainders, source codes, gate indices, class offsets, masked displacements, count accumulators, and canonical signed parts. Context extraction by the stable first-hit scan avoids a sum of many unbounded signed offsets. Source-record selection is one-hot by exact index tests; partial sums of selected nonnegative source fields cannot grow beyond their largest field. Other arithmetic is addition/subtraction, fixed source scaling for factor indices, or multiplication by a Boolean or sign. The trace-generation constants are at most a fixed multiple of F+Z+J+T+1; prescribed target constants occur only in acceptance checks and are charged separately in lambda. Thus each witness uses W=ceil(log2(H_*+1)) bits, and the total witness encoding needs at most V*W bits, in addition to the input encoding. The estimate concerns accepting fibers; a rejected budget can still be evaluated with an analogous bound using R instead of K.

Let lambda be the largest actual residual-coefficient bit length. With symbolic coordinate inputs, coefficients depend on the finite source and chosen target constants, not on H0. If initial coordinates are specialized as constants their bit lengths must instead be included in lambda. No packed F-bit truth table is admitted as one source constant.

The residual coefficient list has O(U+Q) terms by the displayed bounds. Straight-line witness generation uses O((U+Q)*W^2) elementary bit operations under schoolbook signed multiplication/division, with source constants' bit lengths included in W; add preprocessing separately. Direct residual/SOS verification is bounded by O((U+Q)*(W+lambda+log(U+Q+2))^2) bit work. These verification bounds use the declared input/witness height. For an arbitrary submitted tuple, replace W by its actual maximum input/witness bit length, or reject an oversized encoding after reading/checking its length. H_* is a bound on canonical accepting witnesses, not a promise about malicious submissions. This is deliberately loose and sufficient to avoid unit-cost giant arithmetic. It charges the entire natural witness, coefficient data, intermediate products, squares, and accumulation.

If L2 denotes the displayed ordered-square term bound and every residual coefficient has magnitude at most C0, every collected expanded coefficient has magnitude at most L2*C0^2. Its bit length is therefore at most 2lambda+ceil(log2(L2+1))+1. Fully expanded monomials and coefficient collection are paid separately; no equality between factored and expanded representation sizes is assumed.

## 8. Executable scope and small concrete polynomial

`example_emitter.py` implements the complete T+K scheduler for **all two-particle inputs** of one explicitly specified source: two controls q,halt, one right-counter increment with true guard and J=0. Its three natural inputs are (h^+,h^-,g), with h^+h^-=0 and coordinates x0=h^+−h^- and x1=x0+g+1. This parametrizes every sorted two-particle support, but differs from the general theorem's literal 2n-coordinate signed-pair interface; the sample auxiliary counts use this three-input specialization. Its constants are D=8,F=95. Triple factors cannot act at mass two. The only possible changing factors are free-E O/I and phase-free-P O/I, at indices 0,22,47,70. The code directly specializes these four factor actions; it does not purport to be the general descriptor/guard compiler.

For input {-10,-5}, T=1,K=2, endpoint {-9,-4}, it emits all residual coefficients, a natural witness, and the fully expanded quartic. The two changing rounds use factors 0 and47. The third is the separate absence/completion round. Current mechanically emitted counts are 612 witnesses,616 residuals,2013 residual monomials,9955 ordered-square term occurrences, and4573 collected expanded monomials. These numbers belong only to this small specialization and its endpoint checks.

`scheduler_reference.py` implements the general fixed candidate slots and total-event scheduler using pinned factor evaluation. It is a test oracle for the schema, not a polynomial exporter. `test_schema.py` compares its candidate sets and results with the pinned lazy/eager products; includes n=0/1, the known four-event malformed cascade, simultaneous separated copies, strict underbudget rejection, exact completion-round counts, canonical padding, and a multistep total budget; and compares the implemented mass-two polynomials with actual CA iteration, including 100-digit signed coordinates. It checks serialized/expanded equality at the sample and rejects every one-coordinate witness +1 mutation. The supported build interface validates h,gap,T,K as exact integers in their stated domains and an optional target as a list/tuple of exactly two strictly increasing exact integers. Boolean, floating-point and integer-subclass targets are rejected before coefficient construction. The binding checker validates integer coefficient/index types and degrees before comparing the residual list and expansion; dedicated tests include 2^60 floating aliases and 301-digit exact coordinates. These finite tests do not replace the general proof or establish universality at mass two.

## 9. Limits and useful next improvement

A bare list of changing factors is insufficient: it does not certify that an omitted earlier factor was an identity, or that all active occurrences of a selected factor were applied simultaneously. This construction pays for both obligations through full snapshot candidate evaluation.

It is event-budget-sensitive, not solely proportional to the number of active keys. It pays R=T+K complete candidate circuits, including candidates after the minimum and ghost circuits in padded rounds. The operational lazy evaluator can be much cheaper when it tests only a few candidates. The theorem does not inherit its favorable A_test count without additionally encoding the exact sequential search/padding transcript and paying its own data-dependent bound.

No unconditional numerical small-K bound follows from the compiler: arbitrary finite configurations may cascade. The factor count can still appear logarithmically in indices/coefficient heights and algebraically through source constants; it is not silently erased. The next engineering step would be a general coefficient emitter plus an independent binding checker for all macros. Until then, the arbitrary-mass statement is an explicit finite-schema theorem, not a shipped universal polynomial artifact.
