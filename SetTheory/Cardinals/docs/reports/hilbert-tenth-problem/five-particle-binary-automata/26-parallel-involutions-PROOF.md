# Two parallel involutions for the binary five-particle construction

## Result and scope

For every finite source accepted by the pinned Report 15 compiler, there is a **new** translation-equivariant binary cellular automaton

    F_new = P_parallel after E_parallel

whose two displayed blocks are involutions on the full binary shift. It conserves the ordinary number of ones on every finite configuration. Its restriction to the entire admissible doubled micrograph of Report 15 equals the old automaton, step for step. In particular, its valid source encoding, five-particle mass, forward/reverse microedge clock, reflection behavior, halt observer, and clean-target construction are unchanged.

With the old constants

    D = 2m + 4p,
    b = B3 = 4D + 5,
    Z = 10b + 10 + 2J,

an explicit sufficient radius bound is

    R_new = 180D + 258 + 9J.

This replaces a radius bound proportional to the sum over the ordered local factors by one proportional to local geometry. It is **not** a smaller-radius presentation of the same full-shift rule: the rules demonstrably differ on malformed configurations. Neither radius minimality nor a new universality theorem is claimed. No universal template array or truth table is emitted here.

The fixed old compiler is `frozen_reversible_binary.py`, SHA-256
`f95a6028c9d3cc6f8b0b497cfc0cad68104da6d70e55205df04ad234e5d0c76f`.
It is an exact copy; earlier outputs were not changed. Report 19's sparse evaluator remains an evaluator of the **old ordered rule** and does not evaluate this new rule.

## 1. General prospective-isolation lemma

Write I_a(u) = [u-a,u+a] intersect Z. Fix nonnegative integers b <= r and finitely many types g. For each type choose a type-specific write set W_g contained in I_b(0), and two distinct equal-Hamming-weight words on W_g. The translated local map tau_(g,u) exchanges these words on u+W_g and is the identity on other words and outside that write set. It is an everywhere-defined involution.

Let c_g(x,u) be a translation-covariant Boolean predicate depending only on x in I_r(u), implying that the word on u+W_g is one of the two endpoints. Require the natural endpoint symmetry

    c_g(x,u) = c_g(tau_(g,u) x,u).

The complete candidate-key set is

    C(x) = {(g,u): c_g(x,u)}.

A key retains its type and anchor when its endpoint orientation reverses. Different types at the same anchor are different keys. Define H = 2(b+r). A key k=(g,u) is selected precisely when:

1. It belongs to C(x)
2. No other key of C(x) has anchor within distance H of u
3. C(tau_k x) and C(x) have the same keys anchored within distance b+r of u

Condition 3 compares all candidate types, not only the selected type; it ignores endpoint orientation. It does not recursively inspect eligibility. Define A(x) by performing every selected rewrite simultaneously.

**Lemma.** A is a translation-equivariant, particle-conserving full-shift involution of radius at most 3(b+r).

**Proof.** Selected anchors have pairwise distance greater than H, hence their write sets are disjoint. A coordinate belongs to at most one selected write set even for an arbitrary infinite configuration.

A rewrite at u can change a candidate predicate at v only if |v-u| <= b+r. Thus condition 3 is equivalent to global equality C(tau_k x)=C(x). A candidate read window can meet at most one selected write set: meeting two would place their anchors at distance at most 2(b+r)=H. Its value after all selected rewrites therefore equals its original value or its value after exactly one rewrite; prospectivity gives equality in either case. Consequently C(Ax)=C(x). This is the step that excludes simultaneous cooperative births.

A key's prospective condition reads only I_(b+2r)(u). Every other selected rewrite is outside this window for an isolated candidate, since its anchor distance exceeds 2b+2r and its write radius is at most b. The candidate's own rewrite preserves its prospective condition, because tau_k is an involution and the two compared candidate sets are simply interchanged. Candidate-set invariance preserves isolation. Every isolated candidate, including an initially unselected one, consequently retains the same prospective status; nonisolated candidates remain nonisolated and noncandidates remain absent. The selected-key set is therefore invariant. A second application uses the same disjoint involutions and restores x.

Isolation reads radius H+r about its key; prospectivity reads radius b+2r. A coordinate can be written only by a key within b. Hence output radius is at most

    b + max(H+r,b+2r,r) = 3(b+r).

The finite type set makes this a finite Boolean rule. Each disjoint rewrite has equal input and output weight, proving ordinary finite-particle conservation. The definition is shift-covariant. This completes the all-input proof. See `audit-lemma.md` for the independently audited formulation and detailed proof.

The use of type-specific write sets is essential for the application: a two-particle free template has a smaller exactness window than the common bound b=B3, and unrelated particles inside I_b but outside its own write block must be retained.

## 2. New candidate family from the literal old templates

Keep every endpoint pair P_g,Q_g, invariant anchor, and contextual guard from the old compiler's E and P arrays. These arrays are used here as a finite list of template types, **not as an ordered list of executed CA factors**. For each old gate with support parameter B_g, let its own write interval be W_g=I_(B_g)(0), and let ell_g=3B_g+1. The new candidate predicate is:

- All particles in I_(ell_g)(u) are exactly u+P_g or exactly u+Q_g
- The old contextual class guard, if any, is true at u

We intentionally omit the old same-type raw-key exclusion. The new all-type isolation and prospective test replace the full-shift safety mechanism. Exactness in I_ell implies endpoint exactness on W_g. All contextual reads of home dispatch, commit, and direct templates are at u plus/minus (Z+k), for 0 <= k <= J. These sites are outside W_g and are untouched by the paired rewrite. Thus each predicate is endpoint-symmetric. The commit uses the exact old image guard; it is never replaced by a forward guard.

All write intervals have radius B_g <= b. For E choose

    r_E = Z+J,

which dominates 3b+1 and every pair/triple exactness radius. For P there are no class guards, so choose

    r_P = 3b+1.

Apply the lemma independently to each family, using H_E=2(b+r_E) and H_P=2(b+r_P). This produces E_parallel and P_parallel. The same construction covers sources with no nonzero branch or an empty E family. Empty candidate families yield identity blocks; the uniform resource bound is still valid.

## 3. Why all valid states pass the stronger filter

The valid set is exactly the old admissible doubled micrograph: every home ID over natural counters, together with the strict intermediate nodes of enabled source-edge subdivisions, each in plus and minus form, and all their translations. It does not include arbitrary geometrically plausible but guard-invalid O/I packets.

Every admissible state has one unique close pair with gap at most D. The other three particles are markers, with mutual separations at least Z, and all head-marker gaps exceed D. Every endpoint template contains exactly one close pair. A candidate of any type therefore has to use the actual head pair. Globally distinct signed gaps determine its mode and sign. A triple match also determines the nearby marker; marker spacing prevents two markers from being relevant to any one template. In particular, isolated background markers produce no candidates.

For a home state the only E candidates are outgoing dispatch/direct templates in the plus orientation, or incoming commit/direct templates in the minus orientation. Their domain predicates, respectively exact image predicates, are pairwise disjoint. Therefore there is at most one candidate. A missing outgoing or incoming microedge gives no candidate. Any present candidate's reverse endpoint has the same source-edge template and the same invariant key.

For a moving mode, the unique branch label and sign reduce candidate identification to the travel corridor and its boundary interactions. The pair template is exact in the radius-L window centered at the **predecessor** head anchor, where L=3D+4. Triple templates cover its exact complement near a marker. In particular:

- A behind departure from distance L to L+1 uses a triple; its minus endpoint is not a free inverse, because the free predecessor key still sees the marker at distance L
- An ahead arrival from distance L+1 to L uses a free template; there is no ahead triple whose predecessor distance is L+1
- Dispatch/reversal and arrival/commit at distance S use their specifically signed interaction endpoints; no travel from behind S−1 is introduced
- The reverse endpoint interaction retains the old endpoint-marker key, even though the actual marker moves by side times delta

More explicitly, orient a corridor from its departure marker toward its destination and let N be their distance. Let t be the oriented head-anchor distance from the departure marker. Then S <= t <= N−S, and N is at least Z. The plus travel candidates partition the range as

    behind: S <= t <= L
    free: L+1 <= t <= N−L−1
    ahead: N−L <= t <= N−S−1
    forward interaction: t=N−S.

The minus candidates partition it as

    reverse interaction: t=S
    behind inverse: S+1 <= t <= L+1
    free inverse: L+2 <= t <= N−L
    ahead inverse: N−L+1 <= t <= N−S.

The inequalities include all equality cases. The relevant domain/image interaction guard is true on an admissible intermediate because it belongs to an enabled edge and retains that edge's old/post counters. It follows that every admissible intermediate has exactly its intended E candidate. Swapping it stays admissible and leaves exactly the same type-anchor key at the paired orientation.

The P family is simpler: at a home there is the unique home-phase triple; at a moving anchor there is the free phase pair if every marker is farther than L, and otherwise its unique near-marker phase triple. Both orientations use the same anchor and case. Thus every admissible state has exactly one P candidate and its swap leaves exactly the same key.

Consequently each valid block input has either no E candidate or a single E candidate with unchanged before/after key set; P always has a single such key. All-type isolation and prospectivity therefore pass automatically, regardless of how large H is. The new blocks equal the old E matching and P sign flip on this entire admissible set. This is not an assumption about malformed states. The independent symbolic boundary and guard audit is `audit-preservation.md`.

## 4. Simulation, inverse, and conservation consequences

The composition F_new=P_parallel E_parallel is a full-shift bijection with inverse E_parallel P_parallel. It is finite-radius, time-independent, binary, translation-equivariant, and ordinary number-conserving. No parity background, external phase schedule, clock particle, or extra alphabet symbol is introduced; the two submaps are mathematically composed into one CA time step.

On every admissible plus node with successor it advances one old microedge and retains plus. On a minus node with predecessor it moves one old microedge backward and retains minus. At a missing edge it reverses sign in one step. Hence every valid trajectory equals the old trajectory, including both reflections. The nonzero branch clock remains

    tau_e(c)=3+2(Z+c)+Delta−4S,

and a zero-update source edge still takes one step. With a predecessor-free start, a finite forward path of T microedges yields a cycle of exactly 2T+2 states. The anchored observer length remains 3D+3. The old clean-target source wrapper still reaches its input-dependent whole-configuration target first at 2Theta+2 and has reflected period 4Theta+6. The prior caveat about nonhalting stuck source IDs and periodicity remains unchanged.

The local proof applies to every bi-infinite configuration; finite tests are supplementary evidence. Finite-particle number is conserved by disjoint equal-weight replacements in each block. For arbitrary infinite inputs we do not equate divergent total sums; the construction still gives well-defined bounded local particle transport.

For an n-periodic input, translation covariance makes the selected-key set n-periodic. Summing the equal input/output weights of its disjoint selected write blocks over one translation period preserves the number of ones per period, including blocks crossing the chosen period boundary. The full-shift involution proof applies without change. Small periods that force a translated competing key within H simply select no such move; no separate periodic exception is needed.

## 5. Explicit radius and resources

The lemma gives

    R_E = 3(b+Z+J) = 33b+30+9J,
    R_P = 3(b+3b+1) = 12b+3,
    R_new <= R_E+R_P = 45b+33+9J = 180D+258+9J.

There are still 8pD+29p+m+a endpoint template types across the two families. Increasing the number of templates can increase Boolean evaluation work and truth-table complexity but does not sum their coordinate radii. Exactly two full-shift involutions are composed. The reference interpreter materializes small-source template arrays for transparency. No universal efficient evaluator or complexity reduction independent of the template count is claimed here.

Examples, all using the old encoding constants:

- Two-control right increment, J=0, D=8: old radius bound 21,144; new bound 1,698
- The old clean-target sample, J=1, D=18: old bound 164,314; new bound 3,507
- Substitution of the frozen Report 19 universal ledger D=509,508,J=0 gives 91,711,698, versus its old 3,292,955,588,459,274,804 bound

The last line is a symbolic ledger substitution in a proved source-uniform theorem. This packet does not run or materialize that universal new rule, and it does not independently re-prove the attributed universal source theorem.

### Certificate transport boundary

Exact trajectory equality transfers semantic accepted-computation claims whose endpoints and all witnessed steps belong to the admissible source simulation. Thus an old admissible encoded computation reaches the same old observer or exact target at the same time under the new rule. This is a semantic transport statement, not automatic reuse of an arbitrary old arithmetic verifier.

Report 19's evaluator computes the ordered old rule on arbitrary finite supports. Its execution traces are not traces of the new rule on malformed inputs. Likewise, Report 20's ordered-factor/event-budget certificates and its old full-malformed-state circuit counts do not automatically evaluate or certify the new rule. Any certificate intended to describe all new-rule configurations needs a new rule-specific verifier encoding the complete candidate family, exclusion tests, and hypothetical before/after stability tests. Old circuit counts remain counts for the old circuits. Two new mathematical CA blocks do not imply two cheap arithmetic factors, a small Diophantine encoding, or a source-sized efficient evaluator. No such new certificate or resource count is emitted here.

## 6. Malformed-input distinction and necessity of prospectivity

The frozen malformed cascade is

    X={−118,−112,0,18,23}

for controls q,h, a true-guard right increment, and J=0. For each new block X initially has one candidate. Its single hypothetical swap would create another candidate key, so the prospective test rejects it. Both new blocks fix X. The old rule instead maps it to

    {−119,−113,0,19,24},

and its old E and old P blocks are not involutions on X. The checker explicitly confirms both facts. This is affirmative evidence that the new construction did not silently treat the old block products as full-shift matchings.

Dropping prospectivity also fails in a tiny independent example. On period 12 with the sole type P={−1,0}, Q={−1,1}, exactness radius 1 and H=4, the input ones {0,1,2} are moved by the isolation-only rule to {0,1,3}; its next application leaves {0,1,3} unchanged. The first move creates a conflicting candidate. `test_periodic_lemma.py` discovers and records this counterexample during exhaustive enumeration. The actual prospective rule remains involutive.

## 7. Bounded executable evidence

`parallel_particles.py` implements the definition on finite supports, including a separate literal coordinate-local output routine using only its declared radius. Its before/after comparisons keep all candidate types and discard only orientation labels. Verification checks candidate-set invariance, selected-set invariance, reversed selected orientations, mass, and block involutivity using explicit exceptions, so they remain active under Python optimization.

The supported source-facing API is `ParallelCompiler(source)`. It uses the frozen validated JSON schema, retains immutable source/template snapshots, and accepts only a set/frozenset of exact Python integers for particle supports. Boolean and floating-point coordinates are rejected; inverse and verification flags must be exact Booleans. The compiled wrapper, blocks, and patterns are frozen records. The generic block/pattern machinery is an internal lemma/test harness: a custom guard's bounded read radius, purity, and endpoint symmetry are mathematical contracts, not constructor-enforced facts. Public source compilation accepts no user-supplied executable guard. `test_public_api.py` checks these distinctions and mutation/alias behavior in both interpreter modes.

`test_parallel.py` uses an independently generated source micro-path and checks:

- 8,928 valid doubled states across 12 sources/input cases, including 8,450 states in complete reflected cycles
- Left/right increment and decrement, stuck homes, zero-update edges, disjoint guarded mergers, free/contact equality cases, exact source clocks, and the complete 5,670-state clean-target cycle
- 89 comparisons against the frozen old eager CA on valid states
- All 4,096 subsets of two specified 11-site malformed universes, with block verification and whole-map inverse checks
- 100 seeded noisy/multihead configurations, 100 translations, and 2,074 declared-local-radius comparisons
- A finite configuration with two simultaneously selected E moves and two simultaneously selected P moves
- The old cascade, its new rejection, and the differing old/new whole maps

`test_periodic_lemma.py` independently enumerates 24,576 periodic binary words over three small template families, with 24,576 coordinate-local oracle comparisons, candidate/selection invariance, mass, involution, and isolation-only mutation counterexamples. The nontrivial families include 520 periodic words with multiple simultaneous selected moves, a contextual guard, and dense malformed backgrounds. The two-type family is deliberately conflicting and its identity behavior is disclosed in the receipt.

Both suites are run normally and under `python -O`. Tests do not exhaust the source-uniform radius neighborhood or replace the mathematical full-shift proof. The proof is not formalized in a proof assistant. No novelty, optimality, universal runtime, or public release claim is made.
