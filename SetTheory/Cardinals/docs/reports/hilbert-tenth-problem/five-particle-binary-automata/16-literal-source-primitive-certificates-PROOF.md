# Direct primitive shared-offset finite-horizon quartic certificates

3 October 2026. This is an additive refinement of the fixed-horizon certificate construction. It changes neither the frozen literal source nor the earlier general finite-cell proof.

## 1. Exact scope and primitive source interface

Fix a finite deterministic partial two-counter machine. Controls have distinct integer codes 0,...,m−1. Its designated halt control has no outgoing row; other stuck controls are not halts. Natural numbers include zero. Each original row α has source sα, target rα, selected update counter jα∈{0,1}, and one of exactly these five forms:

- I: unguarded increment c′=c+e_j
- D: decrement c′=c−e_j, enabled exactly when c_j>0
- A: unguarded identity c′=c
- Z: identity enabled exactly when c_k=0
- P: identity enabled exactly when c_k>0

For Z and P the tested counter k need not equal the syntactic selected side j, since the update is zero. The implementation tracks the tested counter separately. This prevents a guard-on-the-untouched-counter error. No arbitrary positive-guard increment, Boolean guard AST, threshold other than zero, or callable guard is accepted by this specialized compiler. The earlier finite-cell construction covers the broader finite-Boolean-guard interface; these are different domains of applicability.

Let B be the number of original rows, M the moving-row count (I and D), N_Z the Z-row count and N_P the P-row count. Let P_k be the set of original P rows testing counter k. Determinism means original domains at each source control are disjoint. Reversibility is not needed for the certificate theorem. The supplied universal source is separately verified reversible on every natural ID.

The exact validator stores original rows and source-control adjacency lists. Four-bit zero/positive masks suffice to check domain and image intersections. An I image has selected postcounter positive; a D image allows every natural postcounter; Z/P images retain their zero/positive condition; A is unrestricted. This is a proof over all natural pairs because these are the only boundaries. It stores no normalized branch/cell copies and does not refine the source horizon. An optional `require_reversible=True` rejects intersecting exact image masks. No-incoming-start is reported separately, not assumed by the core certificate theorem.

## 2. Explicit indexed polynomial family

Fix a natural source-instruction horizon K. This is compiler syntax, not a polynomial input. Initial control q0 and counters c0,0,c0,1 are externally specified; initial counters are natural. The implementation specializes these inputs to exact integer constants.

For K≥1 and each t=0,...,K−1 introduce natural witness variables:

- e_t,α for all B original rows
- z_t+1,0 and z_t+1,1, the shifted postcounter coordinates
- b_t,0 and b_t,1, shared offset coordinates

Define actual counter expressions C_0,k=c0,k and, for t≥1,

    C_t,k = z_t,k + b_t−1,k.

The residuals are ordinary integer polynomials:

    A_t = Σα e_t,α − 1
    Q_0 = Σα sα e_0,α − q0
    Q_t = Σα sα e_t,α − Σα rα e_t−1,α,  t>0
    U_t,k = z_t+1,k + b_t,k − C_t,k − Σα δα,k e_t,α,  k=0,1
    B_t,k = b_t,k − Σα∈P_k e_t,α,  k=0,1
    G_t,α = e_t,α z_t+1,kα,  for each Z row α
    F = Σα rα e_K−1,α − h.

State symbols in residuals denote their injective fixed integer codes. Define the polynomial as the sum of the squares of every displayed residual, retaining a slot even if a specialized residual vanishes identically. Every residual has degree at most two; the sum has degree at most four. A displayed SOS is a specification of an ordinary finite integer polynomial, not an added predicate or an implicit arithmetic operation.

Crucially, the zero guard tests the shifted **postcounter**. Testing an unshifted postcounter would also be semantically possible but would add terms. The chosen one-monomial residual is sufficient because a selected Z row is an identity and cannot simultaneously select a P row.

## 3. Complete natural fiber theorem

The full natural witness fiber is empty or consists of exactly one tuple. It is a singleton exactly when the source first reaches halt after K original instructions.

Proof. If the SOS vanishes, every residual vanishes, since squares are nonnegative. Natural selectors summing to one are one-hot. State rows therefore select a row at the current control. Each B_t,k forces its offset to one exactly when the selected row is P testing k, and zero otherwise. In particular the offsets are forced to be 0/1 without additional Boolean equations.

The U rows impose the row's exact update on actual counters C. Actual counters are nonnegative because they are sums of natural z and b coordinates. Inductively the source inputs and updates make them natural. Check each primitive guard:

- Selected I or A has no guard
- Selected D is not P, so both current offsets are zero. Its selected update gives old c_j−1=z_t+1,j≥0; hence old c_j>0
- Selected P testing k has zero update and b_t,k=1. Therefore old c_k=post c_k=z_t+1,k+1≥1
- Selected Z testing k has zero update and both current offsets zero. Its guard residual is z_t+1,k=0, so old c_k=post c_k=0

This produces a legal K-step trace ending at halt. If it reached halt at an earlier layer, the next state row would require a nonexistent outgoing halt row, impossible. Thus it is a first halt at exactly K, not a padded accepting history.

Conversely, a legal first-halt trace supplies the unique selected original row at each step, actual postcounters, offsets b=1 precisely for a selected P test of that counter, and z=actualpost−b. For a selected P, guard positivity guarantees this subtraction is nonnegative; all other offsets are zero. All residuals then vanish. Determinism fixes the trace and selectors; the offset equations fix every active and inactive wire; the update equations fix every z coordinate. Hence there is no slack or unused auxiliary coordinate left free, and the complete tuple is unique. Reversibility never enters this proof.

For K=0 use the single residual q0−h and no core witnesses. Its square has the empty tuple as its unique solution exactly when q0=h, independently of the natural input counter values. With B=0 and K>0 the one-hot residual is −1, correctly preventing a solution. A non-halt stuck control likewise produces no accepting witness.

## 4. Paid nonnegative-real orthant theorem

To replace the witness domain by the whole nonnegative-real orthant, retain natural external initial counters and add one squared selector-norm residual per layer:

    N_t = Σα e_t,α² − 1.

Together with Σe=1 and e≥0 this implies Σα<β eαeβ=0. Every summand is nonnegative, so precisely one selector is one and all others are zero. The offset equations force the same integral 0/1 wires. Counter updates from natural external inputs force integral actual postcounters and integral z. The complete real-orthant zero fiber is therefore exactly the same empty-or-singleton natural tuple. No variables are added; exactly K squares and K(B+1) written residual-term slots are added, still degree at most four.

This is not an unrestricted-real theorem. It also does not assert natural-machine semantics for arbitrary real initial counters. Without these paid norm rows the natural-only SOS can have fractional selector zeros. The tests exhibit a fractional average of two incompatible source controls that satisfies every core row but violates the norm row. The numerical evaluator accepts exact nonnegative integers/Fractions for the paid variant, never floats or booleans; the mathematical theorem covers all nonnegative reals.

## 5. Exact clock and its conditional CA interpretation

Use the original source counts and supplied cutoff J, never a cell-expanded or certificate-variable count:

    D = 2m+4M,    S = 2D+2,    Z_geom = 40D+60+2J.

The separately proved binary compiler uses duration one for every zero-update source row. A moving row with update δ at old selected counter c has duration

    τ(c,δ) = 3 + 2(Z_geom+c) + δ − 4S = κδ+2c,
    κδ = 72D+115+4J+δ.

Add one natural witness Θ and one residual

    T = Θ − Σt,α e_t,α τα(C_t,jα),

where zero-update τα is one. As each C_t,k is a constant or a sum of two degree-one witnesses, T has degree at most two. Θ is uniquely forced, preserving the complete natural and paid-real fiber theorems. A specified natural clock value can instead be supplied externally, costing just the square and no additional witness. For K=0 the retained clock row is Θ, forcing it to zero.

Subject to the separate compiler simulation/observation theorem, Θ is the first anchored plus-halt-word time after K literal source instructions. One full compiled F step, including both gate blocks, is one clock unit. Halt reflection occurs on the following CA step. K is not Θ, and neither generally equals the simulated Turing-machine step count. This implementation checks source arithmetic and clock formulas; it does not rerun or replace the all-configuration CA theorem.

## 6. Resource and expansion ledger

For K≥1 the shared-offset core has exactly

    witness variables:       K(B+4)
    squared residual slots:  K(6+N_Z)+1
    degree:                  at most four.

Exact clock adds one variable and one square. Paid real norms add K squares and no variables. These counts include natural postcounter coordinates and both offset wires. State coordinates are eliminated via the selectors; external inputs are excluded.

### Written residual term slots

Count terms in the written uncollected expression, treating each external initial counter as one atomic term. The implementation specializes the initial constants but retains each raw slot, including zero coefficients, until collection. Arbitrary polynomial input substitutions must be charged separately. The per-type counts are:

- One-hot: K(B+1)
- State: B+1+(K−1)2B
- Counters together: M+6+(K−1)(M+8)
- Offset rows: K(N_P+2)
- Zero guards: KN_Z
- Terminal: B+1

Their exact syntactic sum is

    K(3B+M+N_P+N_Z+11).

The first-layer counter saving of two slots cancels the combined state/terminal boundary constant of two. The same count is still exact for the implementation's written-term generator, because it retains zero coefficient slots before collection. A safe looser bound is this quantity plus two.

The clock adds exactly

    1 + K(B+2M) − M

written slots for K≥1. The first layer has one old input term rather than z+b. A safe looser bound is 1+K(B+2M). Norm rows add K(B+1). For K=0 the core has one written constant slot, even when zero, plus an optional one-term clock row.

### Fully collected row lengths and square costs

The implementation's closed-form ledger is for specialized constant natural inputs. Let n_s count rows whose source state code is nonzero, n_r count rows whose target code is nonzero, M_k count moving rows on k, and p_k=|P_k|. Collected residual lengths for K≥1 are:

- One-hot, and norm if present: B+1 each
- First state: n_s + 1[q0 code≠0]
- Later state: n_s+n_r
- First counter k: M_k+2+1[c0,k≠0]
- Later counter k: M_k+4
- Offset k: p_k+1
- Every Z row: one monomial, even at the first layer
- Terminal: n_r+1[h code≠0]
- Clock, if present: 1+KB+2(K−1)M

The specialized first-layer clock collects κe and 2c0e into one positive selector coefficient. Its collected length therefore differs from its written-slot count. The ledger computes the exact sum of lengths ΣL_i and exact ordered square-product occurrence count ΣL_i² from these categories, in O(B) source work independent of K. The latter charges every ordered product used when expanding the SOS. It is not the number of distinct monomials after all cross-residual merging; the fully expanded support can be smaller through coincidences and cancellation. No claim makes squaring or expression expansion free.

### Coefficients and witness heights

Let C0=max(c0,0,c0,1) and κmax=max(1, all moving κδ). For a valid K-step zero:

    selectors and offsets are at most 1
    actual counters and stored z are at most C0+K
    Θ ≤ K(κmax+2C0)+K(K−1).

The last inequality uses old selected counter at time t at most C0+t. A uniform coordinate bound is max(1,C0+K, the clock bound if included), whose ordinary unsigned binary length is its integer bit_length. Effective universal input encodings may have enormous C0; this cost is not omitted.

A safe specialized residual coefficient bound is max(1,m−1,C0) without clock and max(1,m−1,C0,κmax+2C0) with it. A safe expanded coefficient bound is (ΣL_i²) times the square of that residual bound. This deliberately conservative bound charges coefficient accumulation. With the separately validated corridor simulation, spatial diameter up to halt is at most 2Z_geom+c0,0+c0,1+K.

## 7. Literal universal-source specialization

The pinned source is `source.json` with SHA-256

    38c586706fa1069442d3e5103151adb156448b7d7c783f5c46d9d507b87fe73a.

Independent direct counting gives

    m=122622, B=141561, M=66066, N_Z=23429, N_P=52036,
    unguarded identity rows=30, J=0.

The moving rows split as 33436 increments and 32630 decrements. Per counter:

    Z counts=(14451,8978)
    P counts=(43058,8978)
    moving counts=(51320,14746).

All original domains and exact images are disjoint; START has no incoming row and HALT no outgoing row. The geometry is

    D=509508, S=1019018, Z_geom=20380380,
    κ_increment=36684692, κ_decrement=36684690.

Thus the core has

    141565K natural witness variables
    23435K+1 squared residual slots
    566225K written residual term slots
    polynomial degree at most four.

The clock adds one variable, one square, and 273693K−66065 written slots; paid real norms add K squares and 141562K written slots. These formulas hold for K≥1, with the separate K=0 convention above.

For comparison, the unchanged general cell construction uses 761347K core variables and 700112K+1 squares on this same source. A direct primitive construction using a distinct natural positive-test slack per P row gives 193599K variables and 75469K+1 squares. Explicitly, retain ordinary natural postcounters and add s_t,α−e_t,α(C_t,k−1) for each P row, with natural s_t,α. This forces every inactive slack to zero and selected old-counter positivity, yielding K(B+N_P+2) variables and K(4+N_Z+N_P)+1 squares. The shared offsets save 52034K variables and the same number of squares relative to that slack construction. These are proved constructions, not lower-bound or optimality claims.

One can eliminate both offsets by substituting their selector sums. With the postshift Z guards, that gives 141563K variables and 23433K+1 squares, but its core written slots rise to 618255K−52034. Its clock written slots become

    2342333775K−2342126147,

because each later moving duration multiplies its selector by all previous P selectors of the tested counter. Here Σ_k M_k p_k=2342126148. The shared-offset form avoids this expansion at a cost of only two wires and two squares per layer. The earlier pre-postshift idea also caused a Z×P term explosion; that obsolete bound does not apply to the final postshift-Z formula.

### What is and is not materialized

The release supplies a strict immutable snapshot of the literal source through the indexed reader, demand-emittable integer residual terms, a closed-form numerical universal ledger, and an independently audited small fully materialized ordinary polynomial. The provided universal K=1 clock-plus-paid-real ledger is specialized to the clean empty-tape input START(1,0), which does not halt after one source instruction; its nonacceptance is checked by the unique first transition without allocating a full witness. It does **not** contain a giant materialized universal-horizon-one polynomial or an expanded universal SOS. Even horizon one entails tens of billions of ordered square products before collection. Calling the universal certificate a finite indexed polynomial family is accurate; calling the included universal ledger a fully emitted ordinary polynomial artifact would be inaccurate.

## 8. Executable contract and small complete artifact

Python 3.10 or newer is required (`dataclass(..., slots=True)`). The implementation uses only the standard library. Exact integer and Boolean domains are checked with `type`, so bool is not accepted as an integer and floats/Fractions are not accepted as natural inputs. Guards are parsed only into the five primitive forms. Input dictionaries and lists are copied into frozen tuples/records and read-only maps. Branch, Machine and Certificate explicitly reject reinitialization, as well as ordinary assignment/deletion. Public branch guard evaluation checks exactly two natural counters. Validation uses explicit exceptions, not optimization-removable assertions.

A `Certificate` object stores its immutable source, horizon, initial ID and two flags. Variable and residual indices are calculated arithmetically. Construction allocates no K-sized arrays. The ledger enumerates source rows and constant-many length categories, never the residual family. `iter_raw_terms(i)` emits a selected row lazily. `row`, `materialize`, `expanded`, `witness` and `export` enforce explicit finite limits. The global `materialize`, `expanded`, `witness` and `export` defaults reject even the literal universal K=1 certificate before a global allocation. Individual small `row` requests intentionally remain available. The expansion guard uses ΣL_i², not merely a desired final support size.

The small reversible sample has five rows, respectively Z,I,P,D,A, six controls, and input (0,0). It first halts after five instructions. Its complete clock+paid-real SOS has 46 variables and 42 squares. `example-materialized.json` includes every residual and all 1100 distinct collected expanded monomials; `example-witness.json` includes every coordinate. Its degree is four, its clock is 3115, and exact evaluation is zero.

Tests cover all primitive forms, tested-counter/side mismatch, complete small natural and rational-grid fibers, inactive offset forcing, exact-first-halt rejection, K=0, empty branch tables, non-halt stuck controls, rejected input/witness types, callable/extra/Boolean guard rejection, determinism and optional injection checks, immutable snapshots, reinitialization guards, exact collected ledgers, explicit expansion, fractional spurious core zeros removed by norm, and huge symbolic-horizon allocation guards. They run in ordinary Python and under `python -O`. Finite tests support the implementation; they are not substitutes for the all-K/all-real proof.

## 9. Periodicity corollaries and the real-domain limit

This section additionally assumes the separately audited clean-loader source family and compiler periodicity theorem. For a halting clean-loader input, START is predecessor-free and the compiled CA's least period is Π=2Θ+2. The source horizon remains K and the exact Θ witness is retained.

For a specified positive natural time T, append one natural witness u and the square of

    T − (u+1)(2Θ+2).

This costs one variable and one square, with a quadratic residual and quartic SOS. It certifies that T is a positive multiple of the least period, so a positive return time. Its unique possible extension is u=T/Π−1. On a natural accepting fiber it exists exactly when Π divides T. Expanding this residual has at most five written monomial slots, or four after collecting its constants when the specified T is specialized to an integer; symbolic T retains five. On a positive-return zero, 0≤u=T/Π−1≤T/2−1<T, so the appended coordinate is not bounded solely by the earlier core witness-height bound. A uniform bound for the augmented tuple is max(the core-with-clock coordinate bound,T), with the corresponding integer bit_length. At K=0 the same syntactic formula is valid whenever the periodicity premise itself applies; clean-loader claims should not be extended to arbitrary halt-start IDs without checking that premise.

This multiplier corollary is **natural-witness only**, or explicitly mixed-domain with u∈N and other coordinates in the paid real orthant. Letting u be an arbitrary nonnegative real would falsely accept T=Π+1 via u=1/Π. The paid norm proof does not make u integral. To certify only the specified least period, use the residual T−2Θ−2, costing one square, no extra variable, and preserving the paid real-orthant fiber theorem.

The obstruction to purely-real witnesses for all return multiples is structural, not a missing elementary gadget. Fix a halting input and K, so Π≥2 is fixed. The projection of any finite polynomial equation/inequality system with finitely many real witnesses is semialgebraic in real T by Tarski–Seidenberg. A one-dimensional semialgebraic set is a finite union of intervals and points; equivalently its defining finitely many univariate polynomial signs stabilize beyond their finitely many roots. Membership on sufficiently large natural T must therefore be constant. Positive multiples of Π have nonconstant membership arbitrarily far out. Thus no such fixed-arity purely-real semialgebraic system represents precisely all natural return multiples, even without uniqueness. This is the standard quantifier-elimination corollary, not a novelty claim; see Saugata Basu, *Algorithms in Real Algebraic Geometry: A Survey*, Theorem 2.1 (PDF p.5), https://www.math.purdue.edu/~sbasu/raag_survey2011_final-sep4-2014.pdf . Least-period-only and fixed finite bounded-time formulations are unaffected.

The optional return/least-period rows in this section are explicit theorem-level corollaries. They are not advertised as implemented CLI options in `certificate.py`.
