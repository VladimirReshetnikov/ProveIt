# Independent audit: cellular-clock first-encounter domination

3 October 2026

## Verdict

**PASS, within the fixed static-orientation/template/compiler class.** The proposed exact cellular-automaton clock formulas are correct for the actual literal row graphs. Their monotonicity, together with the existing operation-level recorder embedding, proves first-encounter prefix-optimality for CA arrival time. Compiler size and the common clock coefficient are invariant under every static orientation, including orientations that change the six startup pairs. This invariance is proved below; the executable single-flip checks are corroboration, not a substitute for the proof.

The statement compares corresponding normalized-boundary arrival times in separately compiled machines. It does not compare configurations at equal CA times, host-language running time, or individual gate-evaluation counts. No enormous gate array, local truth table, or CA orbit was allocated or executed in this audit.

The independently reproduced empty-input startup is 138 literal two-counter rows and **1,394,018,396 theorem-derived CA steps**. The latter number is an exact clock calculation from those rows, not an executed CA trajectory.

## 1. Frozen inputs and independence

The primary source is `reversible-initialization-optimization-20261003`; its predecessor is `literal-reversible-source-20261003`. Both remain read-only. The optimized `source.json` SHA-256 is:

    fa61d06178d718511232a80a05e02192d940fde3c273f0c202f0623253b2ade3

This audit read the normalized, five-counter, two-counter, and serialized source tables; their certificates; the frozen compiler code/proof; and the existing first-encounter proof. The new executable imports none of the producer's builders or checkers and does not import the compiler. It reconstructs the complete five-counter and two-counter edge multisets independently, using certificate private names only. Certificate sources, targets, primes, kinds, and coverage are checked against the preceding actual row layer.

The receipt records SHA-256 before and after for eighteen named input files, nine in each frozen directory, including both source tables and both manifests. Those eighteen files are byte-unchanged. No audit action writes inside either frozen directory.

Reproduction from this directory:

    PYTHONDONTWRITEBYTECODE=1 python check_ca_clock.py --receipt receipt.json
    PYTHONDONTWRITEBYTECODE=1 python -O check_ca_clock.py --receipt receipt-optimized.json

All verification conditions are explicit exceptions and remain active under `-O`. The code writes only its requested receipt. Reports and logs are separate audit artifacts.

## 2. Exact clock of a literal two-counter row

The frozen compiler subdivides an enabled nonzero update of a selected physical counter from `c` to `c+delta`, where `delta` is `+1` or `-1`, into:

    dispatch: 1
    outward travel: Z+c-2S
    endpoint move: 1
    return travel: Z+c+delta-2S
    commit: 1

Consequently its exact CA duration is

    tau(c,delta) = 3+2Z-4S+2c+delta
                 = lambda + abs((c+delta)^2-c^2).

For an increment, `c>=0`, and the absolute difference is `2c+1`. For an enabled decrement, `c>=1`, and the absolute difference is `2c-1`. This equality is not claimed for disabled negative-counter updates. Every zero-update row has duration one.

For the frozen compiler constants,

    D=2m+4p,
    S=2D+2,
    Z=40D+60+2J,
    lambda=72D+115+4J > 0.

Here the compiler's `p` counts moving branches; it is unrelated to a prime parameter below. Its actual values are:

    m=122622, p=66066, a=75495, J=0,
    D=509508, S=1019018, Z=20380380,
    lambda=36684691.

One application of the composite CA rule advances one such subdivision edge on an admissible forward run. The many factors defining that rule are not additional units in this CA clock.

## 3. Derivation from the actual prime macro paths

Let the input physical counters be `(N,0)`, with `N>=1`, and let `p` now denote the fixed prime encoding the selected five-counter register. Every whole enabled prime macro ends at a five-counter boundary with physical work counter zero. The following derivation counts each moving row once and sums its square variation; it does not replace that variation by the square difference of the whole macro, which would incorrectly cancel down-and-up motion.

### Increment

The first phase moves physical `A` from `N` down to zero and `B` from zero up to `N`. Its square variation is `2N^2`, with `2N` moving rows. The second phase moves `B` from `N` down to zero and `A` from zero up to `pN`. Its square variation is `(p^2+1)N^2`, with `(p+1)N` moving rows. There are `4N+3` zero-update rows. Hence

    C_+(p,N)=(p^2+3)N^2+lambda(p+3)N+4N+3.

### Enabled decrement

Write `N=pQ`, with `Q>=1`. The first transfer contributes square variation `2N^2` and `2N` moving rows. The second phase decreases `B` from `N` to zero while increasing `A` from zero to `Q`: variation `N^2+Q^2` and `N+Q` moving rows. There are `2N+2Q+3` zero-update rows. Thus

    C_-(p,N)=3N^2+Q^2+lambda(3N+Q)+2N+2Q+3.

When `p` does not divide `N`, the would-be decrement blocks inside the macro; this formula is not a successful-boundary clock for that input.

### Enabled zero or positive test

Write `N=pQ+r`, `0<=r<p`. Quotient/remainder division decreases `A` from `N` to zero and increases `B` from zero to `Q`. The shared destination restorer subsequently increases `A` from zero to `N` and decreases `B` from `Q` to zero. Their total square variation is `2(N^2+Q^2)`, and there are `2(N+Q)` moving rows. The actual zero-update rows number `2(N+Q)+3`, including the division/restore exit tests. Therefore

    C_test(p,N)=2(N^2+Q^2)+2(lambda+1)(N+Q)+3.

Remainder zero selects a positive test; a nonzero remainder selects a zero test. A singleton test with the wrong outcome has no successful exit and blocks internally. The formula applies only to an enabled outcome.

### Identity

The identity is one literal zero-update row, so its CA cost is one.

### Monotonicity

For increments every coefficient depending on `N` is positive. For enabled decrements put `N=pQ`: the result is

    (3p^2+1)Q^2 + [lambda(3p+1)+2p+2]Q + 3,

which is strictly increasing in `Q`. For tests both `N` and `floor(N/p)` are nondecreasing, and all displayed coefficients are positive; this remains true on either enabled test domain separately. Identity cost is constant. Thus each enabled primitive macro is nondecreasing in its encoded positive input, for the same operation and prime. All macro costs are positive.

## 4. Why every static orientation has the same compiler constants

The class fixes the normalized program, the two-register recorder, the five primes, all literal prime templates including shared restorers, and the compiler conventions. Only the bijection from the two incoming edges of each collision pair to bits zero and one can change. Its 233 choices give `2^233` assignments.

### Recorder layer

Each pair replaces its two incoming rows with the same 21-row graph and adds 16 private controls. The two original source operations are retained at their original source controls and are merely attached to the opposite private bit-entry controls when that pair is flipped. Every other private row is fixed. Hence

    five-counter controls = 792+16*233 = 4520,
    five-counter rows = 1024+19*233 = 5451.

More importantly, the multiset of source groups `(selected prime, set of outgoing primitive symbols)` is unchanged. At original controls it retains the original operations; all private source groups have a fixed shape.

The prime compiler shares restorers by destination, so source groups alone would not establish invariance. Every original data operation entering a recorder has a distinct private entry destination. Swapping a pair therefore merely exchanges which of those two private destinations, if any, needs a restorer and which prime it uses. Its contribution to the multiset of restorer primes is unchanged. Nonrecording destinations and all remaining private destinations are fixed. This proves restorer-prime multiset invariance under every individual flip. Because flips of distinct pairs affect distinct private entry destinations and do not change any source-group operation, the argument applies after any set of other flips. It therefore proves invariance for all `2^233` orientations, not only orientations one bit away from the frozen table.

The actual restorer-prime counts are:

    prime 2: 116; prime 3: 116; prime 5: 234;
    prime 7: 932; prime 11: 932.

The total is 2,330 shared restorers. The complete source-group signature is included in the receipts.

### Literal prime expansion

Private namespaces in the frozen templates are disjoint. An identity adds no private controls and one identity row. For prime `p`:

| Template | New controls | Z rows | P rows | + rows | - rows |
|---|---:|---:|---:|---:|---:|
| Increment | p+7 | 3 | 4 | p+1 | 2 |
| Decrement | p+7 | 3 | 4 | 2 | p+1 |
| Source test group | 2p+2 | 1+k | p+1 | 1 | p |
| Shared restorer | 2p+2 | 1 | p+1 | p | 1 |

For a source test group, `k=1[P present]+(p-1)*1[Z present]` is its number of enabled residue-exit rows. This table is obtained by listing actual template controls and rows. Together with the two invariant signatures above it proves invariance of the complete literal control count and primitive-symbol counts:

    controls=122622; rows=141561;
    +=33436, -=32630, 0=30, P=52036, Z=23429.

The serialization always uses class cut zero and the same natural-counter guard grammar: true for `+` and identity, equality to zero for `Z`, and positivity for `P` and `-`. An arbitrary history-bit swap does not change that grammar or the local row determinism/reverse-compatibility conditions. In particular, it cannot demand a larger class cut. Therefore `m,p,a,J`, and hence `D,S,Z,lambda`, agree for all compared machines.

For completeness, the class-cell counts also agree. A true-guard row contributes `(B,r)=(4,4)`; a zero test contributes `(2,1)`; and a positive test or decrement contributes `(2,3)`. A moving increment contributes four moving class cells and a decrement two. The common result is

    (B,r,P)=(350054,411291,199004).

The same compiler resource formulas give 269,291,358,255 local involution factors and radius bound 3,292,955,588,459,274,804 for every orientation. These are symbolic counts only.

## 5. Lifting the recorder embedding to CA clocks

For post-source-operation data factor `K`, the recorder suffix on input history `h` and bit `b` has the exact operation word

    W=0;
    (H>0, H-, W+, W>0)^h;
    H=0;
    (H+, H>0)^b;
    (W>0, W-, H+, H>0, H+, H>0)^h;
    W=0.

It ends at `(H,W)=(2h+b,0)`. The encoded positive input at each operation is `K*7^H*11^W`.

Compare histories `h+d` and `h`, with `d>=1`, and arbitrary high/low bits `a,b`.

1. Match the source operation, entry test, and the first `h` transfer iterations. Encoded input ratios are `7^d`.
2. Skip the higher run's remaining `d` transfer iterations, then match `H=0`. The ratio is `11^d`.
3. If `a=b=1`, match preparation; if `a=1,b=0`, skip higher preparation; if `a=b=0`, neither has preparation. Then skip `d` higher doubling iterations.
4. For the only different case, `a=0,b=1`, host the lower preparation in the first higher doubling iteration: skip that iteration's `W>0,W-`, then match its first `H+,H>0` pair to the lower preparation. The encoded ratio is `11^(d-1)>=1`. Finish this higher iteration and its next `d-1` iterations.
5. The work counters are now both `h`, and the higher history exceeds the lower by `2d+a-b>=1`. Match the remaining `h` doubling iterations and final test at ratio `7^(2d+a-b)`.

This is an order-preserving injection of lower operations into higher operations, matching identical counter/symbol pairs. Every matched input is at least as large, and both matched operations are enabled. The preceding monotonicity theorem, using the now-proved common lambda, orders their **whole CA macro costs**. Higher unmatched operations have positive costs. Since its operation word is longer by `10d+2(a-b)>=8`, the higher recorder's total CA cost is strictly larger.

At equal input history, bit one has a strictly larger cost than bit zero: match the common transfer, skip the two bit-one preparation operations, and match the rest at history gap one. Equal history and equal bit give equal cost. A nonrecording edge has nondecreasing cost at larger history; it can tie if it is an identity.

The proof does not attempt to align individual literal physical-counter rows across two prime macros. It aligns whole five-counter primitives, whose complete CA duration has already been established. That distinction avoids an invalid cancellation or an unsupported pointwise claim about physical counters.

## 6. Prefix-optimality and startup consequence

For a fixed finite enabled normalized trace, the first-encounter orientation gives bit zero to the first used incoming member of each encountered pair and one to its companion. An alternative's first encountered differing pair has bits zero versus one and equal input histories. It creates history gap one and a strict CA-clock delay.

Subsequent recording steps preserve positive history gap because

    d'=2d+b_alternative-b_first >=2d-1>=1.

Nonrecording steps preserve the gap. The recorder comparison above makes every subsequent recording macro more expensive and every nonrecording macro no cheaper. Summing proves simultaneous minimal cumulative CA arrival time at every normalized boundary. Equality through a prefix holds exactly when the orientations agree on every pair encountered in that prefix. Once strict, both history and accumulated clock inequalities remain strict at every later boundary.

All compared runs use common data, common initial history `h0>=0`, clean work counter `W=0`, and common positive cofactor coprime to 2310. The normalized trace must specify enabled edge identities, including loop iterations. Every enabled macro terminates by the frozen transfer/doubling rank invariants, so the finite arrival clocks are well-defined.

Every promised startup with natural `L,R,T` first encounters the same six members:

    entry, v0000z, n0001e0, n0001e1, n0001e2, n0001e3.

The frozen optimized source assigns all six bit zero. It is therefore CA-clock minimal at every startup boundary simultaneously over that input family. Exactly `2^227` static assignments attain the complete-startup minimum, with arbitrary labels at the other 227 pairs. This counts assignments, not machines modulo isomorphism.

For clean `T=0`, put `A=C*2^L*3^R` and `q_p=floor(A/p)`. The actual five-counter startup comprises five identities, one prime-5 test, six prime-7 tests, and twelve prime-11 tests, at unchanged encoded value `A`. Its exact minimum CA clock is

    38A^2+2q_5^2+12q_7^2+24q_11^2
    +2(lambda+1)(19A+q_5+6q_7+12q_11)+62.

At `A=1` this is `38lambda+138=1394018396`. The result does not say nonzero-`T` startup clocks are small, nor does it optimize the recorder, prime encoding, geometry, or arbitrary universal constructions. The first-encounter choice for an arbitrary full unbounded run is not claimed to be uniformly extractable from its machine/input description.

## 7. Executable checks and limits of their scope

The independently written exact checker passes the following finite checks:

- Complete reconstruction of all 5,451 five-counter rows and all 141,561 literal two-counter rows, plus serialized-branch equivalence
- Actual normalized collision-pair/bijection coverage, start/halt normal form, and global deterministic/reversible primitive-row conditions
- Template-ledger reconstruction from the actual group/restorer signatures
- Every one of the 233 single-pair flips, plus the all-flipped assignment, plus the actual predecessor orientation
- 21,277 successful macro traces and 10,136 blocked macro traces, traversing 2,795,605 actual literal rows; successful traces compare moving count, square variation, and zero-update count separately
- 8,112 adjacent enabled-input monotonicity comparisons, including floor transitions
- 975 explicit recorder embeddings, checking 62,361 mapped primitive operations and strict total CA cost
- 64 startup inputs and all 64 assignments to their six encountered pairs: 4,096 comparisons at 36,864 normalized boundaries, with equality/strictness checked at each boundary
- A separate direct traversal of the actual 138-row empty startup, reproducing its exact derived CA clock

The 64 startup inputs are `L,R in {0,1}`, `T in {0,1,2,3}`, `C in {1,13}`, and `h0 in {0,1}`. The recorder embedding inputs are `K in {1,13,30}`, `h=0,...,12`, gaps `d=1,...,6`, all four bit pairs, plus equal-history comparisons of bit one against bit zero.

These bounded checks verify the executable reconstruction and corroborate the unbounded proof. They neither enumerate `2^233` assignments nor replace the structural invariance/embedding arguments. The mathematical theorem is not proof-assistant formalized. No universal computation was completed, and no new universality attribution is made.

## 8. Review of the completed producer proof

The complete `CA_CLOCK_DOMINATION.md`, including the separately stated predecessor/optimized comparison and closed recorder suffix, has now been reviewed. **No substantive correction is needed.** The reviewed final proof SHA-256 is:

    f7385dc48b48fb4f3f95ca082477f36184d6b9cd83f8a97962e9edcc75f94c4c

The claim comparing the two frozen sources beyond startup is not assumed merely because one has a first-encounter-optimal startup. It has its own valid proof: the actual old/new assignments differ at exactly four pairs, whose targets are `n0001_1`, `n0001_2`, `n0001_3`, and `tm_A0_pop0`. Both use entry bit zero, clearing-decrement bit one, and exit bit zero. The four merge edges have old bit one and new bit zero. Thus their final five recording bits act by `h -> 32h+15` and `h -> 32h`, respectively. The common clearing loop gives `h=2^T-1`, so the startup history gap is exactly 15. Thereafter `d'=2d+a-b>=d` for every integer `d>=1`, and the recorder clock lemma prevents the accumulated predecessor delay from shrinking. This establishes the proof's all-later-boundaries assertion without assuming the optimized assignment is first-encounter optimal for every later computation.

`check_proof_corollaries.py` independently checks those actual pair assignments and derives the recorder phase polynomial coefficients by exact rational arithmetic. In the ordered basis `X^2, lambda*X, X, 1`, it obtains:

    transfer:   (616, 76, 60, 12)
    preparation:(152, 26, 20, 6)
    doubling:   (8208, 266, 208, 18).

These coefficients, summed over the displayed geometric progressions, give exactly the producer proof's closed suffix formula. The same independent checker replays every recorded row of all three saved traces, obtaining 138 / 210 / 348 literal rows and respectively 1,394,018,396 / 2,788,036,936 / 4,182,055,332 derived CA steps. The last trace is a continuous run through one TM transition; overlapping trace replays are not counted as distinct logical computations.

Run the supplementary check with:

    PYTHONDONTWRITEBYTECODE=1 python check_proof_corollaries.py
    PYTHONDONTWRITEBYTECODE=1 python -O check_proof_corollaries.py

Both final checkers pass in ordinary and optimized Python. Each normal/optimized receipt pair is identical after removing only its optimization-level field. The supplementary receipts bind the exact reviewed proof hash. `audit-manifest.json` binds the report, code, receipts, and logs. No parent proof file or frozen source was edited by the auditor.

## 9. Requested exact old/new empty-startup comparison

A final, separate executable corroboration was requested before freeze. `check_old_new_startup.py` independently traverses the actual frozen five-counter row tables, starting from `(START,0,0,0,0,0)` and stopping at `tm_A0_pop0`. It imports only this audit's already-verified macro coefficient function, never the producer's `clock_verify.py` or comparison program. Its normal and `-O` runs both pass and agree apart from the optimization-level field.

| Quantity | Predecessor | Optimized |
|---|---:|---:|
| Five-counter rows actually traversed | 142 | 24 |
| Final history | 15 | 0 |
| Predicted moving literal rows M | 43,591,206,890,854 | 38 |
| Predicted zero-update literal rows U | 36,344,944,169,448 | 100 |
| Predicted total square variation | 126,592,856,701,817,520,680,560,340 | 38 |
| Exact derived CA clock | **126,594,455,831,808,973,674,445,902** | **1,394,018,396** |

In each column, `lambda*M + total_square_variation + U` gives the displayed CA clock with `lambda=36684691`. Final data registers and work counter are zero in both cases. The predicted predecessor literal total is 79,936,151,060,302 rows; none of that full literal path was executed by this comparison. Only the 142 and 24 five-counter rows were traversed, charging each via its proved whole-prime formula. No CA execution occurred.

`old-new-five-row-traces.json` records every five-counter state, row, encoded input, macro coefficient triple, and resulting clock. `old-new-startup-receipt.json` and `old-new-startup-receipt-optimized.json` bind those traces and both frozen source hashes. This separately confirms the producer's optional `old-new-empty-startup-receipt.json` without changing the theorem or its reviewed hash.

Reproduce with:

    PYTHONDONTWRITEBYTECODE=1 python check_old_new_startup.py
    PYTHONDONTWRITEBYTECODE=1 python -O check_old_new_startup.py
