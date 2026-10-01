# A paid sentinel fold for causal cyclic-tag streams

The imported [canonical-certificate report, manuscript 07](../../../../../SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/canonical-diophantine-certificates/article.tex), Part VI, proves a canonical exact-horizon cyclic-tag certificate using a global word equation and a first-failure product. The new [source](queue_causality_sentinel_fold.py) combines its content and length tests into one reverse-folded sentinel equality, and uses integer-nonnegative Boolean terms without squaring them again. The [receipt](queue_causality_sentinel_fold.json) records literal operation counts and source digests; the builder emits the complete schedules.

For any fixed program, initial word, terminal word and horizon T>=2, the sentinel schedule has at most **14T-2=(6T-2)M+8T A** operations, **T+1 positive witnesses**, and degree at most **2T**. A separate guard-free family has at most **10T+1=4T M+(6T+1)A** operations and T positive witnesses; only its union over horizons represents eventual halting. The exact-horizon construction retains causality and the unique witness. These are variable-size families, not a fixed-arity universal polynomial or a change to the established 75/87 or explicit universal frontier.

## 1. Fixed data and integer Boolean terms

A cyclic-tag program is a nonempty finite list of binary words. At phase i, a nonempty queue beginning with b loses that bit and appends the phase's word A_i if b=1, or appends nothing if b=0. Phase advances in either case; an empty queue has no successor. Empty appendants are allowed. All phase subscripts below are reduced modulo the fixed program period.

Fix initial word w, terminal word v and T>=1. Write n=|w|, h=|v|, m_i=|A_i|, and a_i=val(A_i), where the first physical symbol is the least significant bit. The supplied positive coordinates are y_0,...,y_(T-1),g, and b_i=y_i-1 is a computed register.

For every integer b, b(b-1)>=0, with equality exactly at b=0 or 1. Therefore the sum of these terms and any collection of squared residuals vanishes over positive integer coordinates exactly when all Boolean conditions and all residual equations hold. This saves the outer square on each Boolean term. It is an integer-domain argument: this finalizer need not be nonnegative on real inputs and is not claimed to be a sum of squares.

## 2. A single equality for content and length

Define the sentinel code of a word by

    S(w)=2^|w|+val(w).

Words of length k have sentinel codes in [2^k,2^(k+1)), so S is injective, including S(empty)=1. For a fixed word a,

    S(a u)=val(a)+2^|a| S(u).                         (1)

Compute polynomial expressions by a reverse fold:

    V_T=1,
    V_i=V_(i+1)+b_i[a_i+(2^m_i-1)V_(i+1)].           (2)

Once b_i is Boolean, this either leaves the suffix unchanged or prepends A_i. Hence V_0 is the sentinel code of the concatenation of the selected appendants, in chronological production order. Separately compute

    R_T=S(v),
    R_i=2R_(i+1)+b_i,
    D=val(w)+2^n V_0-R_0.                            (3)

Thus D=0 on Boolean bits is precisely the full word equality

    b_0 ... b_(T-1) v = w A_0^[b_0] ... A_(T-1)^[b_(T-1)],  (4)

where A_i^[0] is empty and A_i^[1]=A_i. There is no separate unknown length, variable-exponent operation or division in the emitted source.

For comparison with the report's forward formula, put

    d_i=1+(2^m_i-1)b_i,
    p_i=product_(j<i) d_j,
    F=val(w)+2^n sum_i a_i b_i p_i
      -sum_i 2^i b_i-2^T val(v).

Expansion of (2) gives the polynomial identity, on arbitrary signed assignments,

    D = F + 2^n p_T - 2^(T+h).                       (5)

The sentinel and forward final polynomials are not identical off their zero sets. Their positive-zero equivalence follows from Boolean typing and word-code injectivity.

## 3. Retain causality, omit only fixed positive factors

The formal queue lengths are affine expressions

    ell_0=n,
    ell_(i+1)=ell_i-1+m_i b_i.

Let I consist of the indices i<T for which ell_i is not a strictly positive constant polynomial. Define

    C=product_(i not in I) ell_i,
    G=product_(i in I) ell_i.                        (6)

Here C is a fixed positive integer, possibly 1; it is compiler metadata, not a paid product needed by the new polynomial. A length is constant exactly while all previous appendants are empty, so the source detects this without running the tag system. Zero or negative constant factors are retained. In particular, n=0 retains an identically zero factor. The report's full guard is exactly C G on every signed assignment. Omitting C removes no causal information and, in the general nontrivial case, saves the multiplication by the fixed initial length. This optimization is applied equally to every compared exact-horizon backend.

The complete new polynomial is

    P = sum_i b_i(b_i-1) + D^2 + (G-g)^2.             (7)

**Exact-horizon theorem.** Positive integer zeros of (7) correspond bijectively to legal T-step executions from w to v. The witness is y_i=b_i+1 and g=G. As execution is deterministic, the positive zero set is empty or a singleton.

Proof. At a zero, all bits are Boolean and C G=C g>0. If a proposed read is illegal, take its first illegal index. All previous lengths are positive; a legal one-symbol deletion with nonnegative production cannot make the next length negative, so the first illegal length is zero. The full product would be zero, a contradiction. Every pre-step length is therefore positive.

Let U_i be w followed by the appendants selected before step i. It is a prefix of the produced side of (4), and |U_i|=i+ell_i>=i+1. Therefore the symbol at position i of (4) is already present before production i; it is b_i. Inductively, the actual queue is U_i with its first i symbols deleted. The final suffix in (4) is v. Conversely, a legal execution gives (4), positive lengths and the positive integer g from (6), so it is a zero. Determinism fixes every bit and the remaining equation fixes g.

For the report's natural-coordinate certificate, the exact coordinate correspondence is b_i=y_i-1 and u=Cg-1. The inverse at an old zero is g=(u+1)/C; the semantic product formula proves its integrality and positivity. This inverse division belongs to the proof, not the emitted circuit.

The theorem also covers empty initial words: there are no legal T>=1 executions and the guard equation is impossible. At T=0 one may separately use the constant 0 or 1 according as w=v or not; the executable interface deliberately accepts only T>=1.

## 4. Why the guard cannot simply disappear from exact execution

For the fixed one-appendant program A=1 and initial word w=0, the true computation halts after one step. Nevertheless, for every T>=2 the proposed consumed word

    0 1^(T-1)

satisfies (4) with empty terminal word: every proposed later 1 supplies its own copy as an appendant. The lengths are ell_0=1 and ell_i=0 for all i>=1, so the guard rejects this entire family.

There is also a wrong nonempty endpoint. With A=11, initial word 0, T=2 and proposed bits 01, equality (4) holds with terminal word 1. The actual machine has already halted and never reaches that terminal queue. These are explicit obstructions to removing the guard while retaining the exact-T or specified-endpoint theorem. They are not counterexamples to an eventual-halting projection.

The imported report already states this distinction and points to the project's [earlier first-short-prefix theorem](../../1980/EXPLORATION_TAG_HALTING_WITHOUT_PREFIX_GUARDS.md). The following consequence pays the new sentinel schedule for that existing projection; it does not claim a new guard-elimination theorem.

Set v=empty and define

    E_T = sum_i b_i(b_i-1) + D^2.                    (8)

A zero gives the word equality (4). If the true computation first empties before T, it already halts. Otherwise every first T read can be reconstructed by the same available-prefix induction, and (4) says that its queue after T is empty. Hence a zero of E_T implies a genuine halt at some time at most T. A genuine first halt at T>=1 gives a zero of E_T. For every nonempty initial word,

    the system eventually halts iff there exists T>=1 and a positive zero of E_T.

Initially empty words are handled separately at time zero. There is no assertion that every larger T admits a zero after an earlier halt, or that such later zeros form a unique witness. The family in the first paragraph gives explicit noncanonical later zeros.

## 5. Paid schedules and their limits

`build(...,mode='sentinel')` emits (7). The comparison mode `forward` emits the report's forward length/content/guard polynomial with squared Boolean terms; `forward_nonnegative` uses the same forward residuals and the integer-nonnegative Boolean terms. All three use the same positive shifts, constant-positive-factor omission, fixed-literal folding, identical-expression sharing and output-ancestor pruning. Multiplication by a fixed numeral other than 0 or 1 is charged as a multiplication. Constant-only calculations and the neutral 0/1 identities are compile-time simplifications.

For T>=2, a worst-case accounting for (7) is:

| Portion | M | A |
| --- | ---: | ---: |
| Positive-bit shifts and Boolean terms | T | 2T |
| Pre-step lengths ell_1 through ell_(T-1) | T-1 | 2T-3 |
| Guard product, residual and square | T-1 | 1 |
| Reverse selected-appendant fold | 2T-1 | 2T-1 |
| Consumed-word fold | T-1 | T |
| Initial-word insertion, word residual and square | 2 | 2 |
| Final addition of T+2 terms | 0 | T+1 |
| Total | 6T-2 | 8T |

In the first length update, n-1 is a fixed numeral; the first nonconstant guard factor aliases the running product. These facts explain the boundary constants. Actual empty appendants, literal 0/1 values and shared expressions can only decrease these counts. For T=1 the uniform bound is 14 operations. The guard-free source `build(...,exact=False)` drops all length and guard rows by output closure; the same accounting gives 4T M+(6T+1)A for all T>=1.

Every bit has degree 1. The reverse-fold value has degree at most T, the consumed-word fold degree 1, and G degree at most T-1 because ell_0 is constant. Thus (7) and (8) have degree at most 2T. The receipt reports propagated degree bounds, not an asserted exact degree for every constant instance.

For the literal family A=10, w=101 and v=empty, the following source counts include the full final polynomial:

| T | Forward SOS | Forward nonnegative | Sentinel exact | Sentinel eventual |
| ---: | ---: | ---: | ---: | ---: |
| 1 | 16 | 15 | 14 | 11 |
| 2 | 29 | 27 | 26 | 21 |
| 4 | 61 | 57 | 54 | 41 |
| 8 | 125 | 117 | 110 | 81 |
| 16 | 253 | 237 | 222 | 161 |
| 32 | 509 | 477 | 446 | 321 |

For this family and T>=2, the three exact counts are respectively 16T-3, 15T-3 and 14T-2. The sentinel schedule saves 2T-1 operations against the equally constant-normalized forward SOS schedule, or T-1 beyond the Boolean-term improvement alone.

The sentinel schedule is not always cheapest. If every appendant has zero content, a forward content accumulator can disappear. For A=00, w=00, v=empty and T=8, `forward_nonnegative` costs 81 operations. `choose(...)` selects the cheaper of `sentinel` and `forward_nonnegative`, breaking cost ties by degree bound and multiplication count. Consequently it never costs more than the shared-optimization forward SOS baseline. This is a two-schedule comparison, not a globally optimal circuit claim.

All input words and the horizon are fixed compiler data. No ordinary-integer input loader is claimed. T is a metalevel parameter governing the number of coordinates and operations. The guard-free existential union does not package that unbounded choice into one polynomial. Finally, the reverse fold only prepends into a known suffix; it does not provide one scalar supporting faithful polynomial insertion at both ends, so it does not evade the report's polynomial word-memory obstruction.

## 6. Executable evidence

The writer and a fresh default replay compare the complete source outputs with a separately written forward scalar oracle. The saved receipt includes:

- 1,152 complete exact-backend output identities, including 576 signed assignments, and another 128 guard-free identities, including 64 signed assignments. Identity (5) is evaluated without assuming Boolean bits.
- All 68,966 Boolean candidate streams in the stated small program/input/endpoint family, with 950 legal exact execution zeros and 281 globally balanced but acausal candidates rejected; 1,404 additional positive-box assignments check non-Boolean hats and the unique guard.
- 21,266 guard-free Boolean candidates and 1,715 bounded unions of horizons. There are 343 balanced zeros, including 155 after the true halt time. The union agrees with direct queue execution; these late zeros are recorded, not mistaken for exact runs.
- Eighteen cost/degree comparisons, the zero-content fallback, and the explicit fake-continuation family at T=2 through 16.

These checks test the emitted finite circuits. The exact execution, uniqueness and all-horizon statements follow from the preceding arguments rather than extrapolation from these fixtures. No imported report or frozen compiler is edited.

The author writer and fresh replay passed. An additional author audit outside the receipt checked 1,000 random program/frame/horizon cases against the separate multiplication/addition bounds and planner dominance. An independent root proof/source review and fresh replay passed, with 4,112 candidate streams over 36 new random programs/frames evaluated by a separate FIFO interpreter (25 exact zeros and one late guard-free zero), seven exact symbolic fold identities, and 19 long-word componentwise operation-bound checks. These additional fixtures retain their finite scope.

A second independent full proof/source review and fresh replay passed. Its separate executor and concatenation/FIFO oracle checked 2,048 complete outputs (1,024 signed), 51,258 Boolean candidates (99 exact zeros, 22 late guard-free zeros and 30 rejected acausal balances), and 1,536 literal ledgers and output closures across 384 long-word/empty-phase contexts. It also checked the imported first-failure theorem and all four local links. Neither review found a remaining issue.
