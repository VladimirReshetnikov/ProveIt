# Late non-repetition audit at ae736b3

## Decision

Retain four narrowly stated proposals after the late refresh: unrestricted-offset reflected-source normalization, coprimality transport through fixed prime support, translation of an arbitrary fixed-cardinality seed subset, and the arbitrary-exponent LTE divisibility normal form.

Drop the cell/field-equivalence and control-update proposal as a recommendation. Packet w already supplies the full band/time product equivalence, and newly placed packet zd explicitly supplies the numeric control-slot update view, independent controls, unchanged executable word, and last-write priority. A compiled adaptation to a later client is useful implementation evidence, but is insufficient additional conceptual content under the user's assumed-applied rule.

These are corpus-relative judgments, not claims of new mathematics or a proof of the absence of every possible textual paraphrase.

## Exact cutoff and inventory

The refresh is pinned to `ae736b383e59c32c3c3f81910ef1c1197cbfbd44`; no later moving-main assertion is made.

At that cutoff the requested research directory contains **36 packets**, a through zj. The previous audit covered a–w and five incoming ZIPs. The five ZIPs have become x, y, z, za and zb, respectively:

| Already audited archive | New placement |
|---|---|
| diophantine-lean-proof-refinements-2026-10-26.zip | x |
| diophantine-lean-further-deltas-2026-10-26.zip | y |
| proveit-lean-structural-simplifications-2026-10-26.zip | z |
| Lean_Proof_Simplification_Post_Adoption_2026-10-26.zip | za |
| ProveIt_Additional_Lean_Simplifications_2026-10-26.zip | zb |

The eight packets new to this audit are zc–zj. Their complete recursive tree inventories were retrieved, with no truncated tree response. **71 selected packet files, 575,496 bytes**, were fetched: 34 TeX inputs, three directly relevant Lean files, and 34 delivery/review/note/JSON files. Both current directory READMEs were also fetched. All **73 local texts** were checked against their Git blob SHA-1; local SHA-256 values are recorded in `late-corpus-manifest.json`.

The late `docs/incoming` directory contains only `README.md`, so there is no unexamined new incoming archive at this cutoff. Its entire difference from the earlier local README is the packet-count update and 13 new placement rows; `incoming-refresh.diff` records this 31-line unified diff. Historical intake descriptions are unchanged.

Scope: all eight main reports, including split section files, were screened for the candidate mechanisms. Relevant delivery notes, optional/future sections, candidate decisions, and independent review notes were read; candidate-specific code was inspected where wording was close. This is not a re-verification of all inherited baseline snapshots, old compiler transcripts, or historical external manuscripts transitively linked by the intake index. The original 28-packet audit remains in `exclusion-ledger.md` and `corpus-index.json`.

## New exclusion coverage by packet

Paths below are relative to
`Computability/DiophantineConsistency/research/lean-proof-simplification/`
at the exact cutoff.

| Packet | Main report | Additional mechanisms now assumed applied |
|---|---|---|
| zc | `2026-10-26zc/report.tex` | Compose the linear coefficient bound to cover a square; two scalar exponential thresholds; explicit allowed-tile decoder as the data-producing quotient constructor. Further questions extend coefficient composition/power envelopes and normalized threshold recognition. |
| zd | `2026-10-26zd/report.tex` | Negated strict-rank cutoff and tail conditional; exact-order certificates indexed by the candidate order's prime factors; bounded-complement cancellation; proof-side numeric control-slot overwrites preserving Boolean/support/capacity invariants. |
| ze | `2026-10-26ze/report.tex` | Expose five existing Jones field-evaluation lemmas; positive auxiliary norm gap; shared affine carrier domination; helical periodicity; monomial-list interpretation as list sum; eliminate determined function witnesses. |
| zf | `2026-10-26zf/report.tex` | Specialize multiplication recursion at zero; derive discrete successor comparison from set-successor membership; apply linear coefficient bound twice/optional arbitrary powers; normalize power inequality to one quadratic variable. |
| zg | `2026-10-26zg/report/report.tex` and `report/sections/` | Polynomial-identity transport into split-natural cross sums; sparse monomial-list view; quantified assignment restriction through surjectivity; Mersenne residual-exponent order obstruction and optional prime-power-divisor/block-radix recovery. |
| zh | `2026-10-26zh/report/report.tex` and `report/01-summary.tex`–`09-evidence.tex` | Finite-chain order-isomorphism rigidity; direct coprime-cardinality divisibility criterion; inline three conditional Hs residues; exact marker-only convolution response on 1991≤h<2011, including the bare collision at h=2008. |
| zi | `2026-10-26zi/report/proof_simplification_report.tex` and sections | Retained shared halted-color witness constructing pass/finish closing families. Helix, band-helper and temporal seam proposals are explicitly excluded but still part of the assumed prior baseline. Its bounded residual screen adds no new reflection formula. |
| zj | `2026-10-26zj/report.tex` | Finite-order rigidity; bounded-representative interval injection; quotient projection normalization; direct nonzero/positive coprime-cardinality witness; nonzero integer certificate via multiplication cancellation; source positivity from a selected tile without marking. |

A rejected, deferred, uncompiled, or optional mechanism remains excluded whenever it is actually proposed. These categories were not used to evade the user's restriction.

## Candidate-by-candidate comparison

### 1. Unrestricted-offset reflected source: retain, with a strict boundary

**New claim:** for arbitrary natural h, p≤1005, an aligned base b, and source digits supported in local residues at most1004,

```text
c(b + h − (1005 − p)) = if 1005 ≤ h + p then c(b + (h + p − 1005)) else 0
```

The expressions are interpreted in the actual cyclic ring; natural subtraction is guarded where needed. The old h≤1004 premise is unnecessary in this exact source identity, including offsets beyond a whole2011-field cell. The p≤1005 guard remains substantive.

**Nearest late precedent:** zh's `word/README.md` and `report/06-word.tex` give a different stronger result about the actual assembled word: a marker-only weighted convolution on the terminal band1991≤h<2011. The fetched exact candidate `word/candidates/CurrentWordTopBounds2011.lean` retains `top_reflected_source` with premise1005≤h and bounded actual kernel entries; it does not state the all-h conditional source theorem or remove the low-field premise from `CurrentReflectedGeometry2011.reflected_source`. Its proof uses that existing high-field cast identity and then the marker-tail support classification.

**Increment after assuming zh applied:** one guard-normalized identity works for low, high, and arbitrarily wrapped offsets, with a weaker entry bound. Do not claim zh's terminal-band theorem, its sharp1991 threshold, h2008 collision, or savings in its2009/2010 clients as new. Do not remove h bounds from source/budget/carry inequalities, which use them substantively.

Evidence anchors: zh `word/README.md:1–67`; zh `report/06-word.tex:1–37`; zh candidate `top_reflected_source` and `convolution_marker_tail`; zi `late_novelty_review/BOUNDED_RESIDUAL_SCREEN.json`.

### 2. Full coordinates and numeric control updates: exclude

**Old w precedent:** `2026-10-26w/report.tex:330–445` constructs a canonical band/time product equivalence with the cyclic modulus using integer cancellation and quotient/remainder, explicitly without coprimality. Unsigned cell/field coordinates are an adapter to this existing mechanism.

**New zd precedent:** `2026-10-26zd/report.tex:446–522` identifies the actual word with the tile digit function updated first at1004, then at977. It preserves the literal executable definition, handles dummy/marker maps independently, states last-write priority when positions coincide, and derives Booleanity, unconditional support, and capacity invariants. `lean/proposed/ControlSlotInvariant.lean` supplies an exact binding to the production word; `lean/checked/ControlSlotCore.lean` checks the priority and invariant laws.

The exact later single-cell point-update client is not asserted to occur byte-for-byte in zd. Nevertheless, after granting the full coordinate equivalence and the overwrite representation, transporting a point update through an equivalence is a standard residual application. No additional headline is warranted. Both the coordinate implementation and update adapters should be omitted from the list of new proposals.

### 3. Fixed-prime-support coprimality thickening: retain

**New claim:** prove a dimensional family of controller expressions congruent to one reference value modulo the fixed product of relevant primes, then transport coprimality to the moduli obtained by increasing exponents of those primes. The relevant information is prime support, not the size of the dimensional exponents. This combines a fixed reference congruence with a generic thickening lemma.

**Nearest late precedents:** zh's `controller/README.md:33–66`, zj's `evidence/current_controller_findings.md:53–72`, and zj `report.tex:164–181` simplify an auxiliary-cardinality proof by converting a nonzero projection to p∤r.val and then using the existing prime-power coprimality lemma. They preserve the chosen residue/witness and do not establish invariant prime support of the dimensional Γ family or replace repeated nonvanishing checks by a single reference value. Earlier coprime divisibility cancellation likewise concerns combining/cancelling divisibilities of fixed expressions.

**Increment:** congruence to one reference modulo fixed prime support plus exponent-independent coprimality transfer. Credit neither the already-present coprime-to-prime⇒coprime-to-power library fact alone nor local cast normalization as new.

### 4. Translate an arbitrary fixed-cardinality seed subset: retain

**New claim:** for a finite subset S of an additive commutative group, translation by t preserves its cardinality and changes its sum by |S|•t. When multiplication by |S| is invertible, choose t to attain any target sum. Applied to ZMod T, coprimality of a and T supplies invertibility. This removes dependence on a special interval's triangular sum.

**Nearest late precedent:** zj `report.tex:117–140` and `evidence/current_controller_findings.md:10–28` shorten bounded-representative injectivity for the existing translated interval. They retain the interval, its cardinality guard a≤T, and its existing construction. zh `controller/README.md:123–134` explicitly leaves the interval and orbit-transport construction unchanged. Earlier finite-fiber pushforward/sparse placement gives sum reindexing but not the target-sum group action and arbitrary-seed construction.

**Increment:** use any seed with the required cardinality and solve its sum discrepancy by group translation; triangular-number and interval-endpoint arithmetic no longer determine the semantic theorem. Do not claim generic Finset sum reindexing as new. The seed-existence/cardinality conditions and invertibility guard must remain.

### 5. Universal LTE divisibility normal form: retain

**New claim:** under the exact odd-prime/order hypotheses, establish for all k,n the equivalence

```text
p^(n + 1) ∣ g^k − 1  ↔  p^n ∣ k
```

then derive the exact order in each prime-power modulus by mutual divisibility. This replaces separate special-exponent LTE facts and an order-successor split.

**Nearest late precedents:** zd `report.tex:255–370` gives finite certificates for a fixed candidate order by checking its prime-factor divisors. It does not prove a universal p-adic exponent formula. zg `report/sections/03-local.tex:175–257` proves the Mersenne divisibility obstruction (p^d−1)|(p^u−1)⇒d|u and optional recovery of a block-radix power from a divisor of p^R; it uses remainder exponent arithmetic and prime-power divisor classification, not LTE valuation growth of g^k−1 near1.

**Increment:** arbitrary-exponent p-adic divisibility equivalence drives both order divisibilities, including the zero-exponent boundary. Retain all primality, oddness, and first-valuation hypotheses; a different finite certificate for the old concrete orders would overlap zd.

## Evidence files

- `late-corpus-manifest.json`: exact cutoff,36packet tree SHAs, eight recursive-tree inventory sizes,71selected file paths/Git blobs/SHA-256 values, current incoming-directory contents.
- `incoming-refresh.diff`: only incoming-index changes since the original audit.
- `late_sources/`: authenticated selected primary-source texts used by this audit.
- `exclusion-ledger.md`, `corpus-index.json`: original audit before the late refresh.
- `reflection-review.md`: checked reflected-source mathematics and boundary analysis.

The late audit does not change the compiler scope of any new proposal. Independent prototype compilation remains distinct from full production integration.

