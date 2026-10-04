# Independent review of balanced packed matrix outputs

**PASS; no further change requested.** I read the entire final helper and corrected companion, authenticated all six declared dependency pins, and independently checked both complete saved arrays. The actual fixed-table source has **2,462 = 1,124M + 1,338A**, **150 positive witnesses**, and exact degree **35,587**. The diagnostic has **302 = 126M + 176A**, **55 positive witnesses**, and exact degree **1,363**.

| Reviewed file | SHA-256 |
|---|---|
| `matrix193_balanced_output_scout.py` | `e567a5be0cb656dfc984aa86fb306584dd837b7c24568659af222c781266d76a` |
| `matrix193_balanced_output_scout.json` | `63a4b6b269ba177603cbebec51848bc6fbcd3c04115bb3dbb367dd63a2f7c9bf` |
| `matrix193_balanced_output_scout.md` | `cfc892b2c7a577d2348c3583d968e04ab271f065003cc0bfa6316a9f05f3abde` |

The companion pin is the corrected version: the zero-set projection preserves common **non-extraction** ports. Reused extraction slack names do not imply that their values are preserved.

## Independent complete-source checks

A fresh checker reads the saved JSON as data and interprets its rows in a sparse polynomial ring; it imports and executes neither the author nor predecessor Python. It checks all **2,764 binary rows**, unique output names, topological closure, and complete row/port liveness. Direct counts agree with both ledgers above. The retained group registry and fixed context agree exactly with the atomic parent. Independently recomputed coefficient bounds, block lengths and least dyadic padding agree with the saved values, including actual `C=2^93`.

The comparisons cover all selector sums and both new split selector packs; all-value H, M, Z, q and joint-bound formulas; both signed block polynomials; all four reversed signed coefficient words; all six native cut bindings; all four matrix increments including the direct right-action SWITCH; and every one of the **20** full outer residuals. Actual coefficient-word lengths are **144,144,194,194**. A diagnostic coefficient word is identically zero and its folded source is checked as such. The actual source uses 684 distinct integer literals, with maximum magnitude bit length94.

At the declared independent cut variables, the actual H, M and Z polynomials have respectively 444,14,241 and111 terms. The four complete product residual expansions have 28,134,28,134,38,224 and38,224 terms. These are exact sparse coefficient comparisons, not samples or a claimed dense expansion of the final degree35,587 polynomial.

The native63 block agrees literally with its pinned contract after the six checked substitutions. The complete62-row finalizer is checked row by row: all20 differences and squares, all19 joins, addition of one, multiplication by the native product, and subtraction of one. Consequently the verified cut identities and downstream rows establish the complete intended polynomial, including the paid half-radix and half-low-range producers.

For degree, a fresh leading-component interpretation follows every actual row, using the exact expanded main-norm identity at its known cancellation. A new deterministic linear specialization of the input and witnesses, holding the saved valid fixed coefficients constant, gives:

| Array | Exact degree | Nonzero leading coefficient modulo1,000,000,007 |
|---|---:|---:|
| Diagnostic | 1,363 | 657,179,452 |
| Actual fixed table | 35,587 | 15,979,827 |

The companion's uniform degree proof also checks: the actual native product retains degree34,039; a length194 signed convolution residual has degree774, with nonzero leading coefficient; the SOS has degree1,548. The direct count and degree concern the whole emitted source, rather than only its replacement component.

## Signed extraction and projection

The pretyping argument remains valid. At a positive integer zero, the native integer product times `1+SOS` equals one, so all outer comparisons vanish first. The block slacks bound the supplied nonnegative block integers within their allotted Q-powers. The smaller joint sum bounds the four history fields and two SWITCH selections by P. Its unconditional minimum gives P at least six, excluding J=0; thereafter P is at least B. In the diagnostic B is at least320. Native decoding then recovers the time repunit and the selected digits. Q is the padded spatial radix; the time and marked-population radix remains B.

After decoding, each centered selected lane has magnitude strictly below P. Subtracting the paid `c0*selector_pack` from the entire selected block therefore represents exactly the signed lane word. Multiplying by the reversed signed coefficient word gives convolution coefficients with magnitude strictly below Q/2. Because Q is even, each such integer coefficient has magnitude at most Q/2−1. Summing the lower coefficients with their Q-powers proves that the *entire* lower tail has magnitude strictly below `Q^(length−1)/2`; bounding individual coefficients alone would not suffice.

The positive offsets and slacks impose those strict centered ranges on the lower tail and middle coefficient. Comparing two decompositions first modulo `Q^(length−1)` and then modulo Q proves uniqueness. The high quotient is an arbitrary signed integer represented by a difference of two positive ports; no false sign or range restriction is imposed on it. Completeness also covers zero products and negative high quotients. Thus the extracted middle values are exactly the fixed-matrix row increments. The retained direct SWITCH, histories, flow and marked-population equations recover the same ordinary-input trajectory, including x=0 and empty TILE cases.

The corrected projection claim is precise. The balanced and positive-coefficient predecessors have the same projection to their common non-extraction ports, including block hats/slacks, native cuts and native witnesses. The packed fields are all-value identical. Extraction witnesses are reconstructed separately in each direction. I independently checked the common-port census: **135** actual common non-extraction ports (126 positive witnesses, ordinary x and eight fixed coefficients), and40 diagnostic ports. Exactly eight reused names belong to changed extraction slacks; those are excluded. There is no claim of an all-value identity between the complete old/new polynomials or of a bijection between auxiliary fibers.

## Evidence and limits

The independent scratch checker and result are frozen at:

| File | SHA-256 |
|---|---|
| `/tmp/review_balanced_output_checks.py` | `e82f24021cc6c38fc0366719203f1734be6148dbc8475d5dd280e51586620218` |
| `/tmp/review_balanced_output_checks.json` | `04376b437420ffb599db65efe6172b630adc41c11382edd3eddfbefa37e2cc4a` |

I read the author’s finite diagnostic, signed-convolution and actual83-TILE fixture code, but did not repeat the large actual fixture. Its packed-field identity with the predecessor is appropriately distinguished from a complete large-integer outer-DAG evaluation or a materialized native Pell tuple. Root and author separately report fresh normal and optimized exact replays on the frozen author pins; the independent checks above are separate computations, not those replays. The strict duplicate-key parser and type-exact receipt comparison were read.

The eight program parameters remain fixed coefficients produced by the valid inherited recipe; arbitrary assignments are not asserted to describe programs. The illustrative context and diagnostic do not themselves establish universality. The directed193/unary initialization and native Pell/AND converse remain inherited theorem dependencies. Within those stated domains this is a complete fixed-arity ordinary-input construction, saving **700 operations and two witnesses** from the3,162-operation parent. It does not improve the universal84-operation frontier.
