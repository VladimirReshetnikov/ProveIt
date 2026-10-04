# Independent manuscript review of Report55

Date: 4 October 2026. Verdict: **PASS for the reviewed 21-page manuscript and its stated fixed-context positive-integer theorem, conditional on the explicitly inherited constructive Pell and matrix-interface theorems.** No unresolved mathematical, attribution, or rendering defect was found.

## Reviewed version and method

Final article pins:

- `Report55.tex`: SHA256 `1846c0d191ff167602fb252ff3375a3809782ada03f786ae9bdea20f34b803d9`
- `Report55.pdf`: SHA256 `b5b78e9b1d485ea1fc5d09d028805e4c6d2c0abbfedfa25c367bc0449fc6d417`
- PDF: 21 Letter-size pages
- Authoritative polynomial DAG: SHA256 `95e2563fcfcaecfdc5918ffd6dd7421896350df8969a38f08cbb5f5060d80034`

The initial review candidate was independently pinned as TeX `3ba8575cdc58f8365a79fb1053f3dcf080bf0d473f9c0d69aeb4f2afeb77edce`, PDF `4f0fedd362fd176f8e6023ff2e8cdab675c824b5e07fc5ed8ad0a4b7e8982e2d`. The final pins above supersede that candidate.

The entire LaTeX source, complete extracted PDF text, every rendered page, scientific architecture and source notes, independent audit and receipts, pinned Pell theorem statements and constructive proofs, and relevant inherited matrix notes were read. The PDF was independently rendered with Poppler at 110 dpi. All 21 original page images were directly viewed. After the two editorial corrections below, all seven changed pages (1, 3, 4, 5, 6, 18, 19) were directly viewed again; all fourteen remaining rendered pages were byte-identical to the already inspected images. The final PDF text was also diffed against the original to verify the limited changes.

No scientific author program, upstream program, saved accepting schedule, or Lean process was imported or executed. The literal DAG was treated only as inert formal polynomial syntax. A fresh, small standard-library checker, `check_manuscript_data.py`, was written and inspected for this review; normal and optimized isolated runs passed with byte-identical receipts. It does not replace the earlier full semantic reconstruction, whose precise scope the manuscript accurately attributes.

## Findings resolved during review

1. Section 3.2 originally used the shorthand “exponent of the marker P0.” The underlying inherited argument is valid, but that phrase could mean the wrong character of the ambient free group. The final manuscript explicitly takes `t=E0=P0` and the retained `Ei` as a free family, sends `t` to one and the retained `Ei` to zero, distinguishes this from the ambient `P0` exponent, and gives the kernel basis `y_(i,j)=t^j Ei t^(-j)`. This closes the ambiguity without changing the theorem or any scientific source.
2. References to an “established universal 84-operation bound/record” were changed to the repository's prior 84-operation benchmark, with an explicit citation to the inherited gamma recoding note. This correctly presents background provenance and does not claim a newly verified external record.

There are no open correction requests. Ordinary paragraph and bibliography continuation across pages, and whitespace before the complete fifteen-equation POWER block, are readable layout choices rather than lost content.

## Mathematical proof review

### Statement and domain

Theorem 1.2 states a polynomial over the integers with exactly 41,309 independent strictly positive integer witnesses and the literal, strictly positive, unshifted input `x`. It recognizes the actual five-register signed countdown started at `(35426321,-19628667,1,0,x)`. The theorem does not assert zero-input, real-witness, unique-witness, finite-fold, optimal-circuit, or witness-bit-size conclusions. Its matrix equivalence and arithmetic dependencies remain explicit.

The contexts are exactly `[110` and `A0]`. The manuscript clearly separates this numerical fixture, its inherited matrix-interface equivalence, and a potential program-family construction. It does not infer universality of the fixture, implement an arbitrary-program compiler, or extend the numerical gate ledger silently to every program-dependent coefficient array.

### POWER and all positive-leaf adapters

All fifteen equations agree with the science packet and pinned `matiyasevic` / `eq_pow_of_pell` statements. The first nine impose the complete positive-index characterization, including `k<=eta`, positive auxiliary ordinate, divisibility, and both signed congruence quotients. The last six give the required bounds, strict modulus gap, auxiliary Pell relation, modulus identity, and power congruence.

The use of `k=e+1` and `m=b*out` correctly includes exponent zero by positive cancellation. The argument `a>=w+1>b` validates the natural subtraction appearing in the inherited theorem. Completeness explains why every apparently stronger positive variable is positive in the constructive choice, including `g`, `q_b`, `q_v`, and the Pell coordinates. Natural auxiliaries are represented by positive leaves minus one; `a,beta>=2` use positive leaves plus one. The stated 26 independent leaves and 15 residuals are correct.

### Binary containment

The three POWER calls and three extraction equations include strict digit and remainder bounds. `R_s=2^(M+1)` bounds every binomial coefficient strictly. The factorization over the field with two elements proves oddness exactly when the exponent's one-bits form a subset. The proof covers zero mask, zero value, and out-of-range positions; there is no omitted comparison or digit primitive. The five additional positive leaves and three residuals are correct.

### Domains, selectors, and signed packing

The macro-domain argument is well founded: the first power establishes the offset, the two bounds establish the input and initial-state ranges, the second power establishes the common horizon, and natural adapters establish nonnegative arguments before invoking each mask. It does not assume correct transitions to justify a domain or bound.

One common power-of-two offset represents every signed row coordinate. The fixed power-of-two radix factor is greater than the independently recomputed actual coefficient threshold. Since `b>97`, selector addition is carry-free and forces one branch at every position. The four slices per branch have disjoint low-bit blocks, so each selects the entire pre-state digit, with the same branch in all four rows. The proof correctly pays 388 slice predicates rather than treating selection as a primitive.

### Chronology and carry bounds

The exact shift equations enforce the initial digit, all internal joins, and the last frame; there is no reduction modulo the top power. The counter equation also forces the high post-counter digit to zero. Bound gaps ensure every final digit lies below `D`.

The signed coefficient split uses nonnegative sides. Before using an update, every side's coefficient is bounded by `(1+J_ir)(D-1) < (2+J_ir)D <= C_*D`. This uses only masks, one-hotness, and the fixed matrices, so it is noncircular. The actual maximum is `18510406623962009412894903228521`, below `2^104=20282409603651670423947251286016`. Digit equality then recovers exactly `z'=A_i z`, with the transposes demanded by right row-vector action.

### Counter, endpoint, and both directions

The loader-only mask gives the tile pre-guard `n=0`; `N=V_n+E_LOAD` then gives the tile post-guard `n'=0`. At a loader it gives decrement and a positive pre-counter. Exact chronology from `x` to zero therefore yields precisely `LOAD^x TILE*`. The separate telescoping argument shows that packing counters as naturals loses no accepting path of the original signed system.

The two common-offset endpoint equalities are exactly `X=Y`. Soundness reconstructs an actual finite chronological path from positive zeros in the correct logical order. Completeness chooses a large enough power-of-two offset for a genuine finite path, fills the bounded streams, and invokes constructive macro completeness. Positive `x` implies `h>=x>=1`. An empty tile suffix is allowed and corresponds to the central old generator, not an empty old product.

### Matrix interface

The manuscript uses the actual 96 `(K_i,G_i)` pairs and all 97 branches. The first-row implication is applied only inside the inherited subgroup with trivial intersection with the relevant lower-unipotent subgroup. The group membership of actual products and initial matrices is inherited inductively; it is not a new unpaid constraint.

The synchronized rows give `H(s) C0 G(s)^(-1)=B^(-x)`, matching the upper block of the reversed-B lower-marker shape in the correct noncommutative order. The lower-marker summary is now precise about its free-basis character and kernel heights.

The counted-suffix control proof correctly yields exactly `O* F D_c*`. A target match has a nonempty old prefix followed by `END COUNT^x`, since an empty old prefix has the wrong physical lower block. Right cancellation of `B^x` gives the old target. The displayed target copies `x` directly at zero-based entry `(4,6)`. The old lifts and END have rank five; COUNT has rank six. All 195 matrices are singular integer 7-by-7 matrices. The result is directed-semigroup membership, with no mortality or inverse-closed-group inference.

## Independent inert-data cross-check

The fresh supplemental checker independently verified:

- All 31 preserved files from the complete scientific and independent-audit packets are byte-identical in the release; all 18 entries of the scientific frozen manifest match
- The DAG pin, 41,309 distinct witness leaves, 506 ports, 23,618 residuals, all topological references, allowed binary operation vocabulary, and full gate/input/witness liveness
- 184,016 gates with 72,093 multiplications, 64,111 additions and 47,812 subtractions; body counts 48,475 / 40,494 / 24,194
- Every finalizer instruction: residual subtraction, square, and exact complete unweighted sum, totaling 70,853 gates
- 1,475 POWER and 491 Sub records; the arithmetic identities `1475*26+491*5+504=41309` and `1475*15+491*3+20=23618` also agree with the manuscript
- Full-DAG syntactic degree at most twelve, and an independent exact two-variable restriction of the entire DAG giving coefficient one for `bounds.offset.w^8 bounds.offset.g^4`; this establishes exact degree twelve without semantic substitution
- The 97 actual transposed maps and exact coefficient threshold, ordinary initial input, both tile guards, retained original tile identifiers, and literal loader matrix
- Every one of the 9,555 entries of the 195-generator lift recipe against the actual context-transferred array, the complete direct-input target, all actual matrix ranks, and the fixed contexts
- The four principal article hashes and all four deeper matrix-note hashes against the pins recorded by the inherited context source

The earlier complete independent source audit remains the source for exact reconstruction of every full residual polynomial, all expanded macro arguments, all exposed ports, and the reported full residual-degree distribution. The manuscript labels that provenance accurately. This manuscript review did not execute that author's/auditor's programs or substitute its limited supplemental cross-check for the full prior audit.

## Attribution and evidence boundaries

The bibliography identifies the scientific packet, separate audit, exact constructive Pell file and theorem names, countdown proof and receipt, synchronized rows, context transfer, counted suffix, faithful gamma recoding, lower-marker proof, earlier kernel-row construction, effective unary initialization, and the Neary-Woods primary simulation premise. Commit identifiers, Git blob identifiers, principal SHA256 values, local locations, and direct source links are supplied. The mathlib author notice and Apache 2.0 license are preserved.

The deeper matrix sources remain inherited rather than newly re-proved or re-executed here. Their modular-group/finite-graph foundations and effective simulation premises are explicitly identified as such. The primary simulation and arbitrary-program compiler are not claimed as newly audited. Likewise, recorded current-main equality is correctly tied to the prior retrieval rather than asserted as perpetually current. No gigantic complete Pell witness was materialized or claimed.

This review accepts the manuscript's account of the independent audit and its mathematical boundaries. Packaging, sealed ZIP creation, portable replay tooling, and byte-reproducible TeX builds are separate release-QA responsibilities; this review verifies the actual article bytes, source preservation, mathematical presentation, source attribution, and rendered pages.
