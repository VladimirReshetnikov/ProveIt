# Bounded publication and arithmetic-interface review: moving gaps and A189281 Borel completion

This review concerns only immutable publication commit `eea1598182ea39da39d594fcc3370e6e143c7648`, relative to parent `81553ad2ccbdcf295842da96b5f56c6a1421562d`. It finds no paid ordinary-integer compiler construction in the selected interfaces. The contribution is exact finite combinatorial coefficient generation together with analytic asymptotic and summation results. There is one minor write-time notation inconsistency, recorded below. This is not a full analytic proof certification.

The host is `SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a189281-path-forest-expansions/`. Root alone controls any subsequent correction. No repository files were changed in this review.

## 1. Immutable coverage and provenance

The entire 231-line README diff was read, including its long guide, provenance, evidence and limitation paragraphs. The article diff was authenticated, not read in full. Selected resulting article spans were read in full, totalling 1,458 lines:

| Inclusive article lines | New review coverage |
|---|---|
| 3600–3740 | Earlier questions updated by the new Parts; unresolved counting recurrence and analytic-versus-count distinction |
| 4042–4206 | Model, actual-density parameters, uniform theorem statement and law corollary |
| 4985–5060 | Precise fixed-short-path multiplicity and fixed-order length-threshold additions |
| 5315–5407 | Exact rod recurrence, formal local logarithms and finite coefficient algorithm |
| 5465–5558 | Rational Bonferroni and exponential enclosures; finite diagnostics versus asymptotic proof |
| 5607–5793 | Actual-sequence inversion and the write's completed uniform remainder argument |
| 5890–5906 | Retention of the unproved “one order later” rounding claim |
| 6010–6089 | Reproduction instructions, placed-file limitations and mathematical dependency/non-claim ledger |
| 6190–6249; 6282–6297 | Analytic-completion claim boundary and notation dictionary |
| 6671–6739 | Positive-ray completion, stated domain and quadrature interface |
| 7115–7365 | Formal/differential/shift interfaces, analytic recurrence and four-index arithmetic obstruction |
| 7498–7600 | Numerical diagnostics and the numbered retained corrections |
| 7635–7740 | Unproved flat-sector, sign, recurrence, effectiveness and formalization questions |

The source06 archive article was additionally read at lines 481–492 to resolve the notation finding. Search locators elsewhere are not counted as full proof reads. The inherited intake `triage_discrete_e88ed8bf6.md` was read in full (89 lines); its own 1,634 selected manuscript-line coverage remains inherited evidence, not new coverage or a full proof audit. Its SHA-256 is `9b55f9b4a446e7c0fab7a5beebe6775c91a97c4c78713570c5daa67bada37d69` at this publication commit. The applicable retention rule was read at immutable `docs/incoming/README.md` lines 420–446. There is no applicable ancestor AGENTS file for this SetTheory host.

Exact before/after Git blobs, full-file and diff SHA-256 values, and byte hashes of every declared inclusive read span are in the companion JSON. The publication changes exactly these three files:

| File | New Git blob | New bytes | New SHA-256 |
|---|---|---:|---|
| README.md | `47e79ec877df7aa72418a3d06b0b32edbf2e0b26` | 67,117 | `dbcd9895edc806da19554821dd439bd3097f999cf42f4d895e3008c4b3002951` |
| article.tex | `580cce121ef9df8ab8db2de5afab24766cd8e360` | 390,795 | `c4d4f840f6253c42dfda96494ff9cb6fd03848276da653606e7bb95639536dd2` |
| article.pdf | `099a56f9a620c3559b63b87cc7e5c54d3448ad0f` | 1,454,496 | `6cab21d60a8fec7d6f5dee6bac3a69e5cd624a3a10f9da9d8801b26e73ec35c7` |

The PDF was hashed only. Its claimed 114 pages, successful build, layout and absence of warnings were not independently checked. The README diff SHA is `96df66c89e8e3a938e27a660822c0bd00fa4b7ed956e82f22b19c3a0f3e49b93`; the unread-in-full 4,828-line article diff SHA is `7facbc3dbb532113c72177e1dff7e0603cbce99879dc682f70583287af22dafc`.

The two retired archives were read directly from arrival `e88ed8bf6b349e63c0bb3e3ab146c582275ec0d9`:

| Archive | ZIP SHA-256 | Regular members / manifest entries |
|---|---|---:|
| `docs/incoming/ProveIt_Moving_Gap_Permutations.zip` | `c2a78ce70a4e365b1678c283e55549a8433b5efb87ca682c8f61c86a812151d3` | 21 / 20 |
| `docs/incoming/ProveIt_A189281_Borel_Completion.zip` | `64898f6a992021400f3e757f9921c3cff67560eec09ae7532fa6f46dec15e0c3` | 16 / 15 |

All 37 members and all 35 delivered checksums authenticate. At publication commit, 16 moving-gap and 12 Borel ancillary files match their archive members byte for byte; the moving-gap requirements member also matches the existing `data/02-fixed-gap-requirements.txt`. Thus the receipt has 29 placement/reuse records, not 29 newly placed files. This verifies bytes, not the behavior of any script or builder. The two articles cited at source pins `d1680cdfa40c44abf0825416b6f36a3e9ec2662c` and `79e7aab60ee856862b36c38cf32cfdb1be95313f` equal the publication's parent article bytes.

All 138 delivered moving-gap and 98 delivered Borel labels route to their prefixed host labels. The host has 479 distinct literal labels, retains all 216 parent labels, and has 975 literal reference occurrences with no missing targets. These checks do not establish compiled numbering, full transformed-body equivalence, or the mathematical correctness of every target.

## 2. Computational and ordinary-integer boundary

The moving-gap theorem quantifies over pairs of path forests and fixed truncation order `M`. Its “universal polynomials” are rational coefficient polynomials uniform across those forest pairs. This use of “universal” supplies neither a universal transition system nor a universal Diophantine polynomial.

The selected finite algorithm is concrete: `T_0=T_1=1`, and `T_N=T_{N-1}+sum_(ell=1)^(N-1) z_ell T_(N-ell-1)`. Multiplication over paths counts disjoint marked rods. The second difference of the formal logarithm gives local terms `L_q`; twice summation yields `log T_F=sum_q S_q(F)L_q`. At fixed weight each coefficient operation is finite. The source states that truncating rod weight at `2M` and inverse-size degree at `M`, followed by its finite coefficient formula, computes the first `M` corrections. The finite-locality theorem itself and the complete cluster/remainder proof were not re-proved in this review.

The Bonferroni bounds are exact finite rational inequalities, and their exponential normalization uses a positive Taylor-tail bound. The displayed finite intervals remain corroborating instances, not the all-size remainder proof. No supplied interval file or execution transcript was recomputed. Encoding these variable-order computations as some finite arithmetic circuit would still require specifying and charging the input representation, coefficient generation, array sizes, rational denominators and all guards. The selected source gives no fixed witness arity, paid operation ledger, ordinary-input compiler map or positive-integer soundness/completeness theorem.

The inversion theorem concerns only inputs equal to actual sequence values on a fixed rational ray. The completed proof correctly isolates bounded rational functions of `1/log N`, a uniform residual for each fixed order, and division by the carrier derivative. The final nearest-multiple recovery is eventual; it does not provide a numerical effective onset. No general inversion of arbitrary integer inputs or uniform bounded certificate follows. This is absence of the needed interface in the reviewed result, not a proof that no further effective theorem could be developed.

Part V uses analytic Borel–Laplace summation. “Borel” here is not a descriptive-set-theoretic encoding or an integer-computation mechanism. The canonical completion is a specified analytic function, initially for `Re n>1`. The stated shift and `VUT` recurrences act on that completion; the recurrence for the original integer counts remains explicitly unproved.

The four-index obstruction is particularly relevant to avoiding an unjustified arithmetic transfer. If completion and integer counts agreed at four consecutive integers `m,...,m+3`, their `T` combination would be rational. The established analytic forcing formula makes it `(m-2)! Q(m)/(2e)`, with a nonzero integer numerator for `m>=2`, which is irrational. This finite argument is sound given the displayed analytic forcing identity. Therefore the completion cannot simply replace the integer count at all large indices. The discrepancy is flat at each fixed inverse-power order, but its exact scale, pointwise zeros, signs and effective bounds remain open. No stronger impossibility of integer encoding is asserted here.

## 3. Retained claims and bounded proof observations

The precise multiplicity addition states fixed finite short lengths and multiplicities, with remaining lengths tending to infinity. Its density difference formula and bounded-polynomial-gradient argument match the claimed first-order effect. The fixed-order threshold addition likewise uses `S_q=n-qr` through `q=M`, with only `O(1)` discrepancies in `S_(M+1)`; after normalization this changes the order-`M` term only by `O(n^(-M-1))`. These are fixed-order consequences of the cited uniform theorem, not estimates uniform in a growing `M`.

The write keeps the informal multiplicity statement beside its precise version, and its completed inversion argument beside the earlier sketch. The unproved statement that irrational floor rounding can reintroduce an effect “one order later” is explicitly retained as a research question: the missing order-`n^-3` coefficient and nonvanishing proof are named at lines 5899–5905.

The printed small-index truncation table is retained with numbered correction `spf:bc:rem:corrections`: the exact stated floor rule gives zero at `n=8`, whereas the table uses the script's clamp to one. The guide/article correctly separate that small-index mismatch from the eventual truncation theorem. The revised period-four sign table is explicitly called floating-point diagnostic evidence, not an interval certificate or an all-index theorem. This review verifies that scope and retention, not the 50-digit quadrature results or the claimed numerical residuals. The delivered script replay and independent quadrature reported by the publication remain attributed evidence.

No additional theorem-level defect was established in the selected spans. In particular, this statement does not certify the unread full connected-cluster proof, global complex growth bounds, non-P-recursiveness proof, optimized truncation analysis, every short-path case, external references or historical novelty.

## 4. Review remark 1 — a retained write-time notation mismatch

The immutable article's notation dictionary at line 6291 maps delivered quadrature function `J(a)` to host `\mathcal J(a)`. Line 6722 defines `\mathcal J(a)=integral_0^infinity K(x)(1+x)^(-a) dx`. However line 6726 preserves the exact term

```tex
          &+\frac4nJ(n)+\frac1{n(n-1)}\mathcal J(n-1).
```

All other quadrature terms use `\mathcal J`, and a literal whole-article search finds no separate definition of plain `J(n)` at this use. Delivered source06 article lines 485–489 instead consistently define and use plain `J`; thus this is a missed renaming in the publication, not a mathematical counterexample to the quadrature identity. The narrow replacement is

```tex
          &+\frac4n\mathcal J(n)+\frac1{n(n-1)}\mathcal J(n-1).
```

The original is retained here under the incoming rule. Any host correction/rebuild belongs to root; this review and all its pins continue to describe immutable `eea159818`.

## 5. Fresh evidence and limits

The companion collector is new metadata code. It uses only read-only Git commands, ZIP decompression, hashes and literal label/reference parsing; it neither imports nor executes any delivered, frozen or predecessor program. Its own normal and optimized exact-receipt runs from `/` passed before freezing. The saved receipt binds the collector's own bytes and records all member/placement/read-span details.

No analytic suite, archived script, copied script, old reviewer, TeX builder or PDF renderer was run. No external literature was browsed or certified. The review establishes the stated provenance and narrowly examined proof/interface boundaries. It supplies no new compiler, gate saving, universal simulation or general nonuniversality theorem.

Frozen helper SHA-256: `f6e7b4f7ff8a653df2ce5c92335097af6b0edd0499b64d33efd905fdd64338b1`.

Frozen receipt SHA-256: `6977cc33b42bdbfafa59d6597dca0d9d8d8be7f224a39de2fb46962072b0f93d`.
