# Independent manuscript review: Report 69

Review date: 4 October 2026 UTC

## Verdict and exact accepted object

**PASS. No manuscript correction is required.** The frozen v5 manuscript faithfully presents the accepted two-witness and one-witness finite-clipping constructions, their resource bounds, the exact fixed-table zero-versus-one classification, the fixed-dimensional extension, and the paid POWER12 compositions. All 17 rendered pages were individually inspected. No missing mathematics, transcription error, incorrect attribution, illegible equation, clipped content, overlapping table entry, missing glyph, or unresolved reference was found.

This acceptance is for the following exact objects, not an earlier PDF with the same filename:

- Flattened `Report69.tex`: SHA-256 `9f0508066f9354b6c7d74b4d6b8a10498e632e5e31b149ff8312ffb75f82cfd0`
- Seven-module map `manuscript/MANUSCRIPT_PINS.json`: SHA-256 `38b3f7a8a3bb1f837ace42df35edffd8d7627d3af476f4869106903e31824e4c`
- `/workspace/shared/report69-build-locked-v5/Report69.pdf`: SHA-256 `fc0db742d499ee0e515700134460f78b44d3c7301f14c63c77cfa6fb9a6686ce`; 403,021 bytes; 17 US-letter pages
- v5 `BUILD_RECEIPT.json`: SHA-256 `5b830f1d22e7e4b10d08dda6a2858fc3a5ed6e14b20a1bcb64f9fe607afdda64`
- v5 `PAGE_INVENTORY.json`: SHA-256 `ebe89bfeeb39fd620145901ad0c492e49fa876fd6e6b705d2418c76baf5c17b4`

The source root is `/workspace/shared/report69-low-arity-compilers-release-20261004`. The controlling low-arity scientific manifest is `b243e39e0fd9698f9d610f0f6d2b17485a98df8e20a9412c1c38c65877a42c82`; the independent low-arity audit manifest is `6852625bc450563eeda5ad96956e3ac18da64b95ca446c654da14f3b978594b3`. These pins agree with the supplied review boundary.

At review admission the release-root PDF was an older rendering; it was deliberately not used as the accepted object. Final packaging must contain the exact accepted v5 PDF. The manuscript's release-process statements in Section 7.4 remain delivery gates for the release owner: this mathematical/manuscript review does not itself certify the release-tool tests, archive sealing, or future post-seal terminal verification.

## Method and inspection scope

The complete flattened manuscript and every one of the seven manuscript files were read. The two complete native source proofs (`PROOF.md` and `ONE_WITNESS.md`), their full controlling independent audit, the original narrower two-witness review, the source README and preservation explanation were read as inert text. The POWER12 formula and proof were cross-checked against the retained POWER12 proof, the relevant POWER12 audit material, the positive22 quotient-sign argument, and the actual retained Pell recurrence, theorem statements and constructive branches. The complete exact-degree comparison proof and its independent audit were read for the Report67 parity statement.

The review derives the central domain, degree, cost and fiber checks below from the formulas; a prior PASS verdict is not used as a substitute for checking those formulas. Prior finite evidence is read only to authenticate the manuscript's descriptions of prior results. No fresh algebra enumeration or scientific expansion is claimed.

Only read-only text/provenance inspection, primary-source web reads and standard Poppler PDF tools were used, apart from writing this separate review directory. No scientific checker, author/upstream executable, counter interpreter, physical simulator, saved schedule or Lean was run. No candidate file was edited, chmodded or retimestamped.

A standard text-only expansion of the master's six literal include lines exactly reproduces the flattened source. Independently running `pdftotext -layout` reproduces the v5 extracted text byte for byte. Independently rendering the pinned PDF with `pdftoppm -r 120 -png` reproduces all 17 inspected v5 PNGs byte for byte. The evidence is retained in `TRANSCRIPTION_CHECK.txt`, `Report69.independent.txt`, `independent-pages/`, and `INDEPENDENT_RENDER_PINS.sha256`.

## 1. Native two-witness formula and boundary cases

The natural-counter clipping induction uses the strictly positive lower bound T-t only at tested entries t<T. It does not require equality of final counters or a further test at time T. Thus loops, by-horizon acceptance, first-exactly-horizon acceptance and initially halted programs are handled correctly. The shift from natural counters to positive inputs changes the threshold from T to K=T+1. The K-squared table bits and at most K-squared times T representative transitions are explicitly paid; representative counters remain at most 2T.

The signed-binomial Lagrange basis has nodal value (K-1)! and zero at the other nodes. Its basis sum is that constant, so full and empty tables give the zero and constant rejection interpolants respectively. All denominators have been cleared into integer coefficients. The interpolation variables and clipped expressions are not additional witnesses.

The five-square zero first forces u,v into the grid. The positive-integer equality A-u=r-1 then gives the required case split: if u<K, r=1 and A=u; if u=K, A>=K. It recovers u=min(A,K), hence the unique r=A-min(A,K)+1, and similarly for the second coordinate. Table membership follows, and the converse uses exactly this positive pair. Allowing zero witnesses would break the classification, as the manuscript explicitly notes.

The substitution preserves nonzero polynomial degree, and the highest real homogeneous squares cannot cancel. Thus the exact degree is max(2K,4,2 deg F_S), with deg 0=-infinity, bounded by 4T for T>=1. Empty/full tables give 2K and all K=2 tables give degree four. At T=0 the separate five-slot formula has degree two and exactly six/seven nonzero monomials. The fixed two-zero-test program has singleton by-horizon acceptance at every T>=2 and the rejection interpolant has top coefficient -1. Its exact-time qualification and horizon-dependent delayed variant are correctly distinguished.

## 2. Native one-witness formula and exact classification

The tail polynomial is globally nonnegative and, on positive integers, is positive exactly at or above K. Each displayed cell factor therefore has precisely its own clipped-cell positive zero set. The edge and corner converses require strict positivity of w and are proved in that domain. Since the input cells are disjoint, selecting a zero factor cannot introduce an inactive witness freedom. Empty/full tables and the separate K=1 formulas are correctly covered.

Every factor is nonzero, and its exact degree is 2, 4T or 8T according to its tail count. Degree additivity gives D_S=2n_I+4Tn_E+8Tn_C; the full displayed product attains 10T^2+8T, without implying a lower bound for another representation of the full predicate. The literal distributed SOS count is 3^n_I 2^n_E, including the empty product as 1 squared. Q_S is a nonnegative product block, not generally a residual square; Q_S squared has twice its degree and the same positive zeros.

The zero-witness necessity argument is valid without an SOS assumption and even over real coefficients: restriction to an accepted tail cell vanishes on an infinite Cartesian grid, so repeated univariate root reasoning forces its entire coordinate flat. This requires joint replacement of all tail coordinates; no unjustified replacement of fixed coordinates is made. Sufficiency multiplies the squared fixed-coordinate deviations. Empty sums/products handle the all-tail/full and empty cases. The degree 2|S| is qualified to nonempty tables without an all-tail cell. The exact minimum is therefore zero precisely under closure and one otherwise, in the stated single-equation, fixed-table, unrestricted-degree class.

The d-dimensional extension uses the same domain recovery. A cell with t>=1 tails has degree 4Tt; tail incidence over the full table is dK^(d-1), giving 2T^d+4dT(T+1)^(d-1). Support in d+1 variables and the dependence on fixed dimension are correctly stated. The same closure proof applies, and K=1 is separately covered.

## 3. Resource and comparison checks

For the tensor construction, the substituted affine factor has coefficient norm i+1. Product/triangle bounds give the displayed B_K, L_K and H_K bounds after all substitutions. The support count is the Cartesian pair-degree envelope binom(2K,2)^2 plus at most 8K+2 monomials in the two extra pure-pair degree layers. The explicit exponent fields accommodate every actual exponent. These yield O(K log(K+1)) coefficient bits, O(K^4) support and O(K^5 log(K+1)) expanded bits.

The tensor circuit ledger includes constants, range products, classifications, tensor products, final squares and additions: 2K^2+m+5 multiplications and 2K+10+max(m-1,0) additions/subtractions. The uniform combined ceiling follows for K>=2. The separable coefficient transforms justify the conservative O(K^5) coefficient-operation expansion bound, with the claimed coefficient intermediate sizes.

For the one-witness form, the alternating-sign coefficient identity gives norm(p_K)=(K!)^2. Counting interior, edge and corner factors separately yields O(K^2 log(K+1)) coefficient bits rather than charging every cell at the corner's cost. Three-variable support is at most binom(D_S+3,3), yielding O(K^6) support and O(K^8 log(K+1)) expanded bits. Squaring changes constants and exact degree, not these orders.

The one-witness gate ledger correctly reuses the coordinate squares. The combined maximum is 3T^2+10T+7, and the empty table may return 1 without arithmetic. The sum of individual factor-support bounds is O(K^2); multiplying by the O(K^6) partial-product support gives the conservative O(K^8) coefficient-operation bound. Naive self-convolution for the square gives O(K^12). Integer arithmetic, bit complexity, table preprocessing and factored encoding are kept distinct.

The native comparison table faithfully reproduces these statements. The earlier three-witness construction's arity, six slots, support/storage upper bounds and degree ceiling are not retroactively changed. The Report67 parity law agrees with its source and audit: 4K^2-4 for even K; 4K^2-8 for odd K>=3; degree two at K=1. The manuscript does not inherit the comparison source's local unqualified odd-K wording at K=1. All comparisons remain between upper bounds, not instancewise orderings or optimality results.

## 4. Complete paid POWER composition

The six direct positive leaves and six distinct positive adapters, including the output once, are transcribed correctly. q_alpha is direct and strictly positive. The five full base-two residuals are displayed with every required expression; no POWER predicate is silently left as an unpaid constraint.

From the auxiliary norm, alpha=Z/4 has integer square and hence is integral; positivity gives alpha>omega>=2. The second rational recovery similarly makes u_p integral. Its negative branch is excluded specifically by integer q_alpha>=1 and beta>0. The recovered x and s_p are positive. All fifteen old equations and their natural-adapter obligations are restored. The precise imported theorems match the retained local source: the positive-index Pell characterization identifies the pair at index C, and the base-two power characterization at target 2o and modulus M_p yields 2^C=2o. Natural subtraction is reconciled with ordinary subtraction.

Completeness is properly conditional on the pinned constructive theorem pair. The positive-residue lemma pays the signs of all congruence quotients, including q_r via x^2-[y(alpha-2)]^2=(4alpha-5)y^2+1. The beta progression preserves congruences, makes q_alpha positive, and strictly increases a retained leaf q_b. It supplies infinitely many full tuples even at C=1; no bijection with old q_alpha=0 tuples is asserted.

Residual degrees 4,10,10,1,6 and the coefficient-one degree-twenty monomial are correct after positive shifts. The gap equations force positive denominators and recover the exact encoded inputs, with unencoded positive triples excluded. The ledgers are 28 witnesses/31 variables/17 square slots for the two-witness compiler and 27 witnesses/30 variables for either one-witness alternative. The unsquared alternative has twelve squares plus its product block, whereas the squared alternative has thirteen squares. Horizon-zero and distributed-SOS qualifications are explicit.

Global nonnegativity prevents cancellation of the relevant leading homogeneous parts, so the three exact composed degrees and their ceilings are correct. The gaps determine outputs, power injectivity determines A,B and the native formula determines its witness projection, while module variation keeps the complete fibers infinite. The fixed decoding support adds only a T-independent amount; no unsupported dense 30-variable or witness-height bound is inferred.

## 5. Citation, evidence and scope accuracy

The NIST primary page at https://dlmf.nist.gov/3.3#i was inspected on the review date. Equations 3.3.1, 3.3.2, 3.3.3, 3.3.3_1 and 3.3.3_2 contain the cited nodal interpolation formula, basis and basis-sum identity. The manuscript's attribution is accurate and does not assign its specific compiler construction to NIST.

The author-hosted Alon primary text at https://web.math.princeton.edu/~nalon/PDFS/null2.pdf was inspected. Lemma 2.1 states the degree-bounded finite-grid vanishing result and gives the same induction structure. The manuscript distinguishes that finite-set statement from its own explicit infinite-grid argument. The publisher record at https://www.cambridge.org/core/journals/combinatorics-probability-and-computing/article/abs/combinatorial-nullstellensatz/E32C7ED059D6B92C6C67E18CC716872A confirms volume 8 (1999), pages 7-29.

The exact pinned mathlib raw source at https://raw.githubusercontent.com/leanprover-community/mathlib4/ac77769fabe23cb237559e7f56578dbead91499f/Mathlib/NumberTheory/PellMatiyasevic.lean was readable and contains the named theorem pair, Mario Carneiro attribution and Apache 2.0 notice. The GitHub HTML view returned an internal fetch error; this was not treated as proof that the citation was broken. Local theorem statements and constructive branches were inspected, and the inert file hash is exactly `993760c797ad0ff66fa77064a616fce779550bc745cbf6c44e04f392fd0bed0a`. No remote byte-for-byte authentication or Lean rebuild is claimed by this review.

The historical author-evidence counts in Section 7.3 agree with the stored JSON/log and the 24 one-witness expansion entries. The manuscript correctly separates those author counts from the independent audit's different counts and distinguishes the original two-witness-only review from the later complete audit. Prior finite evidence is not represented as report-time execution or as proof of an infinite-domain statement.

The Report68 preservation qualification agrees with the retained explanation: seventeen historical changes in a concurrent sealing interval, followed by a distinct post-seal inventory. This manuscript review checks the fidelity of that description, not the entire historical original filesystem independently. Fixed-horizon family scope, absence of global arity/degree/priority claims, and absence of new physical or single-fold MRDP conclusions are maintained throughout.

## 6. Visual and PDF review

`PAGE_REVIEW.tsv` lists every individually inspected page, its SHA-256 and the content checked. All pages are 1020 by 1320 pixels at 120 DPI. The independently rendered images are byte-identical to those inspected. The native cell diagram distinguishes positive lattice regions from real-domain acceptance, uses the correct edge/corner labels and displays the correct witness formulas. Both resource tables are readable and agree with the proofs.

The complete PDF has a consistent header/footer, sequential page numbers, usable margins and correctly resolved equation/theorem/section references. The theorem and proof continuations are readable across page breaks. Dense bottom-of-page equations remain inside the text area and clear of the footer. References and split hashes remain legible. The three logged underfull hboxes concern the final long mathlib bibliography entry; visual inspection confirms readable wrapping without clipping or overlap. No overfull box, missing-character or unresolved-reference warning was found. The disabled-shell-escape warning is expected and is not a layout defect.

## Final disposition

The manuscript and its exact v5 rendering are accepted for release. The report's mathematical claims retain their explicitly imported POWER theorem boundary. Final archive/tool/terminal acceptance and installation of the exact accepted PDF are separate release-owner responsibilities; they are not waived by this manuscript PASS.

## Preservation result

The fresh file-level before/after inventories match exactly for all manuscript, scientific-source and audit files. Hashes, byte sizes, permission modes and nanosecond modification times were preserved. The separately inventoried flattened source, explicit v5 PDF and its 17 page images also match. Access times are excluded because reading can update them. `PRESERVATION_RESULT.txt` records the file count and exact scope. This check does not claim a separately captured directory-metadata preservation baseline.
