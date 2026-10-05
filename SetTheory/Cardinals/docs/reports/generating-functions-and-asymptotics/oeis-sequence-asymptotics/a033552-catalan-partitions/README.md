# Partitions into Catalan Numbers

**All-orders asymptotics, periodic corrections, and inverse growth for OEIS A033552 — Part II: conditioning, joint limit laws and two-endpoint statistics**

This research report is dated 1 October 2026; Part II was added on 5 October 2026. It was built from three manuscripts of ProveIt's incoming-reports intake: manuscript 39 of batch 73O1 (Part I) and manuscripts 06 and 10 of batch 98, merged into Part II with 06 as the base. The two batch-98 manuscripts were written independently of each other, against the same text of Part I, and answer the same questions of it; Part II prints every result of both, a result proved in both once. Manuscript 39's title-page author line, kept as delivered, is "A proof-focused research report for the ProveIt project"; its PDF metadata named the author "Research report prepared with ChatGPT". Manuscript 06's title page reads "A research article on OEIS A033552" (PDF metadata: "ChatGPT"; its delivered README: "Prepared with ChatGPT, October 5, 2026"); manuscript 10's title page and PDF metadata read "AI-assisted research report prepared for Vladimir Reshetnikov".

| Source | Manuscript | Archive | Pin | Arrived | Placed | Printed as |
|---|---|---|---|---|---|---|
| Part I | batch 73O1, no. 39 | `Catalan_Partitions_Research.zip` (*Partitions into Catalan Numbers: All-Orders Asymptotics, Periodic Corrections, and Inverse Growth*, 21-page PDF, 17 files) | `e6190a945` | `f8c3a392a` | `9df4ba51a` | Part I (Sections 1–11) and Appendices A–B; Appendix C added in the write |
| Part II base | batch 98, no. 06 | `catalan_partition_laws.zip` (*Sharp Conditioning and Joint Limit Laws for Catalan Partitions: Upper multiplicities, a corrected edge distribution, and the total number of parts*, 26-page PDF dated 5 October 2026, 17 files) | `ec4b972db` | `2172df76a` | `0fba5167f` | Part II (Sections 12–24), labels `ctp:cl:`; files prefixed `02-laws-` |
| Part II member | batch 98, no. 10 | `Catalan_Partition_Statistics_Research.zip` (*Two-Endpoint Statistics of Catalan Partitions: Non-Gaussian Length, All-Orders Conditioning, Phase-Dependent Extremes, and Inverse Tail Expansions*, 24-page PDF dated 4 October 2026, 23 files) | `0f93381e8` | `2172df76a` | `0fba5167f` | Part II, labels `ctp:te:`; files prefixed `03-endpoint-` |

The pin `e6190a94552f119e9a2140e5fea8450a045a0837` is the ProveIt commit at which manuscript 39 rechecked the two transseries READMEs it cites (2026-10-01, "Record batch 72 in the incoming README's worked examples"). The delivered `SOURCE_NOTES.md` also names `1f1981f682b2878bde51a6ad40c22777f362fc05`, which its first repository request returned, and calls it "a tree SHA, not a commit SHA". That is wrong: `1f1981f68` is a commit (2026-10-01 09:15, the pin of manuscripts 38 and 40 of the same batch); the root tree of `e6190a945` is the separate object `8e77886c`. Manuscript 06 pins `ec4b972dba46c5f0557cdc55964f286c2bcd4899` (2026-10-04 20:05, "Review Beyond-Ord Part XVI and retain three corrected provenance claims"); manuscript 10 pins `0f93381e8932d3aee3d5c2abfb5c98d128d49b9c` (2026-10-04 19:54, a merge commit) and records the blob it read of this report's `article.tex`, `39d225cc2`, which is that file's blob at both pins and immediately before the batch-98 write: both saw Part I as it stood. The placement commits `9df4ba51a` and `0fba5167f` deleted the archives from `docs/incoming`; they survive in the arrival commits `f8c3a392a` and `2172df76a`.

**Status: AI-assisted, unrefereed, not formalized.** The intakes recomputed A033552 by their own dynamic program through n = 10^6, evaluated Part I's expansion with the lattice form of the phase, hand-checked the main steps of Part II (article Section 22.5), and reran every shipped program of all three manuscripts on copies. They did not re-derive every proof.

## Files

```
README.md                                  this guide (replaces the delivered READMEs)
article.tex                                the report (LaTeX, internal bibliography; \inputs three data/ tables)
article.pdf                                the compiled report, 63 pages
SOURCE_NOTES.md                            manuscript 39's source and repository audit, as delivered
02-laws-code-README.txt                    manuscript 06's computational documentation (delivered code/README.txt)
code/catalan_partitions.py                 Part I: exact coefficients, cumulants, phase and asymptotic formulas (mpmath)
code/verify.py                             Part I: exact cross-checks, phase checks, coefficient, inverse and largest-index tables
code/symbolic_audit.py                     Part I: exact SymPy audit of the normalization and first-correction algebra
code/build.sh                              Part I: the delivered three-pass pdflatex script (fails as shipped; see below)
code/02-laws-verify.py                     06: exact integer moment numerators, edge CDF errors, exact-coefficient total
                                           variation, phase functions, the three tables and two figures
code/02-laws-audit_correction.py           06: independent central-Fourier diagnostic of the edge correction (NumPy/SciPy)
code/03-endpoint-catalan_statistics.py     10: dynamic program, saddle solver, multi-index operator, phase, spectral and
                                           quantile functions (module imported by the two scripts below)
code/03-endpoint-verify.py                 10: main audit; writes the CSV tables and verification files
code/03-endpoint-verify_cutoff.py          10: 549 exact cutoff-cylinder checks and the joint operator identity
code/03-endpoint-build.sh                  10: the delivered LaTeX build script (fails as shipped; see below)
data/verification.json                     Part I: recorded run (environment, five check lines, constants, tables)
data/coefficient_errors.csv                Part I: relative errors of the saddle and explicit expansions, n = 10^2 ... 10^6
data/inverse_errors.csv                    Part I: relative errors of the leading and corrected inverse
data/largest_index.csv                     Part I: exact and limiting law of the largest part index at n = 10^6
data/a033552_0_300.txt                     p(0), ..., p(300)
data/symbolic_audit.json                   Part I: recorded symbolic audit
data/build_and_quality_checks.json         Part I: the delivered PDF's build record (21 pages)
data/requirements.txt                      Part I: mpmath==1.3.0, sympy==1.14.0
data/02-laws-verification.json             06: constants, exact integer numerators, diagnostics, TV values, exploratory fields
data/02-laws-correction_fourier_audit.json 06: Fourier-diagnostic settings and results
data/02-laws-phase_functions.json          06: periodic mean, variance and covariance functions on a phase grid
data/02-laws-moments_table.tex             06: Table 8 of the article (\input)
data/02-laws-edge_errors_table.tex         06: Table 9 (\input)
data/02-laws-tv_table.tex                  06: Table 10 (\input)
data/02-laws-requirements.txt              06: mpmath, matplotlib, numpy, scipy (unpinned)
data/03-endpoint-verification.json         10: limit constants of W and the first ten spectral coefficients
data/03-endpoint-verification.txt          10: the nine PASS lines of its main audit
data/03-endpoint-run.log                   10: captured standard output of that audit
data/03-endpoint-cutoff_verification.json  10: the cutoff audit's record
data/03-endpoint-build_quality.json        10: build record of its delivered 24-page PDF (not shipped)
data/03-endpoint-{mean,laplace,moments,extremes,joint_covariance,cutoff_cylinders,quantiles}.csv
                                           10: the tables of Section 22.3 and all tested cases
figures/02-laws-tv_universality.{pdf,png}  06: Figure 1 (d(a) and finite data)
figures/02-laws-phase_functions.{pdf,png}  06: Figure 2 (F_0 and V_0)
```

Every file except `README.md`, `article.tex` and `article.pdf` is byte-identical to its delivery. The seven `03-endpoint-*.csv` files are CRLF as delivered, like Part I's three CSV files, and are kept so by `-text` lines in `SetTheory/Cardinals/.gitattributes`; `03-endpoint-run.log` is force-added (`*.log` is ignored). The PNG files are raster previews of the PDF figures and are not used by the article.

## Labels and numbering

Every label carries the prefix `ctp:`. Part I's 94 labels (93 delivered plus `ctp:app:edition`) are unchanged in name and number. Part II added 175: 106 with the sub-prefix `ctp:cl:` (manuscript 06's material, Part II's structure and the write's own statements) and 69 with `ctp:te:` (manuscript 10's material): **269** labels. A theorem proved in both manuscripts keeps manuscript 06's label. A build comparison of the `.aux` files shows that no existing label was lost or renumbered: Part II is inserted after Part I's Section 11 and before the appendices, which keep their letters A–C.

Text added in the writes is marked *[Write note, batch 73O1, 1 October 2026.]* (Part I's collection edition) or *[Write note, batch 98, 5 October 2026.]*. The batch-98 write added to Part I only such notes (before the contents, after the proof of Theorem 7.1, in questions 10.4 and 10.5, in the conclusion and in Appendix C), the heading `\part{...}` before Section 1, preamble macros and five bibliography entries marked "[Added in the write of batch 98, ...]". Inside Part II, statements and remarks written in the write rather than taken from a manuscript are marked [write].

## Notation in Part II

The two batch-98 manuscripts use the same letters for different objects (manuscript 06's L_n is the largest part size, manuscript 10's the number of parts; 06's u_j is 10's v_j; 10's μ_q clashes with Part I's μ), and both reuse Part I's letters. Article Section 12.3 fixes one convention before any use and lists every renamed symbol (Table 7). The main choices: number of parts N_n (not Part I's N(y)); limit of J_n − M written 𝒥_θ (06's H_θ, 10's Y_θ); moments of W written ω_q; tail sums A_h, V_h, U_h (06's A_h, V_h, B_h; 10's S_{1,h}, S_{2,h}, U_h); first correction C_h (= 10's D_h); periodic variance coefficients 𝒱_0, 𝒱_1 (06's V_0, V_1, which clash with the tail sum V_h at h = 0); spectral coefficients 𝔡_j (06's b_k, 10's d_j; not 06's d(a)); the upper quantile of W written ξ_ε. Manuscript 06's `\log4\,n/\log n` means (log 4)·n/log n. No normalization was changed.

## What is claimed

Let p(n) count partitions of n into the distinct Catalan numbers 1, 2, 5, 14, 42, … (A033552; the unit part counted once). Put α = log 4 and let μ be the large solution of n = 4^μ/√(πμ).

**Part I (manuscript 39).**

- **Explicit expansion** (Theorem 2.1): log p(n) = (α/2)μ² − ((1 + 3α)/2)μ + (23/8) log μ + C + Ψ_α(μ) + D_α(μ)/μ + O(μ^{−2}), with C = (1/4) log 2 + (3/4) log π + log G(3/2), a smooth nonconstant one-periodic phase Ψ_α given by a Fourier series in Γ(2πiℓ/α) ζ(1 + 2πiℓ/α), and an explicit periodic first correction D_α. Every further inverse-power coefficient is constructively determined (Sections 4.4 and 5.3).
- **No constant asymptotic** (Corollary 2.2): replacing Ψ_α by a constant does not give an asymptotic equivalent. Corollary 2.3 gives the first three logarithmic growth terms.
- **Inverse growth** (Theorem 2.4): the threshold at which p(n) reaches y, with leading term 8√(eα/π) exp(√(2α log y))/(2α log y)^{1/4} and its first correction; Section 6 separates the continuous inverse from the integer staircase.
- **All-orders saddle estimate** (Lemma 3.1, Theorem 3.2) with a contour proof for the noncentral arcs, under a reusable sufficient hypothesis (Section 3.4); the Barnes product, the lattice and Fourier forms of the phase (Lemma 4.1) and the moving-lattice expansion (Theorem 4.2).
- **Largest part** (Theorem 7.1): a phase-dependent limit law for the largest Catalan-part index of a uniform random partition, ∏_{j>h}(1 − exp(−4^{j−θ})); it is a discrete law, not a Gumbel law.
- **Universality** (Proposition 8.1): which coefficients depend only on the exponential and polynomial growth of the allowed part sizes.

**Part II (manuscripts 06 and 10).** Here t = t_n is the exact saddle, m = m_n ~ log n/log 4 the continuous cutoff, M = ⌊m⌋ and θ = m − M, as in Theorem 7.1.

- **Independence of the upper process** (Theorems 15.1–15.2, 06): the total-variation distance between the multiplicities above a cutoff K and independent geometric variables tends to d(K/M) = 2[Φ(√(−log a/(1 − a))) − Φ(√(−a log a/(1 − a)))] at a = K/M; independence holds exactly when M − K = o(M), with rate φ(1)(M − K)/m inside that regime.
- **Corrected edge laws** (Theorem 16.1 and Corollaries 16.3, 16.5, 06; Theorem 16.4, 10): a first-order density correction of the whole upper process with O(m^{−2}) weighted-L¹ remainder; covariances −u_i u_j w_i w_j/m; P(J_n − M ≤ h) = G_h(1 + C_h/m) + O(m^{−2}), proved in both manuscripts; the cutoff vector as a transform, jointly with the number of parts.
- **Largest index** (Section 17): a growing-offset estimate for |h| ≤ m^{1/8} (10), uniform two-sided tails (both), the first correction summed over every threshold (06), all polynomial and exponential moments, and E J_n = m + F_0(θ) + F_1(θ)/m + O(m^{−2}), Var J_n = 𝒱_0(θ) + 𝒱_1(θ)/m + O(m^{−2}) with periodic F_0, F_1, 𝒱_0, 𝒱_1 (06); t_n c_{J_n} ⇒ 4^{𝒥_θ−θ}.
- **Number of parts** (Section 18): an all-orders conditioned Gaussian coefficient operator (Theorem 14.1, 10); t_n N_n ⇒ W = Σ_k E_k/c_k with E e^{−stN_n} = ℒ(s) − s²ℒ''(s)/(2m) + O(m^{−2}) and all moments (10); **no 1/m term in the mean**, t E N_n = S_1 + O(m^{−2}), S_1 = 1 + 4π/(9√3) (10); the joint limit with the upper process and the maximum, with independence and the mgf for s < 1 (06); the first endpoint dependence Cov(tN_n, 1{J_n ≤ M+h}) = S_1 G_h A_h/m (10); small-part energies with covariance −1/m (10). Written in the write: t² Var N_n = S_2 − ω_2/m + O(m^{−2}) (Corollary 18.4) and **m Cov(t_n N_n, J_n) → −S_1 Ξ(θ)**, Ξ = Σ_h G_h A_h, with remainder O((log m)^{5/2}/m) (Theorem 18.6), which proves the value manuscript 06 recorded as an unproved candidate.
- **The law of W** (Section 19, 10 with 06): P(W > x) = Σ_j 𝔡_j e^{−c_j x} with two-sided bounds 4^{−j(j−1)/2} ≤ |𝔡_j| ≤ ϖ^{−2} 2^{−j(j−1)/2} and an explicit remainder; flatness at zero; the series in z = e^{−x} is smooth on the closed disk with the unit circle as natural boundary (Hadamard), so it is not D-finite; a convergent inverse upper-tail expansion, explicit through ε⁴.
- **Mass profile** (Theorem 20.1, 06): a uniform logarithmic mass profile with finite-dimensional Brownian-bridge fluctuations.
- **Universality** (Proposition 21.1, 06): the transition curve, the count limit, the bridge and the first-order edge laws for a lacunary class of part sequences with a gcd-one finite subset (3/2 replaced by β).

Part II answers Part I's questions 10.4 and 10.5 and supplies the growing-offset and moment results Theorem 7.1 does not assert (article Table 5).

## What is not claimed

These are the manuscripts' own limits (Part I: delivered README "Scope and status", `SOURCE_NOTES.md`, article Sections 1.2, 9 and Appendix B; Part II: article Section 12.2), kept in full:

- No exhaustive literature-priority search; no MathSciNet, zbMATH or journal-archive search, by any of the three manuscripts. The absence of a posted OEIS asymptotic is an entry-level gap, not evidence that no general theorem implies a leading term. Periodicity in geometrically restricted partitions is classical (de Bruijn, Erdős–Richmond, Flajolet–Gourdon–Dumas); the saddle and periodic-partition methods are not claimed new, only the sequence-specific formulas and their proofs. In Part II the conditioning framework is classical (Arratia–Tavaré Theorem 3, Fristedt), as are exponential convolutions, Gaussian coefficient expansions, partial fractions and Lagrange inversion; Mutafchiev's part-count theorem does not cover this case; S_1 is OEIS A121839. "A targeted search does not establish priority over all possible general partition theorems."
- No resolution of Pak's question on the exact counting complexity of A033552, and no new exact counting algorithm. No conjecture is attributed to the OEIS entry, and nothing was submitted to OEIS.
- No beyond-all-orders (exponentially small) contributions and no complete transseries: the Part II operator discards the O(tm) marking corrections and the noncentral arcs. No interval certificates: the floating-point checks corroborate and do not replace the proofs; finite-range maxima are not certified suprema.
- [Dated 5 October 2026, batch 98: no longer a limit of the report.] Part I's largest-index law is for fixed h only, and Theorem 7.1 asserts no growing-h or moment theorem; Part II now proves uniform tails, all moments, the all-threshold expansion and a growing-offset estimate for |h| ≤ m^{1/8} (Section 17). The exponent 1/8 is deliberately conservative; no moderate-deviation optimality is claimed.
- Theorem 16.1 is an L¹ statement: the corrected density need not be positive, and no L² density ratio is asserted. The independence of Theorem 18.5 is a limit statement; the finite-n covariances are nonzero. The Gaussian operator (Theorem 14.1) is not a general transfer theorem for locally analytic amplitudes (Remark 14.2). Proposition 21.1's gcd condition is sufficient, not necessary; pure powers are not covered, and its higher-order statements are not asserted for the class.
- The inverse tail of W is a sequential limit (n → ∞, then ε → 0): no uniform finite-n quantile and no integer-quantile reconstruction. Hadamard's gap theorem is the one external input of the natural boundary, and no differential-algebraicity conclusion is drawn.
- Part I's numerical program implements the Gaussian corrections E₁ and E₂ directly and lists E₁ … E₄ in the recorded data; the all-orders theorem does not rest on an unlimited symbolic implementation being supplied (Section 9.1). Manuscript 06's Fourier audit targets a continuous canonical mean, not an integer coefficient; its JSON fields marked exploratory were not claims (the write has since proved all five; Section 23), and its phase covariance is a limit of truncated-energy covariances (no L² total energy exists). Manuscript 10's weighted Laplace program uses double precision, its independent cross-checks run only through the stated small ranges (300, 60), not through 10^6, and a truncated corrected CDF may exceed one (Table 14, h = 1).
- No Lean formalization. Part I's Section 10.8 warns that the contour proof must not be called formalized merely because some algebraic operations have Lean counterparts.
- The numbers show the slow convergence plainly: at n = 10^6 the asymptotic parameter is about 1/11; the relative error after the second saddle correction is 4.66 × 10^−5, the explicit first-correction formula's is −1.06 × 10^−2, and the corrected inverse's at y = p(10^6) is 2.91 × 10^−2 (`data/coefficient_errors.csv`, `data/inverse_errors.csv`); there are only M = 11 active sizes, the scaled count variance is 0.938 against its limit 1.296, and the maximal edge CDF error falls only from 0.0201 to 0.0033 with the correction (Tables 8 and 9).

## Further questions, and the standing rule

Part II's Section 23 collects every unproved claim and proposal of both manuscripts, each with its source, sketch and what is missing: 06's eight further questions and its unproved edge formula for the number of distinct sizes D_n − M; 10's nine further questions, including its formal density correction −(1/2)(x² f_W)''/m, its expectation of a large-deviation rate function for h ∝ m and its suggested small-deviation saddle. Answered within Part II and therefore not listed as open: 06's question on the 1/m cancellation in E(tN_n) (proved by 10, Corollary 18.2) and on m Cov(tN_n, J_n − M) (the write's Theorem 18.6); 10's question on largest-index moments at first order and on the expanding upper cutoff window (06); 10's universality question in part (06's Proposition 21.1); all five exploratory JSON fields of 06. Partly answered questions stay open and are re-scoped (higher orders, TV independence from the low-index variables, minimal universality hypotheses, the log factor and the next coefficient of the mixed covariance). No claim of either manuscript was found wrong. Hazards kept on record with their explanation: 06's "log4 n/log n" notation, 10's corrected CDF above one at h = 1, and the signed corrected density (Remark 16.2).

The batch-98 dossier flagged four compressed proofs; the write re-read each and records its check in a [write] remark: 06's negative thresholds in Theorem 17.5 (Remark 17.6), 06's Proposition 21.1 (Remark 21.2), and 10's localization for marks (Remark 14.3) and central-window remainder (Remark 17.2). All four hold as stated, the second with its scope made explicit. Remark 14.4 [write] shows that 10's periodic constants of the scaled cumulants are Part I's q_0 and q_0 + (1 + q_0')/α.

## Relation to neighbouring material

- **No other report.** No other repository report or formal development treats A033552 or partitions into Catalan numbers (checked at placement and again at both writes); both batch-98 manuscripts are in this report. The manuscripts cite the transseries READMEs (`Analysis/Transseries/README.md`, `Analysis/Transseries/docs/series-and-transseries/README.md`) only for their separation of continuous and integer inverses and of formalized and unformalized results; they import no repository theorem.
- **Fabius tree.** Lemma 4.1's Mellin computation reappears for a different product in `Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/frontier-compilations/Geometric_Uniform_Convolutions_and_New_Frontiers/fabius-frontier-report-H.tex`, section "Mellin analysis and the hidden log-periodic phase": the kernel log((1 − e^{−x})/x) with Mellin transform −Γ(1 + s)ζ(1 + s)/s and the constant c₁ = π²/12 − γ²/2 − γ₁, which is this report's κ. Neither text proves the other's theorem; both are instances of the de Bruijn–Mahler mechanism, and de Bruijn's 1948 paper, cited there, was added to this report's bibliography in the batch-73O1 write. The same kernel log((1 − e^{−x})/x) appears in the proof of Part II's Theorem 18.1 (as g_0).
- **Sibling partition reports of batch 73O1** in this directory: [`a097356-sqrt-restricted-partitions`](../a097356-sqrt-restricted-partitions/) (parts at most ⌊√N⌋) and [`a022629-distinct-partition-norms`](../a022629-distinct-partition-norms/) (∏(1 + k^α q^k)). Different products in different saddle regimes; they share the standard toolkit (exact saddle with an all-orders Edgeworth expansion, noncentral-arc control, Lambert-W inversion with integer staircases), and no proposition is proved in two of them.
- **Radix-layer partitions (batch 77).** [`a174065-radix-layer-partitions`](../a174065-radix-layer-partitions/) shows that the OEIS equivalents of A174065 and A393565 (`∏(1 + z^(i b^j))`) omit a nonconstant log-periodic factor, by the same Mellin pole-lattice mechanism for a different product; no theorem is shared. Part II's Proposition 21.1 does not cover pure powers.
- **Lean.** Placement in the collection confers no formal status, and none of this report's statements is formalized.

## Building

From a scratch copy of this directory (the article `\input`s `data/02-laws-*_table.tex` and includes `figures/02-laws-*.pdf`), run

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

pdfLaTeX (MiKTeX 26.2) produced the shipped `article.pdf`: 63 pages, with no errors, no warnings, no undefined references or citations, no multiply defined labels, no duplicate destinations, and no overfull or underfull boxes. Copy back only `article.pdf`. Do not use `code/build.sh` or `code/03-endpoint-build.sh`: both change into `code/`, where there is no `article.tex`, and stop with an error.

## Rerunning the scripts

All programs write into the report's own directories when run in place: Part I's `verify.py` and `symbolic_audit.py` into `data/` beside `code/`; manuscript 10's two scripts into `data/` beside `code/` unless `--output` is given; manuscript 06's `verify.py` into `data/` and `figures/` under the package root unless `--output` is given, and its `audit_correction.py` into `data/correction_fourier_audit.json` unless a path is given. Manuscript 10's scripts import `catalan_statistics` by its delivered name. So rerun on a copy, with the delivered names restored:

```sh
R=SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a033552-catalan-partitions
W=$(mktemp -d)
# Part I
mkdir -p "$W"/p1 && cp -r "$R"/code "$R"/data "$W"/p1/ && cd "$W"/p1
uv run --no-project --with mpmath==1.3.0 python code/verify.py --max-n 1000000 --dps 60   # about 23 s; rewrites $W/p1/data
uv run --no-project --with sympy==1.14.0 python code/symbolic_audit.py                   # about 22 s
# manuscript 06
mkdir -p "$W"/m06/code && cd "$W"/m06
cp "$R"/code/02-laws-verify.py code/verify.py
cp "$R"/code/02-laws-audit_correction.py code/audit_correction.py
uv run --no-project --with mpmath==1.3.0 --with matplotlib==3.10.8 python code/verify.py --output rerun   # 1-5 min; writes rerun/data, rerun/figures
uv run --no-project --with numpy==2.3.5 --with scipy==1.17.0 python code/audit_correction.py rerun/data/correction_fourier_audit.json   # about 20 s
# manuscript 10
mkdir -p "$W"/m10/code && cd "$W"/m10
for f in catalan_statistics verify verify_cutoff; do cp "$R"/code/03-endpoint-$f.py code/$f.py; done
uv run --no-project --with mpmath==1.3.0 --with sympy==1.14.0 python code/verify.py --max-n 1000000 --dps 60 --output rerun          # about 17 s
uv run --no-project --with mpmath==1.3.0 --with sympy==1.14.0 python code/verify_cutoff.py --max-n 1000000 --dps 60 --output rerun   # about 8 s
```

Compare `rerun/...` with the shipped files under their prefixed names. Manuscript 06's `verify.py --sizes 100 1000 10000 --no-plots` and manuscript 10's `--max-n 10000` give smaller runs; manuscript 10's audit needs at least 60 digits. At the batch-98 write (Windows, Python 3.13.5) the three 06 tables and `phase_functions.json`, all seven 10 CSV files, `cutoff_verification.json` and `verification.txt` equalled the shipped files up to CRLF line ends; the two `verification.json` files and 06's `correction_fourier_audit.json` differed only in Python, platform, date and run-time strings and in last-digit (double-precision) floats; manuscript 10's rerun also writes `a033552_0_300.txt` (not shipped; see below). Part I's scripts were rerun at the batch-73O1 write with the result stated in article Section 9.4. OEIS terms embedded as test vectors (62 in `02-laws-verify.py`, 20 in `03-endpoint-verify.py` and the article, Part I's 20) are OEIS data, licensed CC BY-SA 4.0.

## Disclosures and discrepancies

- The delivered READMEs are not shipped; this guide replaces them. Their commands assume the delivered layouts: Part I's (`python -m pip install -r requirements.txt`, `python code/verify.py …`, two `pdflatex` passes) has `requirements.txt` and `build.sh` at the root; 06's (`python code/verify.py`, `latexmk … catalan_partition_laws.tex`) and 10's (`python -m pip install -r requirements.txt`, `./build.sh`) likewise. The article's Sections 9.4 and 22.6 print the delivered commands, each with a write note.
- Not shipped from the batch-98 archives (both survive in `2172df76a`): the two delivered articles and PDFs (merged into this text), the two READMEs, 06's top-level `requirements.txt` (staged as `data/02-laws-requirements.txt`; its `code/README.txt` is shipped as `02-laws-code-README.txt`), and from 10 the checksum ledger `SHA256SUMS.txt` (verified 22/22 at intake, then retired), its `requirements.txt` (a byte copy of Part I's `data/requirements.txt`), `data/cutoff_run.log` (a byte copy of `data/cutoff_verification.json`) and `data/a033552_0_300.txt` (the same values as Part I's `data/a033552_0_300.txt`, without its comment line; regenerated by the rerun).
- `02-laws-code-README.txt` and the two 06 scripts name the delivered paths (`code/verify.py`, `data/verification.json`, `figures/*.pdf`, …); the 10 scripts write `data/<name>.csv` etc. under delivered names; `data/03-endpoint-build_quality.json` describes 10's delivered 24-page PDF and `data/build_and_quality_checks.json` Part I's delivered 21-page PDF, neither shipped. `data/02-laws-requirements.txt` pins nothing; the versions above are those of the recorded runs and of the write's rerun.
- Manuscript 06's recorded run reports 10.65 s (Linux); on this machine the full run took 1–5 minutes depending on load.
- The figures' axis labels write H_θ for the limit 𝒥_θ of J_n − M (Figure 2's caption says so).
- `SOURCE_NOTES.md` mislabels the commit `1f1981f68` as a tree (above), and refers to `data/verification.json` and `data/symbolic_audit.json` by their (unchanged) paths.
- The delivered bibliography of manuscript 39 omitted de Bruijn's paper on Mahler's partition problem, the origin of the phenomenon Section 1.2 attributes to Erdős–Richmond's discussion; it is added and marked.

## Provenance

Appendix C of the article records Part I's source, pin, edit history and the map from delivery names to shipped paths; the delivered Appendix B records manuscript 39's own search scope. Section 12 records Part II's two sources, their pins, what each contributed, the merge choices and both manuscripts' non-claims. The placement commits record the batch decisions: `9df4ba51a` (no repository report treated A033552; the batch-73O1 partition manuscripts stay in separate reports) and `0fba5167f` (manuscripts 06 and 10 answer the same questions of this report and are merged into one Part II, 06 as the base).
