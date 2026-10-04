# Unconditional All-Orders Asymptotics for Two OEIS Permutation Sequences

**Stable path forests, Poisson expansions, and index inversion for A189281 and A110128 — Part II: fixed-gap asymptotics, a second derivation and its own results — Part III: rational collapse and universal integrality for directed offsets**

This research report is dated 1 October 2026; Part III was added on 3 October 2026. It was built from three manuscripts of ProveIt's incoming-reports intake: manuscript 60 of batch 73 (Part I, the base), manuscript 03 of batch 74 (Part II) and manuscript 03 of batch 85 (Part III). The first two were written independently of each other and prove the same main theorems; Part II prints only what its manuscript adds. The third read Parts I and II and proves Part I's open conjecture. Two different manuscripts are numbered 03: below, **"manuscript 03" without a batch means batch 74's** (Part II), as in the rest of this README before batch 85, and batch 85's is always called "batch-85 manuscript 03". Manuscript 60's author line is "Prepared for Vladimir Reshetnikov" (PDF metadata: "Research report prepared for Vladimir Reshetnikov"); manuscript 03's title page reads "Prepared for Vladimir Reshetnikov" and its PDF metadata names "ChatGPT, research report prepared for Vladimir Reshetnikov"; batch-85 manuscript 03's title page reads "Prepared for Vladimir Reshetnikov, AI-assisted mathematical research report" and its PDF metadata names "AI-assisted research report prepared for Vladimir Reshetnikov".

| Source | Manuscript | Archive | Pin | Arrived | Placed | Printed as |
|---|---|---|---|---|---|---|
| base | batch 73, no. 60 (cluster O2) | `oeis_path_forests.zip` (main file `article.tex`, 21-page PDF *Unconditional all-orders asymptotics for two OEIS permutation sequences*) | none | `aa43cc555` | `6e193dd4f` | Part I (Sections 1–13) and Appendix A; Appendix B added in the writes |
| addition | batch 74, no. 03 | `ProveIt_Fixed_Gap_Asymptotics.zip` (*All-Orders Asymptotics and Boundary Universality for Fixed-Gap Permutations*, 25-page PDF, 14 files) | `291fbe6bb` | `c664fc2f0` | `b669cff87` | Part II (Sections 14–22); files prefixed `02-fixed-gap-` |
| addition | batch 85, no. 03 (cluster Q1) | `OEIS_Rational_Collapse_and_Integrality.zip` (*Rational collapse and universal integrality for directed permutation avoidance: Resolving the A189281 path-forest conjecture and extending it to every fixed pair of offsets*, 23-page PDF, 16 files) | `d68b65ea0` | `317c1ce2e` | `713149ded` | Part III (Sections 23–35); files prefixed `03-rational-collapse-` |

Manuscript 60 pins no repository revision. It cites the repository only by the path `Analysis/FabiusFunction/docs/ASYMPTOTIC_COMPLETION_AUDIT.md`, as an editorial example of separating a printed approximation, a correction and an all-orders theorem, and calls it "not a dependency". Manuscript 03 pins `291fbe6bb4477e0cb2131f1e041b12a9abe363fd` (2026-10-01 18:10, "Index the387-operation C2 construction and both new degree frontiers"). That commit already held manuscript 60's archive, unopened, in `docs/incoming`; the two texts share about 1.1 % of their word 8-grams (bibliography entries and coefficient digits). Batch-85 manuscript 03 pins `d68b65ea064084fb121df9bb431b21d086f7be81` (2026-10-03 17:08, "Write batch 81L (reciprocal notes): …") and records the blob it read of this report's `article.tex`, `5b60a1ad447afe7dce58534fba447b05e401f172`, which is the blob of that file at the pin and immediately before the batch-85 write: it saw Parts I and II as they stood. Each placement commit deleted its archive from `docs/incoming`; the archives survive in the arrival commits `aa43cc555`, `c664fc2f0` and `317c1ce2e`.

**Status: AI-assisted, unrefereed, not formalized.** The intakes reran every shipped program of all three manuscripts on copies and spot-checked the mathematics (see "Checks by the intake"). They did not re-derive every proof.

## Files

```
README.md                          this guide (replaces the three delivered READMEs)
SOURCES.md                         manuscript 60's source and novelty audit, as delivered
02-fixed-gap-sources.md            manuscript 03's source audit and provenance, as delivered
03-rational-collapse-SOURCES.md    batch-85 manuscript 03's sources and contribution boundary, as delivered
article.tex                        the report (LaTeX, internal bibliography)
article.pdf                        the compiled report, 57 pages
code/build.sh                      (60) the delivered PDF build helper (does not work from code/; see below)
code/path_forests.py               (60) exact coefficient formula, stable moments, full path-tiling enumerator (standard library)
code/validate.py                   (60) brute-force distributions, OEIS values, stabilization, degree and coefficient checks
code/certify.py                    (60) exact rational Bonferroni enclosures and scaled-residual certificates
code/check_collapse.py             (60) finite symbolic tests of the rational-collapse conjecture, h = 4..16 (SymPy)
code/inverse.py                    (60) numerical inverse diagnostics from exact values (mpmath); not certified
code/02-fixed-gap-fixed_gap.py     (03) exact tiling enumerator and finite-defect coefficient engine (SymPy)
code/02-fixed-gap-verify.py        (03) its checks; regenerates the six 02-fixed-gap- data files below (SymPy, mpmath)
code/03-rational-collapse-verify.py       (85/03) exact checks and coefficient generation through order 100 (standard library)
code/03-rational-collapse-certify.py      (85/03) rational Bonferroni certificates at n = 64, 128, 256 (standard library)
code/03-rational-collapse-inverse_demo.py (85/03) optional, uncertified index-reconstruction diagnostics (mpmath)
code/03-rational-collapse-Makefile        (85/03) the delivered make targets (delivered layout only; see below)
data/coefficients_order16.json     (60) exact B_J and c_J through order 16; keys "1" (oriented) and "2" (absolute)
data/exact_values.json             (60) n = 0..21 for both sequences, by full tiling enumeration
data/validation.json               (60) counts and outcomes of the validation checks
data/validation.txt                (60) standard output of validate.py
data/bonferroni_certificates.json  (60) exact rational certificate endpoints
data/bonferroni_certificates.txt   (60) standard output of certify.py
data/collapse_checks.txt           (60) standard output of check_collapse.py (13 lines, h = 4..16, all True)
data/inverse_diagnostics.txt       (60) standard output of inverse.py
data/requirements-optional.txt     (60) sympy==1.14.0, mpmath==1.3.0 (for check_collapse.py and inverse.py only)
data/02-fixed-gap-coefficients.csv (03) c_j of A189281 and A110128, orders 0..12, exact rationals
data/02-fixed-gap-component_weight_polynomials.txt (03) the coefficients at r = s = 2 with symbolic orientation weight
data/02-fixed-gap-general_pgf_first_three.txt (03) B_1, B_2, B_3 in symbolic r, s, for both orientations
data/02-fixed-gap-numerics.csv     (03) unscaled errors of the A189281 expansion and of the inverse at n = 20, 40, 80, 120
data/02-fixed-gap-selected_oeis_values.csv (03) the A189281 b-file values used as inputs (n = 20, 40, 80, 120)
data/02-fixed-gap-verification.txt (03) the delivered run's summary output
data/02-fixed-gap-requirements.txt (03) sympy==1.14.0, mpmath==1.3.0
data/03-rational-collapse-coefficients.json       (85/03) B_J, c_J and psi_J at (2,2) for J = 0..100, c_J through order 12 at seven offset pairs, check counts
data/03-rational-collapse-verification.txt        (85/03) the nine PASS lines of the delivered run of verify.py
data/03-rational-collapse-b189281_0_30.txt        (85/03) OEIS b-file excerpt n = 0..30, a test target only (third-party, see below)
data/03-rational-collapse-bonferroni.json         (85/03) exact rational certificate endpoints
data/03-rational-collapse-bonferroni.txt          (85/03) outward-rounded decimal certificates (Table 11)
data/03-rational-collapse-inverse_diagnostics.json (85/03) index errors at n = 20, 30; marked "certified": false
data/03-rational-collapse-OEIS_proposed_note.md   (85/03) a draft OEIS note, marked "not submitted"; nothing was submitted
```

Every file except `README.md`, `article.tex` and `article.pdf` is byte-identical to its delivery. `article.pdf` is a build of this `article.tex`, not any delivered PDF. `data/coefficients_order16.json` has no final newline, as delivered. Manuscript 03's three CSV files are CRLF as delivered and are kept so by `-text` lines in `SetTheory/Cardinals/.gitattributes`; batch-85 manuscript 03's files are LF throughout.

## Labels and numbering

Part I's labels carry the prefix `spf:`. The manuscript's 78 labels are kept, unchanged after the prefix. The batch-73O2 write added three: `spf:rem:offsets-one-one`, `spf:rem:inverse-apparatus` and `spf:app:provenance` (81), and a later reciprocal note added `spf:rem:clique-analogue` (82). The batch-74 write added **49** labels with the prefix `fga:`, all in Part II (131). The batch-85 write added **85** labels with the sub-prefix `spf:rc:`, all in Part III: **216** labels in all. No existing label was renamed or removed, and no existing section, statement, equation or table number changed (checked against the `.aux` of a build of the previous text, at both writes): Part II follows Part I's conclusion as Sections 14–22 and Tables 3–6, and Part III follows Part II as Sections 23–35 and Tables 7–11, before the appendices. In particular `spf:conj:collapse` is still printed as Conjecture 11.1, now proved, and `spf:prop:collapse-implication` keeps its conditional statement, now unconditional by Corollary 26.3; dated notes say so. In new text, references to Part I's lemmas, propositions, corollaries, definitions, conjectures and remarks are written with explicit names, because Part I's shared theorem counter makes `\cref` print them as "theorem".

## What is claimed

**Part I** (manuscript 60):

- **All-orders theorem** (Theorem 1.1, `spf:thm:main`). For fixed positive offsets r, s and θ ∈ {1, 2} (oriented or absolute differences), E(1+u)^X = e^{θu} Σ_{J≤M} B_J(u) n^{-J} + O(n^{-M-1}), uniformly for |u| ≤ U, with a finite formula for every B_J (`spf:eq:Bformula`). Also deg B_J ≤ 2J, B_J(u; r, s) = B_J(u; s, r), (2J)! B_J ∈ ℤ[u], and c_1 = θ(r+s−θ).
- **Structure.** An exact profile identity (Spahn–Zeilberger's matching-of-tilings formula at u = −1, reproved), a stable tiling polynomial independent of the individual path lengths (`spf:thm:stable`), the uniform factorial-moment bound μ_k ≤ (θe²)^k/k! (`spf:lem:moment-bound`), and total-variation universality with error exp(−η′ n log n + O(n)) (`spf:thm:universality`).
- **The whole law.** An all-orders signed Charlier approximation of the full distribution in ℓ¹ (`spf:cor:distribution`).
- **The two OEIS sequences.** A189281 (θ = 1) and A110128 (θ = 2), (r, s) = (2, 2), through n^{-10}. These recover, without the guessed recurrences, the expansions the OEIS entries attribute to those recurrences; Table 1 extends both to n^{-16}.
- **Inversion.** An all-orders Lambert-W index inversion along the sequence values (`spf:thm:inverse-first`, `spf:thm:inverse-all`), and Bonferroni certificates at n = 80, 160, 320.
- **Added in the batch-73O2 write** (Remark 7.2): at (r, s) = (1, 1) the coefficient formula gives c_J^{(1)} = 1, 1, 0, 0, … (no successions, A000255(n−1) = D_n + D_{n−1}) and reproduces the Abramson–Moser expansion of A002464 (Hertzsprung's problem), as displayed in the OEIS entry, through n^{-10}. The intake checked this with the shipped generator and against exact counts to n = 800.

**Part II** (manuscript 03). Its re-derivations of Part I's theorems are listed as second routes in Table 5 and not reprinted; its coefficients of A189281 and A110128 through order 12 equal Part I's and are **not new** (Part I already has orders 11–16). New:

- **Uniformity over forest shapes** (Theorem 16.6, Corollary 16.7): the expansion holds with a constant independent of the individual path lengths for every pair of forests whose shortest path has at least K_n = ⌊(M+4) log n/log log n⌋ vertices — in particular whenever L_min log log n/log n → ∞ — but only on the disk |1+u| ≤ 1, i.e. |u| ≤ 2, which is weaker in u than Part I. (Remark 16.8, an observation of the write, notes that Part I's own proof gives the shape-uniform statement on every disk |u| ≤ U.)
- **Comparison bounds** (Theorem 16.3): for two forest pairs with the same path counts and all paths of at least K vertices, bounds on the difference of the whole generating functions and of the avoidance probabilities, and a second total-variation bound; and an n = 12 example (Remark 16.4) whose moments agree through k = 4 while the counts differ.
- the sharper moment bound μ_k ≤ θ^k (1−2k/n)^{−2k}/k! and a defect-sensitive bound (Lemmas 16.1, 16.5);
- **B_J as a polynomial in the offsets** of total degree at most J in (r, s) (Proposition 17.1), and **closed forms of c_3^{(θ)}(r, s)** for both orientations (Proposition 17.2);
- **proved all-orders integrality for the oriented one-path family**: if r = 1 or s = 1, then B_J^{(1)}(u; r, s) ∈ ℤ[u] for every J (Proposition 18.1, Corollary 18.2). By itself this does not cover A189281, whose offsets are (2, 2); Part III does;
- explicit first-order local laws P(X = j) for both sequences (Section 19);
- the inverse in a coordinate that absorbs κ_θ, with explicit terms through N^{−3} (Proposition 20.1), and a_2 = 0, a_3 = 4319/360 for A110128;
- six research questions not in Part I (Section 22).

**Part III** (batch-85 manuscript 03), for the oriented case θ = 1 only. Its re-derivations of results of Parts I and II are listed in Table 9 and not reprinted, except its second proof of the all-orders theorem, which runs through the new identity and is printed (Theorem 27.2). New:

- **The rational collapse is proved** (Theorem 26.1, `spf:rc:thm:A-collapse`): R_h(n) = 24 (n−h+1)^{\underline{h−4}} / n^{\underline{2h}} for every h ≥ 4, which is Part I's Conjecture 11.1 (`spf:conj:collapse`), together with its ratio recurrence (11.8). Corollary 26.3 records that Part I's Proposition 11.2 (`spf:prop:collapse-implication`) is now unconditional: every c_J^{(1)}(2, 2) of A189281 is an integer.
- **A single-sum formula for the stable moments** (Theorem 24.1): μ_k^*(n) = Σ_{j≤k} w_j binom(n−σ+1−j, k−j)/n^{\underline{k+j}} for every directed pair, with σ = r+s and w_j = (r−1)^{\overline j}(s−1)^{\overline j}/j!, proved through reciprocal-factorial functionals and a beta-integral evaluation of a finite Taylor jet.
- **The universal collapse** (Theorem 25.1): R_h^{r,s}(n) = Σ_{j≤h} w_j binom(h−σ, h−j)/n^{\underline{h+j}} for every (r, s) and h, by an alternating Vandermonde identity; for h ≥ σ the first σ powers of 1/n vanish, and for r = 1 or s = 1 the sum terminates.
- **Universal integrality with an exact degree law** (Theorem 28.1): B_J^{(1)}(u; r, s) = Σ_h u^h Σ_j w_j binom(h−σ, h−j) S(J−1, h+j−1) ∈ ℤ[u] for every directed pair, with deg_u B_J ≤ min{J, max(σ−1, J−σ)} and, for r, s ≥ 2 and J ≥ 2σ, deg_u B_J = J − σ with leading coefficient w_σ. At (2, 2): deg B_J = J − 4 with leading coefficient 24 for J ≥ 8, and every coefficient of u^h, h ≥ 4, is divisible by 24. This answers Part I's question 1 and Part II's question 1 (whether deg_u B_J ≤ J).
- **An inverse-factorial kernel** (Proposition 29.1): the generating function of the polynomials Φ_i(u) is (1−uz)^{σ−1} ₂F₀(r−1, s−1;; uz²/(1−uz)), a formal series; the c_J are a shifted Stirling transform of ψ_i = Φ_i(−1); at (2, 2) the ψ_i satisfy the four-term recurrence 2ψ_i + 3ψ_{i−1} + (i+1)ψ_{i−2} + (i−5)ψ_{i−3} = 0 (i ≥ 6), a recurrence for these auxiliary coefficients, not for A189281.
- **An entire Borel transform** (Theorem 30.1): Σ_{J≥1} c_J t^{J−1}/(J−1)! = 𝓔′(e^t − 1) with 𝓔 entire, so |c_J| ≤ γ_A A^{J−1}(J−1)! for every A > 0.
- **New coefficients:** c_J^{(1)}(2, 2) for J = 17..24 printed and J ≤ 100 in the data (orders 11–16 equal Part I's Table 1); A189282, A189283, A189284 ((3,3), (4,4), (5,5)) through c_6 (Table 10), whose OEIS pages display only n^{-2}; the pair (2, 3) through order 8.
- **Index reconstruction** (Proposition 32.1): in Part II's coordinates, n = N − 1/2 + (1/24 − (σ−1))/(NΔ) + (r−1)(s−1)/(N²Δ) + O(1/(N³Δ)); the second coefficient in closed form for every pair is new, the expansion is Part II's Proposition 20.1 at θ = 1.
- **Certificates** at n = 64, 128, 256 for A189281 (Table 11), computed from single-sum moments.
- ten research questions (Section 34), several continuing those of Parts I and II.

**Not new here:** the inversion method (all three Parts; see below), the leading Poisson behaviour, Tauraso's first correction in the diagonal absolute case and the inclusion–exclusion framework, which all manuscripts credit. In Part III, the one-path case of the collapse and of integrality is Part II's Proposition 18.1 and Corollary 18.2, and c_1, c_2, c_3 for general (r, s) are Part II's Proposition 17.2 at θ = 1; batch-85 manuscript 03 re-derives them without citing Part II, and Remarks 25.2 and 28.2 credit Part II.

## What is not claimed

These are all three manuscripts' own limits, kept in full (manuscript 60's article, `SOURCES.md` and delivered README; manuscript 03's abstract, its "Scope and priority" paragraph, the remarks after its theorems, `02-fixed-gap-sources.md` "What the computations do not establish" and its delivered README; batch-85 manuscript 03's status paragraph, remarks, its subsection "What this does not imply", its source and novelty ledger, `03-rational-collapse-SOURCES.md` and its delivered README "Scope").

- **The rational collapse was a conjecture in Parts I and II and is now proved in Part III.** Until batch 85, `spf:conj:collapse` was checked as a rational-function identity for h = 4, …, 16 only, the integrality of every c_J^{(1)}(2, 2) was conditional on it (`spf:prop:collapse-implication`), and all-orders integrality for A189281 was not claimed; Part II proved integrality for the oriented one-path subfamily only, and manuscript 03 warned against extrapolating it to two paths on both sides. Part III proves the collapse for every h and integrality for every directed pair. The texts of Parts I and II are kept as delivered, with dated notes.
- **Integrality is proved for directed (oriented) differences only.** The absolute model (θ = 2, A110128), whose coefficients are not integers, is not covered by Part III; integrality must not be transplanted to it, and Part I's (2J)! denominator theorem remains its arithmetic statement.
- Neither guessed OEIS recurrence (A189281's order-8, degree-11 recurrence; A110128's order-24, degree-64 operator) is proved, by any of the three manuscripts. The recurrences Part III proves are in the moment order h ((11.8)) and for the auxiliary coefficients ψ_i, not in n.
- Only the algebraic asymptotic sector: no exponentially improved transseries, no geometry-dependent exponential sector, no Borel summability, Stokes data or optimal truncation (the expansion is a Poincaré statement with M fixed). Part III's entire Borel transform does not establish Laplace summability or convergence of Σ c_J n^{-J}; its ₂F₀ and inverse-factorial series are formal; no beyond-all-orders term is identified, since forests with equal stable moments can differ; no sign rule for the c_J is claimed.
- Stable rational moments equal actual moments only in the stability range (3.13) of Corollary 3.2.
- Nothing uniform in growing offsets; Part II's shape uniformity needs every path to have at least K_n ≍ log n/log log n vertices, and the threshold is not claimed to be sharp. Part III's second proof of the all-orders theorem covers only forests whose shortest path is a fixed fraction of n, which is weaker than Part II and is not an improvement.
- The inverse diagnostics and the numerical tables of manuscript 03 and batch-85 manuscript 03 are uncertified decimals; manuscript 03's values of A189281 at n = 80 and 120 are b-file inputs, not regenerated. Part III's index reconstruction gives no explicit onset for nearest-integer rounding. The Bonferroni intervals of Parts I and III are the certified counterpart; their limits follow from the theorem, not from extrapolation.
- No peer review, no Lean or Rocq formalization, no Lean kernel run, no historical priority beyond the sources reviewed by each manuscript. Batch-85 manuscript 03's firm novelty comparison is only with this report's open conjecture; missing proofs on an OEIS page are not evidence that none exists.
- Padhi's preprint (arXiv:2608.11290) is not a dependency of any manuscript. The intake confirmed that the record exists with the cited title but did not check its content.
- **The inversion method is not new.** Section 9 re-derives the canonical transseries volume's gamma-carrier inversion (`p6:thm:gamma`, `p0:thm:perturbed-inversion` in `Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/`), and its integer-threshold remark is an instance of that volume's `p0:thm:staircase`. Remark 9.1 cites them. Manuscript 03's inverse (Section 20) and batch-85 manuscript 03's (Section 32) are further instances of the same apparatus, in coordinates shifted by κ_θ; no novelty is claimed for any of them.
- No manuscript submitted anything to the OEIS. Manuscript 03's proposed OEIS additions (orders 11 and 12) are already exceeded by Part I's Table 1. Batch-85 manuscript 03's `data/03-rational-collapse-OEIS_proposed_note.md` is a draft marked "not submitted", which asks for independent review and a stable public citation first; nothing was submitted.

## Relation to neighbouring material

- **Sibling report** [`a330266-balanced-smirnov-poisson`](../a330266-balanced-smirnov-poisson/) (batch 73, manuscript 57): the same chain of method (exact marked-subset generating function, Poisson limit, all-orders 1/n expansion of E(1+v)^X, Lambert-W inversion) for a different model, equal-rank adjacencies in balanced multiset words with limit Poisson(k−1). Neither theorem specializes to the other, so the two are separate reports. That report's tail estimate is a sketch; its README names this report's uniform factorial-moment bound (`spf:lem:moment-bound`) as the device that would make it rigorous. Remark 7.4 here (`spf:rem:clique-analogue`, a reciprocal note) points to that report's first-order local law for P(X = j) (its Corollary 8.3, `bsw:cor:local`) as the clique-model analogue of the case M = 1 of Corollary 7.3 here.
- **Transseries volume** `Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/`: the inversion apparatus cited above, and its chapter "The subfactorial" (`p8:sec:top`), the closest analogue (derangements, by citing the same gamma carrier). Its repair box already lists several sources that re-derive the gamma-envelope inverse; manuscript 03 and batch-85 manuscript 03 are two more. Part III's entire Borel transform (Theorem 30.1) concerns the algebraic sector only and makes no resurgence or summability claim.
- **Citing report** [`a181199-shifted-rectangles`](../a181199-shifted-rectangles/) (batch 85, manuscript 09; pointer added 3 October 2026): its Section 1.3 and its ProveIt bibliography entry cite this README (as "the existing path-forest reports") as the editorial precedent for separating unconditional expansions, conjectured recurrences and inverse-index approximations; none of this report's theorems is used there. Its Section 10.2 inverts its fixed-height expansion by the same Lambert-W apparatus (an instance of the transseries volume's `p0:thm:lambert-core`), with no novelty claimed, and a dated note there names this report's `spf:thm:inverse-first` and `spf:thm:inverse-all` as the same apparatus.
- **Fabius audit** `Analysis/FabiusFunction/docs/ASYMPTOTIC_COMPLETION_AUDIT.md`: cited by manuscript 60 as context only; not continued.
- **Formal status.** Placement in the collection confers no formal status, and no formal development continues this report; none of its statements is formalized, Part III included (its question 6 proposes a formalization route, as a proposal only). The only Lean declaration the report mentions (in a bracketed note at the end of Section 9), `Fabius.staircase_separation` (`Analysis/FabiusFunction/Lean/FabiusFunction/StaircaseInversion.lean`), formalizes the separation step of the staircase theorem in general; it verifies nothing specific to this report.

## Building

From a scratch copy of `article.tex`, run

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

pdfLaTeX (MiKTeX) produced the shipped `article.pdf`: 57 pages, with no errors, no warnings, no undefined references or citations, no multiply defined labels, no duplicate destinations, and no overfull or underfull boxes. Copy back only `article.pdf`.

The delivered `code/build.sh` changes into its own directory and runs `pdflatex` on `article.tex` there three times, writing `build/`. In the shipped layout it sits in `code/`, where there is no `article.tex`, so it fails; use the command above. The same holds for the `pdf` target of `code/03-rational-collapse-Makefile`.

## Rerunning the programs

Run every program on a copy, never in the report directory, and without Python's `-O` flag (the checks use assertions).

**Manuscript 60.** `validate.py` and `certify.py` write their JSON outputs into `../data/` relative to themselves (`data/exact_values.json`, `data/validation.json`, `data/bonferroni_certificates.json`), so running them in place overwrites the shipped records:

```sh
R=SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a189281-path-forest-expansions
W=$(mktemp -d); cp -r "$R/code" "$R/data" "$W/"; cd "$W"
py code/path_forests.py --order 16 --output data/coefficients_order16.json   # about 7 s
py code/validate.py > data/validation.txt                                    # about 4 s; rewrites exact_values.json, validation.json
py code/certify.py > data/bonferroni_certificates.txt                        # about 2 min; rewrites bonferroni_certificates.json
uv run --no-project --with sympy==1.14.0 python code/check_collapse.py > data/collapse_checks.txt   # about 50 s
uv run --no-project --with mpmath==1.3.0 python code/inverse.py > data/inverse_diagnostics.txt     # about 1 s
py code/path_forests.py --r 1 --s 1 --order 10 --output offsets_1_1.json      # the (1,1) check of Remark 7.2
```

Compare the outputs with the shipped `data/` files. On Windows the regenerated text files have CRLF line endings, while the shipped ones are LF, so compare ignoring line endings (JSON as parsed). The intake's run on a copy matched in this sense; `collapse_checks.txt` differs only in its timings, and `coefficients_order16.json` also in its final newline, which the regenerated file has and the delivered one lacks.

**Manuscript 03.** `02-fixed-gap-verify.py` imports its sibling by the delivered name (`from fixed_gap import …`), which fails under the prefixed name, and writes six **unprefixed** files into `../data/` relative to itself, which in the report directory would land beside manuscript 60's data. Restore the delivered names in a scratch directory:

```sh
R=SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a189281-path-forest-expansions
W=$(mktemp -d); mkdir -p "$W/code"
cp "$R/code/02-fixed-gap-fixed_gap.py" "$W/code/fixed_gap.py"
cp "$R/code/02-fixed-gap-verify.py"    "$W/code/verify.py"
cd "$W"; uv run --no-project --with sympy==1.14.0 --with mpmath==1.3.0 python code/verify.py --order 12
# writes data/{coefficients.csv, component_weight_polynomials.txt, general_pgf_first_three.txt,
#              numerics.csv, selected_oeis_values.csv, verification.txt}; compare with $R/data/02-fixed-gap-*
```

At the batch-74 write (Windows, Python 3.14, SymPy 1.14.0, mpmath 1.3.0) this order-12 run took 104 s; all eight checks passed; the three CSV files were byte-identical to the shipped ones, the two `.txt` polynomial files equal apart from CRLF line ends, and `verification.txt` equal apart from line ends and its timing line. At the intake, on the same machine under load, the order-12 run exceeded 170 s and was stopped; `--order 9` passed all checks in 72 s, and the order-11 and order-12 coefficients were recomputed separately and equal the shipped ones. A smaller `--order` rewrites the data files with shorter tables.

**Batch-85 manuscript 03.** Its three scripts rely on the delivered layout, and the shipped names break it in three ways:

- `certify.py` does `from verify import stable_mu, correction_polynomials`, which fails under the prefixed name.
- `verify.py` runs its 31 OEIS-value checks only `if datafile.exists()`, with `datafile = <output>/b189281_0_30.txt`. Under the prefixed name, or with any `--output` directory lacking that file, it **silently skips them** and still passes: it prints eight PASS lines instead of nine and records `"oeis_value_checks": 0`. `inverse_demo.py` reads the same file and fails without it.
- All three write **unprefixed** files (`coefficients.json`, `verification.txt`, `bonferroni.json`, `bonferroni.txt`, `inverse_diagnostics.json`) into `../data/` relative to themselves (`certify.py` and `inverse_demo.py` have no output option), which in the report directory would land beside manuscript 60's data.

Restore the delivered names in a scratch directory:

```sh
R=SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a189281-path-forest-expansions
W=$(mktemp -d); mkdir -p "$W/code" "$W/data"
for f in verify certify inverse_demo; do cp "$R/code/03-rational-collapse-$f.py" "$W/code/$f.py"; done
cp "$R/data/03-rational-collapse-b189281_0_30.txt" "$W/data/b189281_0_30.txt"   # without it, the 31 OEIS checks are skipped
cd "$W"
py code/verify.py --order 100 --identity-order 16    # about 15 s; writes data/coefficients.json, data/verification.txt
py code/certify.py                                   # about 2 s; writes data/bonferroni.json, data/bonferroni.txt
uv run --no-project --with mpmath==1.3.0 python code/inverse_demo.py   # about 5 s; writes data/inverse_diagnostics.json
grep -c PASS data/verification.txt                   # must print 9
# compare data/X with $R/data/03-rational-collapse-X, ignoring line endings (JSON as parsed)
```

`code/03-rational-collapse-Makefile` (targets `test`, `pdf`, `inverse`, `clean`) calls `python3 code/verify.py`, `python3 code/certify.py`, `python3 code/inverse_demo.py` and `pdflatex … article.tex` by the delivered names; it works only in such a restored copy, and its `pdf` target would build this report's `article.tex`, not batch-85 manuscript 03's article. Its `clean` target removes `article.aux`, `.log`, `.out` and `.toc` from its directory. The delivered README's `python3` is `py` here.

At the batch-85 write (Windows, Python 3.14) this recipe passed all nine checks in 15 s (`verify.py` reports 13.3 s; the delivered `coefficients.json` records 1.166 s), and `certify.py` and `inverse_demo.py` (mpmath 1.3.0) ran in 2 s and 5 s. On Windows the regenerated text files have CRLF line endings, while the shipped ones are LF; ignoring line endings, the regenerated `verification.txt`, `bonferroni.json`, `bonferroni.txt` and `inverse_diagnostics.json` equal the shipped files, and `coefficients.json` was equal as parsed apart from its `elapsed_seconds` field, which is diagnostic only. A run without the b-file excerpt passed with eight PASS lines and `"oeis_value_checks": 0`, confirming the silent skip.

## Checks by the intake

- Batch 73O2: every shipped program of manuscript 60 rerun on a copy (all passed, outputs as described above); both sequences recounted by brute force for n ≤ 9, equal to `data/exact_values.json`; the two order-ten expansions compared with the current OEIS entries, equal digit for digit (A189281: 3, 2, 1, 0, 3, 26, 101, 124, −1409, −13266; A110128: 4, 8, 68/3, …, 32213578294/14175); the coefficient d_1 of `spf:thm:inverse-first` rederived by hand (71/24 = 3 − 1/24, 95/24 = 4 − 1/24); the (1, 1) checks of Remark 7.2.
- Batch 74: manuscript 03's coefficients of both sequences at orders 0–12 equal Part I's `data/coefficients_order16.json` exactly; its general B_2 equals Part I's for both orientations identically in r, s, u (SymPy); its B_1, B_2, B_3 at (2, 2) equal Part I's; its closed forms of c_1, c_2, c_3 (Proposition 17.2) equal the values of Part I's generator at (r, s) = (1, 1), (1, 3), (2, 3), (3, 3), (2, 5) for both orientations; its third inverse coefficient reduces, in the pure-gamma case, to the corresponding block of `p6:thm:gamma`; its uncertified errors at n = 80, 120, scaled by n^{11} and n^{13}, approach Part I's c_11 and c_13 (Section 21); its program rerun as above. These checks do not replace an independent review of the proofs.
- Batch 85: the checksum ledger `MANIFEST.sha256` verified (15/15) and every suite rerun on a copy at the intake (verify 15 s, certify 2 s, inverse 4 s; outputs equal up to line endings and the elapsed-time field); **Part I's own generator `code/path_forests.py`, run on a copy, reproduced batch-85 manuscript 03's avoidance coefficients through order 12 at (r, s) = (2, 3), (3, 3), (5, 5) and (1, 3) exactly**, an independent confirmation of Theorems 25.1 and 28.1 at those pairs; B_J and c_J at (2, 2) equal Part I's `data/coefficients_order16.json` for J = 0..16; the intake read the single-sum proof (the two functionals and the endpoint argument), the alternating Vandermonde step and the convolution of Theorem 26.1 and found no gap; and checked algebraically that binom(σ,3) − (σ−1)(r−1)(s−1) = (σ−1)(r²−4rs+s²+4r+4s−6)/6, which is Part II's c_3^{(1)}. The write reran the recipe above; recomputed, in exact rational arithmetic, the Stirling-number formula (28.2) against the series of the collapse (25.1) for J ≤ 14 at (2, 2), (2, 3), (3, 3), (1, 3), (4, 2), the printed c_J(2, 2) for J = 17..24, Table 10 and the (2, 3) row, c_2 and c_3 against Part II's closed forms for 1 ≤ r, s ≤ 5, and the recurrence for ψ_i at (2, 2) for 6 ≤ i ≤ 39: all agree. These checks do not replace an independent review of the proofs.

## Disclosures and discrepancies

- **Not shipped:** the three delivered READMEs (replaced by this one), the three delivered PDFs (replaced by a build of the edited text), manuscript 03's and batch-85 manuscript 03's `article.tex` (merged as Parts II and III), and the checksum ledgers `SHA256SUMS` of manuscript 60 (19/19), `SHA256SUMS.txt` of manuscript 03 (13/13) and `MANIFEST.sha256` of batch-85 manuscript 03 (15/15), verified at placement and retired.
- **Moved and renamed files.** Manuscript 60's `build.sh` is shipped as `code/build.sh` and `requirements-optional.txt` as `data/requirements-optional.txt`; its README placed both at the archive root. Manuscript 03's `code/X` is `code/02-fixed-gap-X`, its `data/X` is `data/02-fixed-gap-X`, its `requirements.txt` is `data/02-fixed-gap-requirements.txt`, and its `sources.md` is `02-fixed-gap-sources.md`. Batch-85 manuscript 03's `code/X` is `code/03-rational-collapse-X`, its `data/X` is `data/03-rational-collapse-X`, its root `Makefile` is `code/03-rational-collapse-Makefile`, its root `OEIS_proposed_note.md` is `data/03-rational-collapse-OEIS_proposed_note.md`, and its `SOURCES.md` is `03-rational-collapse-SOURCES.md`. It ships no requirements file; `inverse_demo.py` needs mpmath, which `data/requirements-optional.txt` pins (1.3.0).
- **Delivery wording in shipped text.** Manuscript 60's "the archive", "the accompanying JSON" and "the archive's README" mean this directory, `data/coefficients_order16.json` and this README; bracketed notes say so. `SOURCES.md` refers to "Section 11" for the rational collapse, which is still Section 11, and says "Section 11's stronger rational collapse is intentionally unproved": true of manuscript 60, no longer of the report, since Part III proves it. `code/02-fixed-gap-verify.py` and `02-fixed-gap-sources.md` use manuscript 03's delivery names (`code/fixed_gap.py`, `code/verify.py`, `data/…`, `requirements.txt`). Batch-85 manuscript 03's three scripts and `Makefile` use its delivery names (`code/verify.py`, `data/b189281_0_30.txt`, `data/coefficients.json`, …; see "Rerunning the programs"); `03-rational-collapse-SOURCES.md` calls this report "the inspected repository report" and its own article "the present report", which is Part III here, and says that "only n=0..30 are included in this archive", meaning `data/03-rational-collapse-b189281_0_30.txt`; the OEIS note's "ProveIt's earlier report" and "the article" are Parts I–II and Part III of this report.
- **Third-party data.** `data/03-rational-collapse-b189281_0_30.txt` is an excerpt (n = 0..30) of the OEIS b-file of A189281 (terms 0–35 credited to V. Kotesovec, 36–39 to C. Koutschan, later ones to R. Matsuo), credited in the file and in `03-rational-collapse-SOURCES.md`. OEIS content is licensed CC BY-SA 4.0, not MIT-0. It is a validation target only, never an input to coefficient generation or proof.
- **Stale sentence.** `02-fixed-gap-sources.md` says a GitHub code search for A189281 "returned total_count=0" at the pinned commit; manuscript 03's article says the same. The pin already held manuscript 60's archive, which code search cannot read (bracketed note in Section 14.1).
- **Run time.** Manuscript 03's README promises "tens of seconds" for `verify.py --order 12`, and `data/02-fixed-gap-verification.txt` records "Completed in 22.44 seconds"; here it took 104 s to more than 170 s (above). Batch-85 manuscript 03's `data/03-rational-collapse-coefficients.json` records `elapsed_seconds` 1.166 for its delivered run; here the same run reports 12–13 s.
- **Edited text.** `article.tex` is manuscript 60's text with the label prefix, the batch-73O2 editorial note, Remarks 7.2 and 9.1, bracketed notes marked "[Added 1 October 2026, batch 73O2]", three bibliography entries (A000255, A002464, the transseries volume), Appendix B (provenance) and, in a separate reciprocal note, Remark 7.4; from the batch-74 write, the two part headings, a batch-74 editorial note, bracketed notes marked "[Added 1 October 2026, batch 74]" (after the proof of Theorem 1.1, in research questions 1 and 5, in Appendix B), Part II, two bibliography entries (the A189281 b-file and manuscript 03's pinned repository) and a table-of-contents line "Appendices"; and from the batch-85 write, two preamble macros (`\rcw`, `\Stir`), a batch-85 editorial note, bracketed notes marked "[Added 3 October 2026, batch 85]" (after Conjecture 11.1, after Proposition 11.2, in research questions 1 and 4, after Corollary 18.2, in the overlap paragraph and question 1 of Section 22, in Appendix B's "Status of the conjecture"), Part III, three paragraphs of Appendix B and five bibliography entries (A189282, A189283, A189284, batch-85 manuscript 03's b-file citation and its pinned repository). Nothing was removed. Manuscript 03's and batch-85 manuscript 03's texts are restated in Part I's notation, with some proofs condensed.
- **Overloaded letters.** Part I's C, K, d and D each carry two or more meanings in different sections (listed in Appendix B, kept). Manuscript 03 overloads D, w, T, A and B and swaps several of Part I's letters (η and θ, H_h and Q, S_k, K, d_j); Part II renames all of them into Part I's notation, as listed in its Table 4. Batch-85 manuscript 03 uses D, w_j, p, q, 𝓛, T, A, B, K, P_m, d_m, 𝓗, 𝓟 and z for objects Part I or II names otherwise; Part III renames them (σ, 𝗐_j, r−1 and s−1 written out, 𝔏, 𝒯, τ_0 and τ_1, h_n, Φ_i, ψ_i, Ψ, Φ(z,u), Part II's Λ, N, Δ), indexes components by vertices rather than edges, and lists every renaming in its Table 8; no normalization changed.

## Provenance

Appendix B of the article records all three sources, their pins, where the batch-74 and batch-85 merges had to choose and what each write changed. The placement commit `6e193dd4f` records the batch-73O2 decisions; the placement commit `b669cff87` records the batch-74 decision: manuscript 03 proves this report's main theorems in independent text, with every shared number equal, so it is added as Part II holding only its own results, with its re-derivations as marked second routes. The placement commit `713149ded` (batch 85A) records the batch-85 decision: batch-85 manuscript 03 proves this report's open Conjecture `spf:conj:collapse`, so it is an addition, Part III, with local file prefix `03-rational-collapse-`; the write gave its labels the sub-prefix `spf:rc:` (the report prefix with a sub-prefix, as the intake procedure prescribes for new material in an existing report; Part II's separate prefix `fga:` is kept unchanged).
