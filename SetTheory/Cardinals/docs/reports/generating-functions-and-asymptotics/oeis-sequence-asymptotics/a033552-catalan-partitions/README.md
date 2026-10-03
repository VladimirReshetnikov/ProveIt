# Partitions into Catalan Numbers

**All-orders asymptotics, periodic corrections, and inverse growth for OEIS A033552**

This research report is dated 1 October 2026. It was built from one manuscript, number 39 of batch 73O1 of ProveIt's incoming-reports intake. Its title-page author line, kept as delivered, is "A proof-focused research report for the ProveIt project"; the delivered PDF metadata named the author "Research report prepared with ChatGPT".

| Source | Batch-73O1 manuscript | Archive | Pin | Arrived | Placed | Printed as |
|---|---|---|---|---|---|---|
| sole | 39 | `Catalan_Partitions_Research.zip` (*Partitions into Catalan Numbers: All-Orders Asymptotics, Periodic Corrections, and Inverse Growth*, 21-page PDF, 17 files) | `e6190a945` | `f8c3a392a` | `9df4ba51a` | the whole report; Appendix C added in the write |

The pin `e6190a94552f119e9a2140e5fea8450a045a0837` is the ProveIt commit at which the manuscript rechecked the two transseries READMEs it cites (2026-10-01, "Record batch 72 in the incoming README's worked examples"). The delivered `SOURCE_NOTES.md` also names `1f1981f682b2878bde51a6ad40c22777f362fc05`, which its first repository request returned, and calls it "a tree SHA, not a commit SHA". That is wrong: `1f1981f68` is a commit (2026-10-01 09:15, the pin of manuscripts 38 and 40 of the same batch); the root tree of `e6190a945` is the separate object `8e77886c`. The placement commit `9df4ba51a` deleted the archive from `docs/incoming`; it survives in the arrival commit `f8c3a392a`.

**Status: AI-assisted, unrefereed, not formalized.** The intake recomputed A033552 by its own dynamic program through n = 10^6, evaluated the explicit expansion with the lattice form of the phase (not the authors' Fourier code) and reproduced the delivered error columns, and reran both scripts on a copy. It did not re-derive every proof.

## Files

```
README.md                          this guide (replaces the delivered README)
article.tex                        the report (LaTeX, internal bibliography)
article.pdf                        the compiled report, 23 pages
SOURCE_NOTES.md                    the manuscript's source and repository audit, as delivered
code/catalan_partitions.py         exact coefficients, cumulants, phase and asymptotic formulas (mpmath)
code/verify.py                     exact-integer cross-checks, phase cross-checks, coefficient, inverse and
                                   largest-index tables; writes the data files below
code/symbolic_audit.py             exact SymPy audit of the normalization and first-correction algebra
code/build.sh                      the delivered three-pass pdflatex script (fails as shipped; see below)
data/verification.json             recorded run: environment, five check lines, constants, tables
data/coefficient_errors.csv        relative errors of the saddle and explicit expansions, n = 10^2 ... 10^6
data/inverse_errors.csv            relative errors of the leading and corrected inverse
data/largest_index.csv             exact and limiting distribution of the largest part index at n = 10^6
data/a033552_0_300.txt             p(0), ..., p(300)
data/symbolic_audit.json           recorded symbolic audit
data/build_and_quality_checks.json the delivered PDF's build record (21 pages)
data/requirements.txt              mpmath==1.3.0, sympy==1.14.0
```

Every file except `README.md`, `article.tex` and `article.pdf` is byte-identical to the delivery. Delivery names: `build.sh` and `requirements.txt` were at the package root and are now in `code/` and `data/`; everything else kept its place. Not shipped: the delivered `article.pdf` (replaced by a build of this text) and the checksum ledger `SHA256SUMS.txt` (verified 16/16 at intake, then retired). The three CSV files are CRLF as delivered and are kept so by `-text` lines in `SetTheory/Cardinals/.gitattributes`.

## Labels and numbering

Every label carries the prefix `ctp:`. The 93 delivered labels keep their names after the prefix, and the write added one (`ctp:app:edition`): **94** labels. (The batch dossier counted 94 delivered labels; the 94th match of its search was the word "label" in a sentence of Section 10.8.) No section, statement, equation or table number changed. The write also added cleveref type hints (`\label[lemma]`, `\label[corollary]`, `\label[proposition]`) to the five labels of lemmas, corollaries and propositions, and `\crefalias{section}{appendix}` after `\appendix`: these environments share the theorem counter, and the delivered PDF printed every reference to them as "theorem". Only those printed names changed.

Text added in the write is marked *[Write note, batch 73O1, 1 October 2026.]*: after the principal-formula box, in Sections 1.2 (de Bruijn) and 1.3 (repository status, the pin), after the proof of Lemma 4.1 (the Fabius-tree relative), in Section 9.4 (rerun hazards) and Appendix C (provenance). Two bibliography entries are marked "[Added in the write.]", and the PDF author field was replaced as described in Appendix C. No delivered sentence, statement, proof or table was changed or removed.

## What is claimed

Let p(n) count partitions of n into the distinct Catalan numbers 1, 2, 5, 14, 42, … (A033552; the unit part counted once). Put α = log 4 and let μ be the large solution of n = 4^μ/√(πμ).

- **Explicit expansion** (Theorem 2.1): log p(n) = (α/2)μ² − ((1 + 3α)/2)μ + (23/8) log μ + C + Ψ_α(μ) + D_α(μ)/μ + O(μ^{−2}), with C = (1/4) log 2 + (3/4) log π + log G(3/2), a smooth nonconstant one-periodic phase Ψ_α given by a Fourier series in Γ(2πiℓ/α) ζ(1 + 2πiℓ/α), and an explicit periodic first correction D_α. Every further inverse-power coefficient is constructively determined (Sections 4.4 and 5.3).
- **No constant asymptotic** (Corollary 2.2): replacing Ψ_α by a constant does not give an asymptotic equivalent. Corollary 2.3 gives the first three logarithmic growth terms.
- **Inverse growth** (Theorem 2.4): the threshold at which p(n) reaches y, with leading term 8√(eα/π) exp(√(2α log y))/(2α log y)^{1/4} and its first correction; Section 6 separates the continuous inverse from the integer staircase.
- **All-orders saddle estimate** (Lemma 3.1, Theorem 3.2) with a contour proof for the noncentral arcs, under a reusable sufficient hypothesis (Section 3.4); the Barnes product, the lattice and Fourier forms of the phase (Lemma 4.1) and the moving-lattice expansion (Theorem 4.2).
- **Largest part** (Theorem 7.1): a phase-dependent limit law for the largest Catalan-part index of a uniform random partition, ∏_{j>h}(1 − exp(−4^{j−θ})); it is a discrete law, not a Gumbel law.
- **Universality** (Proposition 8.1): which coefficients depend only on the exponential and polynomial growth of the allowed part sizes.

The OEIS entry (as inspected on 1 October 2026) gives a generating function, a recursion and Pak's survey, and **states no asymptotic conjecture**. The report therefore answers no posed question; it supplies the asymptotics the entry lacks.

## What is not claimed

These are the manuscript's own limits (delivered README "Scope and status", `SOURCE_NOTES.md`, article Sections 1.2, 9 and Appendix B), kept in full:

- No exhaustive literature-priority search; no MathSciNet, zbMATH or journal-archive search. The absence of a posted OEIS asymptotic is an entry-level gap, not evidence that no general theorem implies a leading term. Periodicity in geometrically restricted partitions is classical (de Bruijn, Erdős–Richmond, Flajolet–Gourdon–Dumas); the saddle and periodic-partition methods are not claimed new, only the sequence-specific formulas and their proofs.
- No resolution of Pak's question on the exact counting complexity of A033552.
- No beyond-all-orders (exponentially small) contributions, no interval certificates: the floating-point checks corroborate and do not replace the proofs.
- The largest-index law is for fixed h only; no growing-h or moment theorem is asserted (Theorem 7.1).
- The numerical program implements the Gaussian corrections E₁ and E₂ directly and lists E₁ … E₄ in the recorded data; the all-orders theorem does not rest on an unlimited symbolic implementation being supplied (Section 9.1).
- No Lean formalization. Section 10.8 warns that the contour proof must not be called formalized merely because some algebraic operations have Lean counterparts.
- The numbers show the slow convergence plainly: at n = 10^6 the asymptotic parameter is about 1/11; the relative error after the second saddle correction is 4.66 × 10^−5, the explicit first-correction formula's is −1.06 × 10^−2, and the corrected inverse's at y = p(10^6) is 2.91 × 10^−2 (`data/coefficient_errors.csv`, `data/inverse_errors.csv`).

## Relation to neighbouring material

- **No host.** No repository report or formal development treats A033552 or partitions into Catalan numbers (checked at placement and again at this write). The manuscript cites the transseries READMEs (`Analysis/Transseries/README.md`, `Analysis/Transseries/docs/series-and-transseries/README.md`) only for their separation of continuous and integer inverses and of formalized and unformalized results; it imports no repository theorem.
- **Fabius tree.** Lemma 4.1's Mellin computation reappears for a different product in `Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/frontier-compilations/Geometric_Uniform_Convolutions_and_New_Frontiers/fabius-frontier-report-H.tex`, section "Mellin analysis and the hidden log-periodic phase": the kernel log((1 − e^{−x})/x) with Mellin transform −Γ(1 + s)ζ(1 + s)/s and the constant c₁ = π²/12 − γ²/2 − γ₁, which is this report's κ. Neither text proves the other's theorem; both are instances of the de Bruijn–Mahler mechanism, and de Bruijn's 1948 paper, cited there, was added to this report's bibliography in the write.
- **Sibling partition reports of batch 73O1** in this directory: [`a097356-sqrt-restricted-partitions`](../a097356-sqrt-restricted-partitions/) (parts at most ⌊√N⌋) and [`a022629-distinct-partition-norms`](../a022629-distinct-partition-norms/) (∏(1 + k^α q^k)). Different products in different saddle regimes; they share the standard toolkit (exact saddle with an all-orders Edgeworth expansion, noncentral-arc control, Lambert-W inversion with integer staircases), and no proposition is proved in two of them.
- **Radix-layer partitions (batch 77).** [`a174065-radix-layer-partitions`](../a174065-radix-layer-partitions/) shows that the OEIS equivalents of A174065 and A393565 (`∏(1 + z^(i b^j))`) omit a nonconstant log-periodic factor, by the same Mellin pole-lattice mechanism for a different product; no theorem is shared.
- **Lean.** Placement in the collection confers no formal status, and none of this report's statements is formalized.

## Building

From a scratch copy of this directory, run

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The article needs no external figures or bibliography files (newtx, tcolorbox, titlesec, hyperref and cleveref). pdfLaTeX (MiKTeX 26.2) produced the shipped `article.pdf`: 23 pages, with no errors, no warnings, no undefined references or citations, no multiply defined labels, no duplicate destinations, and no overfull or underfull boxes. Copy back only `article.pdf`. Do not use `code/build.sh`: it changes into `code/`, where there is no `article.tex`, and stops with an error.

## Rerunning the scripts

Both scripts write into the `data/` directory **beside `code/`**, that is into the shipped data, when run in place: `verify.py` by default (pass `--output` to change it), `symbolic_audit.py` always (it has no option). So rerun on a copy:

```sh
R=SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a033552-catalan-partitions
W=$(mktemp -d)
cp -r "$R"/code "$R"/data "$W"/ && cd "$W"
uv run --no-project --with mpmath==1.3.0 python code/verify.py --max-n 1000000 --dps 60   # about 23 s; rewrites $W/data
uv run --no-project --with sympy==1.14.0 python code/symbolic_audit.py                   # about 22 s; rewrites $W/data/symbolic_audit.json
```

The million-term run stores a million Python integers; `--max-n 10000` gives a smaller diagnostic run that writes only the applicable rows. At intake (Windows, Python 3.13.5, mpmath 1.3.0, SymPy 1.14.0) the three CSV files were byte-identical to the shipped ones; `a033552_0_300.txt` and `symbolic_audit.json` were equal apart from CRLF line ends (Windows text mode); `verification.json` was equal apart from line ends and its `python` and `platform` strings.

## Disclosures and discrepancies

- The delivered README is not shipped; this guide replaces it. Its commands (`python -m pip install -r requirements.txt`, `python code/verify.py …`, two `pdflatex` passes) assume the delivered layout, with `requirements.txt` and `build.sh` at the root.
- `data/build_and_quality_checks.json` describes the delivered 21-page PDF, which is not shipped.
- `SOURCE_NOTES.md` mislabels the commit `1f1981f68` as a tree (above), and refers to `data/verification.json` and `data/symbolic_audit.json` by their (unchanged) paths.
- The article's Section 9.4 gives the delivered commands ("From the package directory"); a write note there explains the rerun hazards.
- The delivered bibliography omitted de Bruijn's paper on Mahler's partition problem, the origin of the phenomenon Section 1.2 attributes to Erdős–Richmond's discussion; it is added and marked.

## Provenance

Appendix C of the article records the source, the pin, what the write changed and the map from delivery names to shipped paths; the delivered Appendix B records the manuscript's own search scope. The placement commit `9df4ba51a` records the batch decisions: no repository report treats A033552, and the batch's three partition manuscripts stay in separate reports because they study different products and prove no common proposition.
