# An Exact Gamma Constant for an Apéry-like Sequence

**A279619: two independent proofs of C = √(3π)/(Γ(1/7)Γ(2/7)Γ(4/7)), all-orders asymptotics, a second exact sum at 1/125, and a recessive companion**

This research report is dated 1 October 2026. It was built from two manuscripts of batch 73O2 of ProveIt's incoming-reports intake, written independently on the same day and proving the same theorem by different routes. Author lines: "Research report prepared for Vladimir Reshetnikov" (58) and "A mathematical analysis prepared for Vladimir Reshetnikov" (56).

| Source | Batch-73O2 manuscript | Archive | Pin | Arrived | Placed | Printed as |
|---|---|---|---|---|---|---|
| base | 58 | `A279619_Gamma_Asymptotics.zip` (*An exact gamma constant for an Apéry-like sequence*, 22-page PDF) | `a5ad4ac2e` | `aa43cc555` | `6e193dd4f` | Sections 1, 3–5, 7–12, 13.1–13.12, 14.2, Appendix A, C.1, and the companion, convolution and rounding theorems |
| member | 56 | `A279619_exact_asymptotics.zip` (*Exact asymptotics of OEIS A279619*, 15-page PDF) | none (cites no revision) | `58dbe2cd3` | `6e193dd4f` | Section 6 (second proof), Theorem 2.2 (sum at 1/125), Corollaries 2.3–2.5, the integer Frobenius recurrence and c₆…c₁₀ in Section 7, Remark 11.1, Section 12.4, Section 13.13, Section 14.1, Appendices B and C.2 |

The pin `a5ad4ac2e2d4e642a6c015836a70492d40fcbc71` is the repository snapshot manuscript 58 inspected (12:35 PDT). It predates the arrival of manuscript 56 (`58dbe2cd3`, 12:56 PDT); manuscript 56 cites no revision. Neither saw the other. The placement commit `6e193dd4f` deleted both archives from `docs/incoming`; they survive in their arrival commits.

The two manuscripts prove the same leading constant, the same boundary value Σ aₙ/27ⁿ = 3Γ(1/7)Γ(2/7)Γ(4/7)/(8π²), and the same rational corrections (equal as rationals through order 10, the last order 56 prints; 58 records them to order 12). Their proofs differ:

- **58**: a rational pullback of the generating function to ₂F₁(1/12,5/12;1), Ramanujan's level-seven 1/π series (Hemmecke–Paule–Radu, Eq. 98) and the singular elliptic period K(k₇).
- **56**: the boundary value is the eta product 3η(i/√7)η(i√7) at the Fricke fixed point (O'Brien's modular parametrization), evaluated by the Chowla–Selberg formula at discriminant −7 and a Weber-function step; the singular coefficient is then read off from Hirschhorn's constant for the square sequence A183204, whose leading term 56 re-derives by Laplace's method.

The report prints the result once, with 58's proof as the main text and 56's as a marked second proof (Section 6). Two independent derivations arriving on the same day are mild corroboration, not a substitute for review.

**Status: AI-assisted, unrefereed, not formalized.** The intake checked selected constants and identities independently (Section "Checks made at intake" below) and reran both shipped scripts on copies. It did not re-derive every proof. The two non-elementary special values of 58's proof, and the Chowla–Selberg formula and the functional equation used by 56, are cited classical inputs.

## Files

```
README.md                                   this guide
article.tex                                 the report (LaTeX, internal bibliography)
article.pdf                                 the compiled report, 38 pages (unnumbered title page,
                                            contents pages 1-3, then pages 4-37)
58-gamma-SOURCE_AUDIT.md                    manuscript 58's source and contribution audit, as delivered
code/58-gamma-verify.py                     58: rational certificates, coefficient recurrences to order 12,
                                            Wronskians, A183204 checks, rational enclosures of C and L, tables
code/56-exact-verify_a279619.py             56: exact terms, c_j and v_j by exact recurrences, high-precision
                                            constants, its two tables (stdout only)
data/58-gamma-verification.json             58: coefficients c_j, d_j, ell_j to order 12, eight zero certificates,
                                            rational bounds and 100-digit enclosures of C and L
data/58-gamma-dominant_errors.csv           58: signed relative errors of the dominant expansion (CRLF, as delivered)
data/58-gamma-minimal_errors.csv            58: signed normalized errors of the recessive expansion (CRLF)
data/58-gamma-inverse_errors.csv            58: continuous inverse errors at exact a(n) (CRLF)
data/58-gamma-run_log.txt                   58: standard output of its verification run
data/58-gamma-pdf_validation.json           58: validation record of its delivered 22-page PDF (not shipped)
data/58-gamma-requirements.txt              sympy==1.14.0, mpmath==1.3.0
data/56-exact-verification.txt              56: standard output of verify_a279619.py --max-n 5000
data/56-exact-OEIS_update.txt               56: plain-text OEIS proposal (unsubmitted; see "Disclosures")
```

Every file except `article.tex`, `article.pdf` and this README is byte-identical to the delivery. The three CSVs are CRLF as delivered and are protected by `-text` lines in `SetTheory/Cardinals/.gitattributes`. Manuscript 56 shipped no requirements file; its script needs SymPy and mpmath, which `data/58-gamma-requirements.txt` pins.

## Structure, labels and numbering

- **Section 1**: 58's scope section; Section 1.3 says what each source contributes, and Section 1.4 (Table 1) is the notation dictionary.
- **Section 2**: the principal results: Theorem 2.1 (proved in both sources), Theorem 2.2 (56: the sums at 1/27 and 1/125), Corollaries 2.3–2.5 (56: ratio to n⁻⁴ with eventual log-convexity, root scale, critical tail), Theorem 2.6 (58: the recessive companion).
- **Sections 3–5**: 58's analytic setting, rational certificate and first proof of the constant.
- **Section 6**: 56's second proof: the square identity, the modular parametrization, the Laplace derivation of the A183204 constant, the CM evaluation, the functional equation and the sum at 1/125, and the singular coefficient.
- **Sections 7–12**: 58's all-orders expansion (with 56's Frobenius recurrence and c₆…c₁₀), continued fraction, recessive scale, convolution powers, inversion and rounding, and computations (with 56's tables in Section 12.4).
- **Section 13**: research questions: 58's twelve (13.1–13.12) and 56's ten (13.13, R1–R10), each of 56's marked where it meets 58's.
- **Section 14**: 56's novelty audit and 58's roadmap and conclusion. **Section 15**: provenance. **Appendices**: A (58's period normalization), B (56's two derivations), C (both OEIS proposals).

Every label carries the prefix `l7g:`; manuscript 56's own labels carry the sub-prefix `l7g:cm:`. The staged base (58's `article.tex`) had **69** labels; all 69 are kept with the prefix. The report has **153** labels: 69 from 58, 52 of manuscript 56's 71, and 32 added by the merge (sections, the notation table). The 19 labels of 56 not kept named items printed once in 58's wording: the recurrence, the definitions, the main theorem with its constant and coefficients, the critical sum, the differential equation in two variables, the singularity list, the local form, the Frobenius series, the transfer formula, the formal identity, the inverse formula and its envelope, and the all-orders section. Text added in the merge is marked "[Merge note, batch 73O2: …]".

## What is claimed

- **Theorem 2.1.** C = √(3π)/𝒢₇ with 𝒢₇ = Γ(1/7)Γ(2/7)Γ(4/7); A(1/27) = 3𝒢₇/(8π²) and C·A(1/27) = 3√3/(8π^(3/2)); for every fixed M, aₙ = C·27ⁿn^(−3/2)(Σ_{j≤M} c_j n^(−j) + O(n^(−M−1))) with rational c_j, the first being −215/1008, −1265/290304, 4683055/877879296, …. Two proofs.
- **Theorem 2.2 (56).** Σ aₙ/125ⁿ = 5𝒢₇/(16π²), from the boundary value and the functional equation (A(y/(1+4y)³)/(1+4y) = A(y²/(1+2y)³)/(1+2y)) at y = 1/8.
- **Corollaries (56).** aₙ₊₁/aₙ = 27(1 − 3/(2n) + 2105/(1008n²) − 18815/(7056n³) + 3425255/(1053696n⁴) + O(n⁻⁵)), eventual strict log-convexity, the root scale, and the critical tail A(1/27) − Σ_{n≤N} aₙ/27ⁿ = C(2ν^(−1/2) + (541/1512)ν^(−3/2) + (2411/145152)ν^(−5/2) + O(ν^(−7/2))), ν = N+1.
- **Theorem 2.6 (58).** The companion b₀ = 0, b₁ = 1 gives L = lim bₙ/aₙ = 0.4672117688…, exact alternating rational brackets, the Wronskian Wₙ = (−1)ⁿ(3n)!/(n!(n+1)!²), the continued fraction 1/(2+6/(41+240/(132+…))), and eₙ = bₙ − Laₙ ~ (−1)^(n+1)(√3/(56πC))n^(−3/2)(1 + d₁/n + …) with rational d_j to every order.
- **Theorem 10.1 (58).** Convolution powers [zⁿ]A(z)^m ~ mA⋆^(m−1)C·27ⁿn^(−3/2)(1 + c₁^⟨m⟩/n + …), coefficients in ℚ(πC²/A⋆²); the case m = 2 recovers the known A183204 constant (not new).
- **Section 11.** The Lambert-W₋₁ inverse with triangular corrections q_j ∈ ℚ(log 27), and Proposition 11.2 (58): rounding brackets ⌈x_M − K_M x_M^(−M−1)⌉ ≤ N(Y) ≤ ⌈x_M + K_M x_M^(−M−1)⌉ with existential constants.
- A rational enclosure of C of width 10⁻¹⁰⁰ and of L by b₉₀/a₉₀ < L < b₉₁/a₉₁ (58).

## What is not claimed

- **Priority.** The first three corrections are O'Brien's (2016 thesis, §8.4), the hypergeometric generating function is Kotěšovec's (OEIS, 2018), and the A183204 asymptotic is Hirschhorn's. Both manuscripts' novelty audits are targeted, not exhaustive; neither claims global priority for the constant.
- **No novelty for the inverse.** The Lambert-W inverse and its corrections are the instance a = log 27, β = −3/2 of Theorem `t2:thm:balanced-inverse` of the volume *Combinatorial Transseries and Their Inverses* (`Analysis/Transseries/docs/series-and-transseries/Combinatorial_Transseries_Inverses/`); 58's q₁, q₂ are that theorem's d₁, d₂. Neither manuscript cites it. The rounding proposition has the form of the separation condition of `p0:thm:staircase` in the canonical volume (`Transseries_And_Inversion/`).
- **Not established:** the Lucas-congruence conjecture of the OEIS entry; a closed form for L; irrationality of L or an irrationality measure; a canonical exponentially improved (Borel-summed) expansion of aₙ; convergence of the series in 1/n; explicit remainder constants K_M, N_M, Y_M; a uniform rounding rule N(Y) = ⌈x_M(Y)⌉; global log-convexity; a direct single modular proof of C·A⋆.
- 56's statement that W₋₁ "rounded and corrected by one or two exact recurrence evaluations, gives an efficient certified locator" is a recipe, not a theorem: certification needs the explicit constants neither source supplies (merge note in Remark 11.1).
- The two-scale statement concerns a specified exact recurrence basis, not a generic solution.
- Nothing is Lean-certified; the Python programs check algebra and supply interval certificates and diagnostics.

## Relation to neighbouring material

- **Transseries volumes** (`Analysis/Transseries/docs/series-and-transseries/`): the inverse of Section 11 instantiates `t2:thm:balanced-inverse` (cited, not reproved as new). The same volume's Motzkin two-endpoint section (`ct:sec:motzkin`) treats a 3ⁿ/(−1)ⁿ two-root structure through a moment integral and warns against adding a lower-endpoint sector merely because a recurrence has a second characteristic root; 58 respects that warning by constructing a separate exact companion instead.
- **Apéry-number reports** in this collection: [`apery-array-zeta-accelerations`](../../apery-array-zeta-accelerations/) uses discrete Wronskians (Casoratians) for a different sequence; `hankel-determinants/growth-and-runs/apery-hankel-determinant-growth` and `congruences-and-valuations/supercongruences/a267220-apery-transform-supercongruences` concern the classical Apéry numbers, not A279619. None mentions A279619, A183204 or Γ(1/7).
- **Lean.** Placement in this collection confers no formal status. Nothing in this report is formalized. The only related formal statements in the repository are the generic staircase lemmas `Fabius.staircase_separation` and `Fabius.staircase_separation_fails` (`Analysis/FabiusFunction/Lean/FabiusFunction/StaircaseInversion.lean`), which formalize the separation condition `p0:eq:separation` for real numbers in general; they do not verify Proposition 11.2 or any statement about A279619.

## Checks made at intake

On copies, with exact arithmetic where possible: the recurrence to n = 6000; both binomial forms of A183204 against [zⁿ]A² for n ≤ 40; 58's and 56's Frobenius recurrences equal for j ≤ 9 (12 by the dossier's helper); c₀…c₈ by a third route (Bernoulli-polynomial gamma-ratio expansion), all equal; C from 58's hypergeometric formula (which does not involve 𝒢₇) against √(3π)/𝒢₇ at 60 digits; F(1/125) by direct summation, difference 3·10⁻⁶¹; the functional equation as a power series through y²⁴; the tail coefficients 541/1512 and 2411/145152 by Euler–Maclaurin; the Wronskian closed form for k < 60; the continued-fraction coefficients; the A183204 coefficient −65/144 from both sources.

## Building

From a scratch copy of this directory, run

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

pdfLaTeX (MiKTeX) produced the shipped `article.pdf`: 38 pages, no errors, no undefined references or citations, no multiply defined labels, no duplicate destinations, no overfull or underfull boxes. No Python run is needed; the tables are in the TeX source. Copy back only `article.pdf`.

## Rerunning the scripts

Run on a copy with the **delivered** layout. `code/58-gamma-verify.py` writes `dominant_errors.csv`, `minimal_errors.csv`, `inverse_errors.csv` and `verification.json` into `../data/` relative to itself, under the delivered (unprefixed) names; run in place it would not overwrite the shipped `58-gamma-` files but would leave four unprefixed files in `data/`. `code/56-exact-verify_a279619.py` writes only to standard output.

```sh
R=SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a279619-level-seven-gamma-constant
W=$(mktemp -d); mkdir -p "$W/code" "$W/data"
cp "$R/code/58-gamma-verify.py" "$W/code/verify.py"
cp "$R/code/56-exact-verify_a279619.py" "$W/verify_a279619.py"
cd "$W"
uv run --no-project --with sympy==1.14.0 --with mpmath==1.3.0 python code/verify.py          # about 45 s
uv run --no-project --with sympy==1.14.0 --with mpmath==1.3.0 python verify_a279619.py --max-n 5000 > verification.txt   # about 80 s
```

Compare `data/*.csv` with `data/58-gamma-*.csv` (byte-identical at intake: Python's `csv` module writes CRLF on every platform), `data/verification.json` with `data/58-gamma-verification.json` (equal apart from line endings on Windows, where `write_text` writes CRLF), the standard output of the first run with `data/58-gamma-run_log.txt` (equal except the output-path line), and `verification.txt` with `data/56-exact-verification.txt` (equal apart from line endings). Do not run Python with `-O`: 58's tests are assertions.

## Disclosures and discrepancies

- **Not shipped:** both delivered PDFs, manuscript 56's `A279619_exact_asymptotics.tex` and `README.md`, manuscript 58's delivered `README.md` (replaced by this guide) and its `SHA256SUMS.txt` (verified 12/12 at placement and retired).
- **Delivery names in shipped text.** `58-gamma-SOURCE_AUDIT.md` refers to the report and its files under delivered names. `data/58-gamma-pdf_validation.json` describes manuscript 58's delivered 22-page PDF, not the shipped `article.pdf`. `data/58-gamma-run_log.txt`, line 5, reads `Files written to /mnt/data/A279619_research/data`, a path in the delivery sandbox. In `article.tex`, manuscript 58's references to `README.md`, `SOURCE_AUDIT.md` and `data/verification.json` were changed to the shipped names (marked by a merge note).
- **Missing credit in a shipped file.** `data/56-exact-OEIS_update.txt` (and 56's printed proposal) give the first three corrections −215/1008, −1265/290304, 4683055/877879296 without saying that they were calculated formally by O'Brien (2016 thesis, §8.4). The file is kept byte-identical; Appendix C.2 adds the credit, and any submission must too. 58's proposal (Appendix C.1) credits O'Brien.
- **Functional equation.** 58's source audit calls a functional identity "added in August 2026" to the OEIS entry "a possible future input, not a dependency"; 56 uses the functional equation, which it attributes to O'Brien's modular equation, to prove the sum at 1/125. The report states its provenance once (merge note in Section 6.6). The sum at 1/125 depends on it; Theorem 2.1 does not.
- **Transfer step.** 56's text justifies the coefficient transfer only by "the next finite singularity is at x = −1". The report uses 58's dented-disk continuation for both proofs and keeps 56's sentence in a merge note (Section 7.2).
- **Notation.** 56's symbols were rewritten in 58's (Table 1): its sequence cₙ is aₙ, its generating function F is A, its corrections α_j are c_j, its Frobenius coefficients b_m are v_m, its log 27 (L) is λ, its entropy H is Ent, its Laplace variable a and weight g are ξ and κ, its Qₙ is Rₙ, its tail S_N and q are Σ_N and ν, its Weber value u is 𝔲. No normalization changed.
- **Bibliography.** Merged. Five entries manuscript 56 listed but never cited (Cooper, Cox, Apostol, DLMF, Flajolet–Sedgewick) are now cited where used. Two repository entries (the two transseries volumes) were added in the merge.
- **Hard-coded section numbers** in 58's text ("Section 3/5/6/8") are now references.
