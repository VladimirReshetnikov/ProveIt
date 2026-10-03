# Precise Asymptotics of the Powered Catalan Numbers (OEIS A113227)

**Positive Bessel spectrum, all fixed orders, and fixed Fourier sectors**

This research report was built on 2 October 2026 from two manuscripts of
batch 77, both dated 1 October 2026. Source 57 is the foundation; source 56
is its addendum and cites it throughout. Author lines: "A proof and
reproducible research report" (57) and "A research addendum with
reproducible diagnostics" (56). No tool or person is named.

| Source | Batch-77 manuscript | Archive (main file) | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 57 | 57 | `oeis-powered-catalan-report.zip` (`powered-catalan-asymptotics.tex`, 635 lines, 14-page PDF) | none | `aa7345800` | Part I, Sections 1–10 |
| 56 | 56 | `oeis-powered-catalan-fourier-addendum.zip` (`powered-catalan-fourier-addendum.tex`, 497 lines, 10-page PDF) | none | `aa7345800` | Part II, Sections 11–17 |

Both archives arrived in commit `096ee7b87` and survive there
(`git show 096ee7b87:docs/incoming/<archive> > <scratch>/<archive>`).
Archive 56 embeds source 57's manuscript, PDF and verification record byte
for byte (as `core-report.tex`, `core-report.pdf`,
`core-mathematical-verification.md`) and six byte-identical support files.
The placement staged each file once, from archive 57. Neither manuscript
pins a ProveIt commit or names a repository path.

Both manuscripts are printed in full. Source 56 restates the inputs it takes
from source 57 (node and weight estimates, the first coefficients, the
coefficient generators); these restatements are kept, because Part II
continues them into the complex plane and cites them by its own labels, and
each now names where Part I proves the input.

**Status: AI-assisted delivery, unrefereed, not formalized.** Neither
manuscript states how it was produced; both came through the repository's
incoming channel for AI-assisted research deliveries. Source 57's
verification record is "not a proof-assistant verification or an external
peer-review certification"; source 56's is "component cross-review plus
integrated mathematical review, not formal verification or conventional peer
review". At intake the programs were rerun on copies (see "Rerunning"); the
proofs were not re-derived.

## Files

```
article.tex        the merged report, standalone LaTeX with an internal bibliography
article.pdf        the compiled report, 32 pages (title page and contents 1-2,
                   Guide 2-7, Part I 8-21, Part II 22-31, references 32)
README.md          this guide

Source 57 (Part I), from oeis-powered-catalan-report.zip
57-catalan-SOURCE_NOTES.md                  established inputs and scope of the literature check
57-catalan-VALIDATION.md                    numerical, rendering and replay record
57-catalan-mathematical-verification.md     independent mathematical review of the delivered source
code/57-catalan-residue_expansion.py        exact reciprocal-product and Stirling coefficients (alpha_l, B(z))
code/57-catalan-saddle_expansion.py         exact Gaussian-moment extraction of c_1 ... c_4
code/57-catalan-verify_coefficients.py      exact recurrence through n = 2500 against c_1, c_2
code/57-catalan-verify_spectral_moments.py  110-digit Bessel nodes and weights (65 nodes), moments through n = 30
code/57-catalan-verify_inverse.py           H_J inverse against exact targets through n = 500, J = 0, 1, 2
code/57-catalan-run_checks.sh               delivered replay driver (delivery names; do not run here)
code/57-catalan-build.sh                    delivered PDF build (builds powered-catalan-asymptotics.tex; do not run here)
data/57-catalan-residue-output.txt          output of residue_expansion.py
data/57-catalan-saddle-output.txt           output of saddle_expansion.py
data/57-catalan-saddle_coefficients.txt     c_1 ... c_4 written by saddle_expansion.py
data/57-catalan-coefficient-output.txt      output of verify_coefficients.py
data/57-catalan-coefficient_checks.json     written by verify_coefficients.py
data/57-catalan-spectral-output.txt         output of verify_spectral_moments.py
data/57-catalan-inverse-output.txt          output of verify_inverse.py
data/57-catalan-inverse_checks.json         written by verify_inverse.py
data/57-catalan-environment.txt             tested Python, mpmath, SymPy and pdfTeX versions
data/57-catalan-requirements.txt            mpmath==1.3.0, sympy==1.14.0

Source 56 (Part II), from oeis-powered-catalan-fourier-addendum.zip
56-fourier-SOURCE_NOTES.md                  sources and attribution (Paris 2016, DLMF)
56-fourier-VALIDATION.md                    numerical, document and replay record
56-fourier-mathematical-verification.md     component cross-review and integrated review
code/56-fourier-verify_fourier_sectors.py   exact-Bessel central saddle integrals, 70 digits, 160 nodes; --order 192 refinement
code/56-fourier-verify_exponential_spectral_replacement.py  exact counts at n = 80, 160, 320 vs a 180-digit lattice sum
code/56-fourier-verify_output_consistency.py  agreement of the 160- and 192-node outputs
code/56-fourier-run_checks.sh               delivered replay driver (delivery names; do not run here)
data/56-fourier-fourier-output.txt          output of verify_fourier_sectors.py
data/56-fourier-fourier_sector_diagnostics.json            written by verify_fourier_sectors.py
data/56-fourier-quadrature-refinement-output.txt           output of the --order 192 run
data/56-fourier-quadrature_refinement_diagnostics.json     written by the --order 192 run
data/56-fourier-spectral-replacement-output.txt            output of verify_exponential_spectral_replacement.py
data/56-fourier-exponential_spectral_replacement_diagnostics.json  written by the same
data/56-fourier-consistency-output.txt      output of verify_output_consistency.py
data/56-fourier-environment.txt             tested versions
```

Not shipped (all in `096ee7b87`): both delivered PDFs, both `SHA256SUMS`
ledgers, source 56's README, manuscript and `build.sh` (its text is Part II),
and the nine copies of source 57 inside archive 56 (manuscript, PDF,
verification record, `residue_expansion.py`, `saddle_expansion.py`,
`residue-output.txt`, `saddle-output.txt`, `saddle_coefficients.txt`,
`requirements.txt`). The delivered README of source 57, staged as `README.md`
by the placement commit, is replaced by this file; it survives in
`096ee7b87` and `aa7345800`. No file was excluded as heavy (largest data
file 8,549 bytes), so there is nothing to reconstruct.

## Label prefix

`pcn:` (Part I, source 57's labels) and `pcn:fs:` (Part II, source 56's
labels). Guide labels are `pcn:guide:`, Part labels `pcn:part:`. 108 labels:
59 from source 57, 32 from source 56, 17 added at the merge.

## What is claimed

- **Part I (source 57).** Every finite truncation of the known formal
  continued fraction is a probability moment transform; the limit measure is
  unique, with a_n = ∫ s^n dμ(s). The transform equals 1 − E/D with entire
  E, D; the zeros of D are positive and simple, and they carry positive
  weights (Theorem 3.1). One node λ_k = k + O(e^{−ck log k}) lies near every
  large integer, with an exact weight formula (Proposition 4.2). With
  w = W(n/e) and r = n/w,
  a_n ~ M_n ~ e^{e−2}(2π)^{−1/2} r^{−3/2} B_n(e), where B_n is the Touchard
  polynomial, and a_n = M_n(Σ_{j<J} c_j(w) r^{−j} + O_J(r^{−J})) for every fixed J,
  with explicit c_1, c_2 and an exact algorithm for every c_j (Theorem 1.1).
  A canonical continuous inverse (Theorem 7.1, two explicit corrections), and
  an entire exponential generating function with an all-orders expansion on
  the positive axis (Corollary 8.1). This answers the question of precise
  asymptotics that Elizalde left open (Adv. Appl. Math. 36 (2006), Section 7).
- **Part II (source 56).** The exact Bessel weight Q(z) = 1/(π² z b(z)²) has
  an asymptotic expansion, and b is eventually zero-free, in every closed
  wedge |arg z| ≤ θ < π/2 (Lemma 13.1). The spectral sum equals a lattice sum
  up to a relative error O(e^{−dn}) for every d < log 2 (Proposition 12.1).
  For every fixed J, a_n is the sum of the J + 1 exact cutoff-defined Fourier
  sectors I_0 + 2 Re Σ_{j≤J} I_j with error O(E_{J+1}), the next
  complex-saddle envelope; each fixed sector has an all-orders expansion with
  the same c_j, at the complex saddle w_j = W_{−j}(n/e); and
  log(E_j/M_0) = −2π²j²r/(w+1) + O_j(r/w³) (Theorem 11.1).

## What is not claimed

The union of both sources' non-claims, all printed in the report:

- no convergence of the infinite correction series; the all-orders result is
  a Poincaré expansion, "not an exponentially complete transseries";
- fixed truncation only: no growing number of sectors, no summation of
  infinitely many sector expansions, no canonical Borel sum; a fixed
  algebraic truncation of the principal sector has an error larger than every
  nonzero Fourier envelope;
- error scales without explicit constants; a numerical Newton residual
  controls only the truncated inverse equation, and a certified enclosure of
  the true inverse needs an explicit remainder bound; no exponentially
  accurate inverse; no uniform integer accuracy from a finite inverse
  expansion;
- the numerical tables are diagnostics, not interval certificates; Part II's
  quadratures integrate central saddle segments, not complete sectors;
- scoped literature checks, no worldwide priority or repository-wide
  nonduplication; the recurrence, path models and continued fraction are
  prior art (Callan 2010; Beaton, Bouvel, Guerrini and Rinaldi 2019;
  Gladkovskii in OEIS, 2012); Poisson summation, complex Gaussian expansion
  and Lambert-W saddles in Touchard asymptotics are standard (Paris 2016).

## Placement: why Part II is here and not in the transseries tree

Part II (source 56) is batch 77P2's closest case to the repository's rule
that transseries material goes to `Analysis/Transseries/`. It was kept in this
collection, beside its foundation, because it proves a finite decomposition
into a fixed number of exact cutoff-defined Fourier sectors with algebraic
expansions, and constructs no transseries, Borel sum or Stokes data; its own
scope section (Section 17) and its delivered README's "Important limitations"
say so. This choice is flagged for Vladimir: if every exponentially ordered
sector theorem should live in the transseries tree, Part II can be filed there
whole and replaced here by a cross-reference.

## Relation to other reports and to formal developments

- **[2 October 2026] Sibling report on the pattern 12-34.**
  [`../a113226-vincular-avoiders`](../a113226-vincular-avoiders) (batch 77,
  OEIS A113226) proves precise asymptotics for permutations avoiding the
  vincular pattern 12-34, a different sequence, by a closed exponential
  generating function. Both reports concern length-four vincular patterns
  whose asymptotics Elizalde studied, and both cite Callan's 1-23-4 bijection
  paper; they share no theorem or method. By the coordinator's decision at the
  write, sources 57 and 56 form their own report instead of Parts III–IV of
  the A113226 report. The article says this in the Guide ("Relation to other
  reports") and in a dated note in Part I, Section 10.
- The Touchard saddle at θ = e is the analogue of the Bell-number saddle
  (θ = 1) in [`../a277364-bell-asymptotics`](../a277364-bell-asymptotics) and
  in the transseries volume
  `Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/`
  (chapter `q2:sec:bell`, theorem `q2:thm:bell`). That volume's remark
  `q2:rem:bell-sectors` keeps the Bell numbers' nonprincipal complex saddles
  formal; Part II proves fixed sectors for A113227 only and does not settle
  that remark.
- The saddle w + log w = log(n/e) and its branches w_j are instances of the
  volume's Lambert core `p0:thm:lambert-core`; the inverse of Part I is a
  reversion as in `p0:thm:perturbed-inversion`, and its integer threshold rule
  is the separation step of `p0:thm:staircase`. No novelty is claimed for these
  mechanics.
- **Formal status.** Nothing in this report is formalized in Lean or Rocq, and
  its location confers no formal status. The only related formal statement is
  generic: the separation inequality of `p0:thm:staircase`, formalized as
  `staircase_separation` in
  `Analysis/FabiusFunction/Lean/FabiusFunction/StaircaseInversion.lean`.

## Building

From this directory, in a scratch copy (the repository keeps no auxiliary
files):

```
mkdir <scratch>/pcn && cp article.tex <scratch>/pcn/ && cd <scratch>/pcn
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

pdfLaTeX with amsmath, amssymb, amsthm, lmodern, microtype, hyperref,
booktabs, enumitem, longtable and array. The build of 2 October 2026 (MiKTeX)
had no errors, no undefined references or citations, no multiply defined
labels or duplicate destinations, and no overfull boxes. The log repeats
pdfTeX notices "fontmap entry ... already exists, duplicates ignored"; they come
from the `\pdfmapfile` lines both delivered sources carry and are harmless.

## Rerunning

Run the programs on a copy, never in this directory: they write their
outputs into the working directory or beside the script, under delivery
names, and the shipped `*-run_checks.sh` and `57-catalan-build.sh` use
delivery names (`powered-catalan-asymptotics.tex`, `residue_expansion.py`, …)
and rebuild a PDF. Requirements: Python 3 with mpmath 1.3.0 and SymPy 1.14.0
(`data/57-catalan-requirements.txt`; use `py` on this machine).

```
R=<this directory>; mkdir <scratch>/pcn-run && cd <scratch>/pcn-run
for f in residue_expansion saddle_expansion verify_coefficients verify_spectral_moments verify_inverse; do
  cp "$R/code/57-catalan-$f.py" "$f.py"; done
for f in verify_fourier_sectors verify_exponential_spectral_replacement verify_output_consistency; do
  cp "$R/code/56-fourier-$f.py" "$f.py"; done
py residue_expansion.py > residue-output.txt
py saddle_expansion.py > saddle-output.txt              # also writes saddle_coefficients.txt
py verify_coefficients.py > coefficient-output.txt      # also writes coefficient_checks.json
py verify_spectral_moments.py > spectral-output.txt
py verify_inverse.py > inverse-output.txt               # also writes inverse_checks.json
py verify_fourier_sectors.py > fourier-output.txt       # also writes fourier_sector_diagnostics.json
py verify_fourier_sectors.py --order 192 --output quadrature_refinement_diagnostics.json > quadrature-refinement-output.txt
py verify_exponential_spectral_replacement.py > spectral-replacement-output.txt
py verify_output_consistency.py > consistency-output.txt
```

Each output corresponds to `data/57-catalan-<name>` or `data/56-fourier-<name>`
of the same name. Compare modulo CR: on Windows the redirected outputs end
lines with CRLF, the shipped ones with LF (for example
`diff --strip-trailing-cr`). Source 56's replay also runs
`residue_expansion.py` and `saddle_expansion.py`; its copies were
byte-identical to source 57's, which is why only those are shipped.

At intake (2 October 2026, on copies, machine heavily loaded) every program
of source 57 reproduced its outputs modulo CRLF (residue 19 s, saddle 30 s,
coefficients 41 s, spectral moments 14 s, inverse 2 s), as did source 56's
`verify_fourier_sectors.py` (91 s) and
`verify_exponential_spectral_replacement.py` (104 s). The `--order 192`
refinement and `verify_output_consistency.py`, which reads its output, were
not rerun. No delivered PDF was rebuilt.

## Delivered files that use delivery names

The shipped records are byte-identical to the deliveries and therefore speak
of the delivered packages:

- `57-catalan-VALIDATION.md` and `57-catalan-mathematical-verification.md`
  name `powered-catalan-asymptotics.tex` (SHA-256 `2feb8e8d…`) and
  `powered-catalan-asymptotics.pdf` (`f3f0c49f…`). That source is the text of
  Part I (and was `article.tex` at the placement commit `aa7345800`); the PDF
  is not shipped. They also mention the release manifest and a fresh-directory
  replay of the delivered package.
- `56-fourier-mathematical-verification.md` names
  `powered-catalan-fourier-addendum.tex` (SHA-256 `801866ee…`), the text of
  Part II.
- `56-fourier-SOURCE_NOTES.md` and `56-fourier-VALIDATION.md` name
  `core-report.pdf`, `core-report.tex` and `core-mathematical-verification.md`
  (source 57's manuscript, PDF and `57-catalan-mathematical-verification.md`,
  byte for byte), `run_checks.sh`, `build.sh`, a "27-file pre-replay
  baseline" and a "frozen ZIP"; these describe archive 56.
- `code/57-catalan-run_checks.sh` and `code/56-fourier-run_checks.sh` call
  unprefixed script names and `build.sh`; `code/57-catalan-build.sh` builds
  `powered-catalan-asymptotics.tex`, which is not shipped under that name.
- Sentences in the Parts about "the reproducibility package", "the
  reproducibility archive" or "the accompanying output" describe the delivered
  archives; dated notes in Sections 9 and 17 say what is shipped.

## Changes made at the merge

- Labels prefixed (`pcn:`, `pcn:fs:`); four section labels added in Part I and
  one in Part II.
- Sections numbered through the report (source 56's Section k is Section
  k + 10); equations numbered through the report.
- Source 56's four `\cite{Core}` and two further mentions of "the companion
  report" / "the audited spectrum" are references to Part I; its bibliography
  entry `Core`, which described `core-report.pdf` and `core-report.tex` as
  included, is dropped; the two DLMF entries are merged.
- Three symbols of source 56 renamed to avoid collisions with Part I:
  β_m (coefficients of 𝓑) → 𝓑_m; the Bernoulli numbers B_{2q} → β_{2q}
  (Part I's notation); the Schläfli remainder E(z) → E_S(z). No normalization
  changed. A notation table in the Guide lists these and the remaining shared
  letters with their false readings (for example Part I's w_0 of the inverse
  versus Part II's w_0 = W_0(n/e); Part II's J counts sectors, not orders).
- Seven dated `[write, 2 October 2026]` notes: the Guide's sibling-report note,
  Part I §1 (pointer to Part II), §9 (shipped files), §10 (the A113226 and
  Bell-number neighbours; question 2 partly answered by Part II and re-scoped),
  Part II §17 (the transseries volume's Bell remark; shipped files and intake
  replay).
