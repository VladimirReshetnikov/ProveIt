# Many-Color Rooted Trees and Their Symmetries (OEIS A242249, A255517, A242375, A255523)

**Uniform asymptotics, Poisson laws, and exact inverses for rooted trees
with `q` colors on the non-root vertices, uniformly for `q ≥ 40`; with
Kotěšovec's growth-base conjectures in A242249 and A255517 proved.**

A single-source report: bundle Report 222 of one external research session
(the session bundle of Reports 1–243, arrival commit `60f54ea06`), placed by
`f79c9bef1` (batch 112) and written on 7 October 2026. The author line and
the PDF author field read "Report 222"; the manuscript names no person, tool
or addressee.

| Source | Archive | Placed | Shipped as |
|---|---|---|---|
| *Many color rooted trees and their symmetries: Uniform asymptotics, Poisson laws, and exact inverses* ("Report 222", 4 October 2026) | `Report222.zip` (630,103 bytes, 18 files, no wrapper directory; `article.tex`, 1128 lines, 29 pp.) | `f79c9bef1` | `article.tex` |

The package records no ProveIt commit, so no pin is recorded.

**Status:** AI-assisted, unrefereed, not formalized: no Lean or Rocq
declaration exists for any statement of this report, and its place in the
collection confers no formal status.

## What the report proves

`A_+(N, q)` counts rooted trees with `N` vertices and `q` colors on the
non-root vertices up to color-preserving isomorphism (A242249), `A_−(N, q)`
those with trivial automorphism group (A255517); `a = e^{−1}`;
`L(N, q) = q^{N−1} N^{N−2}/(N−1)!` the exact Cayley baseline.

- **Theorem 4.1:** for either sign and every fixed `M`,
  `A_σ/L = e^{N S_σ(1/q)} H_σ(1/q) (1 + Σ_{j<M} d_{σ,j}(1/q) N^{−j} + O_M(1/(q N^M)))`
  **uniformly for all integers `q ≥ 40`**, from a common complex domain
  (Section 3, rational constants certified in Appendix A).
- Proposition 5.1: palette expansions of `S_±`, `log H_±`; hence the growth
  bases `D_±(q) = eq ± 1/(2e) + O(1/q)`.
- **Theorem 6.1:** the asymmetry crossover `p(N, q) → exp(−1/(e² α))` for
  `q/N → α`, with rounding-sensitive corrections.
- **Theorem 7.1:** leaf-sibling pairs `J ⇒ Poisson(1/(e² α))`; Theorem 8.2:
  every fixed order of signed-Poisson corrections; (54): the sharp
  total-variation constant `𝒞(α)/N`.
- **Theorem 9.3:** `Aut ≅ (C_2)^J` with probability `1 − (a³+a⁴)/(α² N) + O(N^{−2})`.
- Theorem 10.1: the labeled-sampling contrast (mean halved); Section 10.3:
  divergence of positive exponential moments.
- **Theorem 11.1:** diagonal corrections `ℓ_{±,1}`, `ℓ_{±,2}` for A242375 and
  A255523 (`b_±(n) = A_±(n+1, n)`); Proposition 11.2: a smooth inverse.
- Proposition 12.1 and Corollary 12.3: palette sizing and a global eventual
  integer threshold `q_min = ⌈q_*(N)⌉`.

(Section, statement and equation numbers are those of the committed PDF.)

## What the report does not claim

Enumeration (Riordan, Labelle, Foissy), fixed-model analysis
(Harary–Robinson–Schwenk, Genitrini), uniform transfer (Flajolet–Sedgewick),
automorphism laws (Olsson–Wagner) and asymptotic inversion are prior; the
leading diagonal constants are Kotěšovec's (OEIS); Labelle's 1992 article was
not accessible. No worldwide novelty claim, no effective onset; fixed
expansion depths; integer palettes only for probabilities; the ranges
`q ≥ 40`, `q ≥ 200`, `Q_0` and all onsets differ; moving Poisson parameter;
the class-`ℬ` defect is an upper bound for non-elementary-abelian groups; no
moment convergence; no finite-size monotonicity in `q`; no truncated
expansion inside a ceiling; numerical brackets are diagnostics.

## The write's findings

- **Kotěšovec's two conjectures are proved** (Remark 5.2, from
  Proposition 5.1): A242249's "Conjecture: d(k) ~ k * exp(1)." (26 August
  2014) and A255517's "Conjecture: For big k the limit asymptotically
  approaches k*exp(1)." (24 February 2015). The column growth base is
  `D_±(k) = k/r_±(1/k) = ek ± 1/(2e) + O(1/k)` for `k ≥ 20`, so both
  statements hold, with `d(k+1) − d(k) → e`. The source proves the expansions
  but does not name the conjectures. Solving the singularity equation with
  40-digit arithmetic reproduces Kotěšovec's posted `d(5)`, `d(10)`,
  `d(100)`, `d(200)` and the A255517 limits for `k = 5, 10, 100` in all 25
  significant digits compared. No OEIS edit.
- **One decimal corrected** (note at the end of Section 13.2):
  `𝒞(1) = 0.13683983139099866117…`; the printed `0.1368398313909987…` is a
  rounding; truncation `0.1368398313909986…`.
- **Remark 11.3 (transseries volume):** the diagonal core `X = L_y/W(eL_y)` is
  an exact instance of `p0:prop:factorial-core` (`κ = 1`, `d = 1`); the
  corrections in (72) are, formally, an instance of `p0:thm:core-reversion`
  (`Λ = h`); nearest-integer recovery at range points is an instance of
  `p0:thm:staircase`(3); Corollary 12.3 above `Q_0` is `p0:thm:staircase`(1)
  in the index `q`, with Lemma 12.2 excluding small palettes.
- **Recomputed:** all b-file terms of A242249 and A255517 with `n ≤ 60`,
  `k ≤ 40` (2460 each), both diagonals for `n ≤ 60`, all 36 entries of the
  table in Section 13, the class-`ℬ` defect row at `N = 80, …, 640`,
  `a³ + a⁴`, and the approach of exact diagonal values to `ℓ_{±,1}`,
  `ℓ_{±,2}`.

## Further questions, and the standing rule

Section 14 (the source's list, with a dated note under Vladimir's standing
rule of 4 October 2026): effective onsets, all-palette monotonicity,
exceptional automorphism groups, other local repetitions, moments and large
deviations, growing orders; added from the non-claims: a fixed-parameter
Poisson rate, an exact group total-variation constant, Labelle 1992. No claim
of the source was found false; the two OEIS conjectures are proved, not
refuted.

## Relation to the repository

No other file of the repository names A242249, A255517, A242375 or A255523.
Nearest (same directory): `a244407-high-outdegree-rooted-trees`,
`a055779-labeled-fat-trees`, `a003238-uniform-trees-binary-partitions`
(batch 112) and `a116379-bounded-identity-trees` (rooted identity trees of
bounded outdegree); no shared result, so no reciprocal note. No Lean or Rocq
development treats these sequences.

## Labels and numbering

All labels carry the prefix `mct:`: the 92 delivered labels, prefixed before
anything cited them (71 references updated: 48 `\eqref`, 23 `\ref`), the
write's label for Section 1 (`mct:sec:scope`), and the write's three
(`mct:sec:provenance`, `mct:rem:oeis`, `mct:rem:transseries`); 96 in all. The
write's remarks are the last statements of their sections and its additions
contain no numbered display, so every number is delivered (checked against
the `.aux` of a build of the delivered text: 92 labels, 0 differences).
Section 1.1 is the write's.

## Notation

No symbol was renamed. Letters with several senses are tabulated in Section
1.1 with the false readings: `N` versus the diagonal index `n` (A242375`(n)`
is `A_+(n+1, n)`), `A`, `D` (the growth bases `D_±(q)` are Kotěšovec's
`d(k)`), `L`/`ℒ`, `C`/`𝒞`, `H`/`h`, `S`, `R`, `r`, `p`/`P`, `a`, `λ` (the
class and labeled models' Poisson means differ by two), `δ`, `ε`.

## The write's additions

The status note after the abstract, Section 1.1 (provenance, sources read,
checks, relation, collected non-claims, reading conventions), Remarks 5.2 and
11.3, the dated notes at the ends of Sections 13.2 and 14, the label
prefixes and the label of Section 1, the bibliography entry `TSvol`, the
`\file` macro and `writenote` environment in the preamble, and the generated
table printed inline instead of `\input{tables.tex}`. Everything else is
delivered text.

## Files

```text
README.md                          this guide (replaces the delivered README.md)
article.tex                        the report (delivered article.tex, written)
article.pdf                        compiled report, 33 pages
code/build.py                      PDF and deterministic ZIP builder (delivered root build.py)
code/certify_bounds.py             rational certificate of the domain inequalities (Appendix A)
code/colored_trees.py              exact counts, marked polynomials, diagonals, inverses, palette search
code/diagnostics.py                optional mpmath diagnostics (crossover, defects, inverses, TV)
code/make_tables.py                generator of tables.tex
code/palette_jets.py               optional SymPy palette coefficients, orders 1..6
code/test_exact.py                 exact regression suite (Prüfer enumeration, Euler products, guards)
data/oeis_diagonal_prefix.json     OEIS diagonal prefixes n = 0..35 (third-party, CC BY-SA 4.0)
data/requirements-optional.txt     SymPy and mpmath versions (delivered root)
data/results-analytic_bounds.json  output of certify_bounds.py (delivered results/)
data/results-diagnostics.json      output of diagnostics.py --tv (delivered results/)
data/results-exact_checks.json     output of test_exact.py (delivered results/)
data/results-palette_jets.json     output of palette_jets.py --order 4 (delivered results/)
data/tables.tex                    generated table, printed inline in Section 13 (delivered root)
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to its delivery. Not shipped (retrievable from `60f54ea06`):
the delivered `Report222.pdf` (29 pages), the pure checksum manifest
`SHA256SUMS` (17 entries, verified at the write), and the delivered
`README.md`, replaced by this guide.

```sh
git show 60f54ea06:docs/incoming/Report222.zip > <scratch>/r222.zip
```

**Delivered text that names the delivery layout.** The programs write and
compare `results/*.json` and read `data/oeis_diagonal_prefix.json` by
delivered paths; `code/build.py` expects the delivered root layout
(`build.py`, `tables.tex`, `results/`, `SHA256SUMS`), so it runs only in a
re-extracted archive; Section 13 describes the delivered archive.

**Third-party data.** `data/oeis_diagonal_prefix.json` holds OEIS terms
(CC BY-SA 4.0, https://oeis.org/LICENSE), not MIT-0 like the rest of the
repository.

## Rerunning the checks (on scratch copies)

Never run the programs in place. From this directory (Git Bash):

```sh
T=$(mktemp -d); mkdir -p "$T/data"; cp -r code "$T/"; cp data/oeis_diagonal_prefix.json "$T/data/"
cd "$T"
py -B code/test_exact.py | tr -d '\r' | cmp - <(tr -d '\r' < "$OLDPWD/data/results-exact_checks.json") && echo same-exact
py -B code/certify_bounds.py | tr -d '\r' | cmp - <(tr -d '\r' < "$OLDPWD/data/results-analytic_bounds.json") && echo same-cert
py -B code/palette_jets.py --order 4 | tr -d '\r' | cmp - <(tr -d '\r' < "$OLDPWD/data/results-palette_jets.json")   # SymPy 1.14.0
py -B code/diagnostics.py --tv | tr -d '\r' | cmp - <(tr -d '\r' < "$OLDPWD/data/results-diagnostics.json")          # mpmath 1.3.0
```

At the write (7 October 2026, Windows, Python 3.14.4) all four outputs
equalled the recorded results after removing carriage returns
(`test_exact.py` also under `-O`; `diagnostics.py --tv` took 66 s). The
builder was not run.

## Build

pdfLaTeX (lmodern, amsmath, amssymb, amsthm, mathtools, microtype, booktabs,
longtable, array, hyperref, enumitem, fancyhdr, geometry). In a scratch copy:

```sh
B=$(mktemp -d); cp article.tex "$B/"; cd "$B"
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built this way with MiKTeX pdfLaTeX (7 October 2026):
33 pages; no errors or warnings, no undefined references, no multiply defined
labels, no duplicate destinations, no overfull or underfull boxes. The
delivered text (with its `tables.tex`) gives 29 pages with no warnings.

## Provenance

- Batch 112 of `docs/incoming`: bundle Report 222 (arrival `60f54ea06`),
  placed unprefixed by `f79c9bef1`; written 7 October 2026.
- Sources cited by the report: Riordan (1957); Labelle (1991, 1992);
  Harary–Robinson–Schwenk (1975); Bell–Burris–Yeats (2006); Genitrini (2016);
  Flajolet–Sedgewick (2009); Foissy (2021); Olsson–Wagner (2023);
  Bartholdi–Diaconis (2026); Dimitrov–Fox–Hadaway–Tharp–Wagner (2026); OEIS
  A242249, A255517, A242375, A255523; the ProveIt repository; and the
  repository's transseries volume (added by the write).
