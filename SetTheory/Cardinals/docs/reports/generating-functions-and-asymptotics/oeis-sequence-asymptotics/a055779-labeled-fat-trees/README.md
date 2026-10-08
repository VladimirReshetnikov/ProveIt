# Labeled Fat Trees (OEIS A055779, A295623)

**Uniform asymptotics and inverses for labeled fat trees: explicit
coefficients and a Poisson deficit window.**

A single-source report: bundle Report 203 of one external research session
(the session bundle of Reports 1–243, arrival commit `60f54ea06`), placed by
`f79c9bef1` (batch 112) and written on 7 October 2026. The title block and
the PDF author field read "Report 203"; the manuscript names no person, tool
or addressee.

| Source | Archive | Placed | Shipped as |
|---|---|---|---|
| *Uniform asymptotics and inverses for labeled fat trees: Explicit coefficients and a Poisson deficit window* ("Report 203", 4 October 2026) | `Report203.zip` (537,766 bytes, 20 files in `Report203/`; `Report203.tex`, 688 lines, 19 pp.) | `f79c9bef1` | `article.tex` |

The package records no ProveIt commit, so no pin is recorded.

**Status:** AI-assisted, unrefereed, not formalized: no Lean or Rocq
declaration exists for any statement of this report, and its place in the
collection confers no formal status.

## What the report proves

`A_n(M)` is the edge-weighted number of fat trees on `n` labeled vertices
(a set partition plus original-vertex edges whose contraction is a tree),
edge weight `M`; `A_n(1)` is A055779. With `r = r(M)` the root of
`M r (1+r) e^r = 1`, `b = (1+3r+r²)/(1+r)`, `q = M e^{H(r)}`,
`C = 1/(M√b)`:

- **Theorem 1.1:** for every fixed `J`, `A_n(M) = C q^n n^{n−2}
  {Σ_{j≤J} c_j(r) n^{−j} + O_J(n^{−J−1})}` **uniformly for all real
  `M ≥ 1`**, with rational `c_j` regular on `[0, r_1]`, `c_j(0) = 0`, a finite
  coefficient engine (4.3)–(4.5) and a second engine (4.10), `c_1` (1.6) and
  `c_2` (4.9) explicit.
- Corollary 6.1: the uniform logarithmic expansion with `d_j` (6.1)–(6.2), `d_2`
  explicit.
- **Theorem 7.1:** for fixed `M`, with `Y = log y`, `w = W(qY)`, `t = Y/w`,
  `L = w + 1`, recursive centres `X_J = t + Σ p_k t^{−k}` and
  `⌈X_J − K t^{−J−1}/L⌉ ≤ N_M(y) ≤ ⌈X_J + K t^{−J−1}/L⌉` (existential `K`).
- Section 8: the specializations to A055779, A295623 (`A295623(n) =
  n² A055779(n)`) and A162695, with Kotěšovec's parameter.
- Appendix A (block deficit `D = n − K`, `λ = n/M`): an exact tilted
  Poisson law, Theorem A.2 (explicit finite bounds, total variation
  `≤ min{1, (3λ²+2λ)/(2n)}` to `Pois(λ)`), and Theorem A.3 (every fixed order
  for bounded `λ`).

(Section, statement and equation numbers are those of the committed PDF.)

## What the report does not claim

The exact formula is Zaslavsky's (re-proved, not new); the leading amplitude
is implicit in Kotěšovec's 2014 A162695 formula; saddle-point and Poisson
assembly methods are standard (Arratia–DeSalvo credited). No first-prefactor,
global novelty, convergent-series, uniformity-in-`J`, optimal-truncation,
effective-onset or optimized-constant claim; the inverse is for fixed `M` only,
with no computable `K_{J,M}` and no single-ceiling rule; the deficit appendix
gives no rate to `Pois(1/τ)`, no maximal range, no tier theorem; the
block-count scales of Appendix C are motivation; the prior-source check was
bounded; numerical output is diagnostic.

## The write's findings

- **Remark 1.2 (OEIS):** A055779 (#42, Zaslavsky), A295623 (#15, Gutkovskiy)
  and A162695 (#19, Hanna; Kotěšovec's 2014 formula) quoted; the finite sum
  checked against all 100 b-file terms of A055779, the relation to A295623
  against all 360 of its b-file terms (`n ≥ 1`), and A162695's logarithm
  relation for `n ≤ 60`; the attributions of Section 2 match. **False
  readings recorded:** the "r" of A055779's limit formula is Kotěšovec's
  `p = 1/(1 + r_1) = 0.6924…`, and the "r" of A162695's formula is the
  report's `ρ`. No OEIS conjecture exists here.
- **Two decimals corrected** (note at the end of Section 8.1): `q(1)` and
  `c_1(r_1)` are printed rounded where "…" asks for truncation; the
  truncations are `q(1) = 1.65548791299153430662521161862…` and
  `c_1(r_1) = −0.07357275810351076496294030050…`. The other three constants
  and all eight diagnostic-table entries recompute correctly.
- **Remark 7.2 (transseries volume):** the centre `t` is an exact instance of
  `p0:prop:factorial-core` (`κ = 1`, `d = log q`, target `Y`); the
  corrections `p_k` are, formally, an instance of `p0:thm:core-reversion`
  (`Λ = L`, `h = 0`, after the shift by `p_0`); the two-ceiling bracket is an
  analogue of `p0:thm:staircase`(2), proved directly; the forward expansion is
  outside `p0:def:model`.
- Recomputed: `κ_1…κ_4`, `s_1`, `s_2` from the multi-index formula, `c_1`,
  `c_2`, `d_2`, `p_0…p_2`, (7.7), the Appendix's `E A(Z)`, `E A(Z)²`,
  `e_2(d)` and the second coefficient of (A.11).

## Further questions, and the standing rule

Appendix C (the source's own section, with a dated note under Vladimir's
standing rule of 4 October 2026) holds every open question: effective
constants, late terms and exponentially small corrections, the block-count
crossover (a formal differentiation offered as motivation; missing an
analytic-marking proof), sharper Poisson and component results; and, from
the non-claims, a uniform-in-`M` inverse, a computable `K_{J,M}`, a rate to
`Pois(1/τ)`. No claim of the source was found false; nothing is refuted.

## Relation to the repository

No other file of the repository names A055779, A295623 or A162695. Nearest
by object: `a242375-many-color-rooted-trees`, `a244407-high-outdegree-rooted-trees`
(batch 112, different models); by method: `a277364-bell-asymptotics`,
`a064856-stirling-catalan-transforms`. No shared result, so no reciprocal
note. No Lean or Rocq development treats these sequences.

## Labels and numbering

All labels carry the prefix `fat:`: the 70 delivered labels, prefixed before
anything cited them (48 references updated), and the write's three
(`fat:rem:oeis`, `fat:sec:provenance`, `fat:rem:transseries`); 73 in all. The
write's remarks are the last statements of their sections and its additions
contain no numbered display, so every section, statement and equation keeps
its delivered number (checked against the `.aux` of a build of the delivered
text: 70 labels, 0 differences). Section 1.1 is the write's.

## Notation

No symbol was renamed. Letters with several senses (the front-matter table
in Section 1.1): `D` (deficit, and the operator `z d/dz`), `A`, `r`/`p`/`ρ`/`s`
(with the two OEIS false readings above), `c`, `a`, `B` (also Bernoulli
numbers), `T`, `t`/`w`/`L`, `E`/`P`/`Q`, `K`.

## The write's additions

The status note after the abstract, Remark 1.2, Section 1.1 (provenance,
sources read, checks, relation to the repository, collected non-claims,
reading conventions), Remark 7.2, the dated notes in Section 8.1 and
Appendix C, the label prefixes, the bibliography entry `TSvol`, and the
`\file` macro and `writenote` environment in the preamble. Everything else is
delivered text.

## Files

```text
README.md                                     this guide (replaces the delivered README.md)
article.tex                                   the report (delivered Report203.tex, written)
article.pdf                                   compiled report, 22 pages
code-README.md                                the delivered code/README.md (programs, toolchain, provenance)
code/build.py                                 whole-package validation, replay, PDF and ZIP builder (delivered root build.py)
code/check.py                                 replay runner, normal and -O (delivered code/)
code/coefficients.py                          coefficient engine: cumulants, c_1, c_2, d_2 (delivered code/)
code/exact_checks.py                          exact audit: enumeration, recurrences, inverse recursion (delivered code/)
code/numerical_diagnostics.py                 mpmath diagnostics, labelled DIAGNOSTICS ONLY (delivered code/)
code/symbolic_checks.py                       SymPy checks of the formulas (delivered code/)
code/test_guards.py                           malformed-input, tampering and article-to-data tests (delivered root test_guards.py)
data/code-.python-version                     recorded Python version (delivered code/.python-version)
data/code-expected-coefficients.json          expected output of coefficients.py
data/code-expected-exact_checks.json          expected output of exact_checks.py
data/code-expected-numerical_diagnostics.json expected output of numerical_diagnostics.py
data/code-expected-symbolic_checks.json       expected output of symbolic_checks.py
data/code-requirements.txt                    pinned SymPy and mpmath (delivered code/requirements.txt)
data/manifests-source_manifest.json           source manifest with PDF engine banner and build epoch (delivered manifests/)
data/requirements.txt                         the same pins (delivered root requirements.txt; equal to the code copy)
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to its delivery. Not shipped (retrievable from `60f54ea06`):
the delivered PDF (19 pages), the pure checksum manifest
`manifests/package_manifest.json` (19 entries; verified at the write, as were
the 17 entries of the shipped source manifest), and the delivered README,
replaced by this guide.

```sh
git show 60f54ea06:docs/incoming/Report203.zip > <scratch>/r203.zip
```

**Delivered text that names the delivery layout.** The programs read
`expected/*.json` beside them; `build.py` and `test_guards.py` check the
closed delivered inventory (`Report203.tex`, the PDF, `manifests/`), so they
run only in a re-extracted archive; `code-README.md` and the source manifest
use delivered paths; Appendix B describes the delivered archive.

## Rerunning the checks (on scratch copies)

Never run the programs in place. From this directory (Git Bash; SymPy 1.14.0
and mpmath 1.3.0 installed for the last three):

```sh
T=$(mktemp -d); mkdir -p "$T/code/expected"
for f in coefficients exact_checks symbolic_checks numerical_diagnostics check; do cp "code/$f.py" "$T/code/"; done
for f in data/code-expected-*; do b=$(basename "$f"); cp "$f" "$T/code/expected/${b#code-expected-}"; done
cd "$T/code"
for p in coefficients exact_checks symbolic_checks numerical_diagnostics; do
  py -B $p.py | tr -d '\r' | cmp - expected/$p.json && echo "same $p"
done
```

At the write (7 October 2026, Windows, Python 3.14.4) all four outputs
equalled the recorded ones, in normal and `-O` mode. The delivered runner
`check.py --all` stops at its first comparison on Windows, because it compares
bytes and the programs' output there carries carriage returns (the intake
recorded the same). The builder and the guard tests were not run.

## Independent check of the write (7 October 2026)

An independent adversarial check of the write (`b76f517a4`) read A055779
(#42), A295623 (#15) and A162695 (#19) again. Every quotation and attribution
in Remark 1.2 is verbatim. The check recomputed the write's numbers with its
own code, by other methods wherever it could. It is recorded in a dated note
at the end of Appendix C.

- **OEIS data.** All 100 A055779 b-file terms agree. `A295623(n) =
  n² A055779(n)` for all 360 terms with `n ≥ 1`. The A162695 logarithm
  relation holds for `n ≤ 120`, by an exact power-series logarithm.
- **Enumeration.** A brute-force count over set partitions and cross-block
  edge sets for `n ≤ 6` reproduces `A_n(M)` and the OEIS comment's
  polynomials. (7.1) holds coefficientwise for `n < 60`.
- **Symbolic.** `κ_0…κ_4` by direct differentiation of `Mz e^z`; from them
  `s_1`, `s_2`, (1.6), (4.9), `d_2` and `c_j(0) = 0`.
- **Numerical, independent of the coefficient formulas.** Richardson
  extrapolation of exact `A_n(1)`, `300 ≤ n ≤ 1800`, gives `c_1(r_1)` and
  `c_2(r_1)` to 45 digits; at `M = 4` it gives `c_1` to 37 digits.
- **The inverse.** A numerical solve of `F_2(x) = Y` for `Y = 10⁴…10¹⁰`
  leaves `(x − X_2) t³ L` between 2.1 and 3.3, consistent with (7.4)–(7.6).
  (7.7) is an identity, and the engine (7.3) was re-derived by hand.
- **Decimals, diagnostics and the appendix.** All decimals were recomputed
  to 40 digits. The eight diagnostic entries are correct roundings. In the
  appendix, `E A(Z)`, `E A(Z)²`, `e_2` and the second coefficient of (A.11)
  are confirmed.
- **Remark 7.2.** Re-read against `p0:prop:factorial-core` and
  `p0:thm:core-reversion`: confirmed.
- **Provenance, manifests, byte identity and numbering.** All confirmed:
  20 files, 688 lines, 19 pp.; manifests 19/17; 16 staged files
  byte-identical; 70 labels unchanged, 3 added.
- **Delivered programs.** All four (`coefficients`, `exact_checks`,
  `symbolic_checks`, `numerical_diagnostics`) reproduce their expected
  outputs up to carriage returns.

**Corrected by a dated note (Section 8.1).** The write's own note printed
Kotěšovec's `p` rounded, as `0.6924583254616546081…`; the truncation is
`…6080…` (`p = 0.692458325461654608095939…`). The reading-conventions table
has the same slip as `0.6925…`, which should be `0.6924…`. This README's
"false readings" bullet is corrected accordingly.

Rebuilt: 22 pages (unchanged), label numbers unchanged.

## Build

pdfLaTeX (lmodern, microtype, geometry, amsmath, amssymb, amsthm, mathtools,
booktabs, array, xcolor, enumitem, fancyhdr, hyperref). In a scratch copy:

```sh
B=$(mktemp -d); cp article.tex "$B/"; cd "$B"
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built this way with MiKTeX pdfLaTeX (7 October 2026;
rebuilt after the independent check, three passes): 22 pages; no errors or warnings, no undefined references, no multiply defined
labels, no duplicate destinations, no overfull or underfull boxes. The
delivered text, built the same way, gives 19 pages with no warnings.

## Provenance

- Batch 112 of `docs/incoming`: bundle Report 203 (arrival `60f54ea06`),
  placed unprefixed by `f79c9bef1`; written 7 October 2026.
- Sources cited by the report: Zaslavsky, *Perpendicular dissections of
  space* (2002; arXiv:1001.4435); OEIS A055779, A295623, A162695; Kotěšovec's
  2012 note; Arratia–DeSalvo (arXiv:1606.04642v2); DLMF §5.11; and the
  repository's transseries volume (added by the write).
