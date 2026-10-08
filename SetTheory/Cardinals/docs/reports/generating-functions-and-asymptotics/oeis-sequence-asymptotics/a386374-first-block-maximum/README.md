# First Maximum Frequencies in Ordered Partitions (OEIS A386374, A386375)

**Ordered set partitions whose first block is (strictly) largest: explicit
absolute residue errors, finite root-free expansions at every fixed order, two
different sharp oscillation scales (limsup 2/e, liminf 2 log 2) with the
constant term of each phase minimum, a phase-uniform strict/weak ratio, and a
finite-step Newton inverse with two-ceiling enclosures for the weak
sequence.**

A single-source report: bundle Report 208 of one external research session
(the session bundle of Reports 1–243, arrival commit `60f54ea06`), placed by
`a4186a946` (batch 113) and written on 7 October 2026. The author line and
the PDF author field read "Report208"; the manuscript names no person, tool
or addressee.

| Source | Archive | Placed | Shipped as |
|---|---|---|---|
| *First maximum frequencies in ordered partitions* ("Report208", 4 October 2026) | `Report208-reproducibility.zip` (470,406 bytes, 13 files, wrapper `Report208/`; `Report208.tex`, 551 lines, 15 pp.) | `a4186a946` | `article.tex` |

The package records no ProveIt commit, so no pin is recorded.

**Status:** AI-assisted, unrefereed, not formalized: no Lean or Rocq
declaration exists for any statement of this report, and its place in the
collection confers no formal status.

## What the report proves

`a_n` (A386374) counts words on an initial alphabet in which letter 1 is tied
for the highest frequency, i.e. ordered set partitions whose first block is
largest; `u_n` (A386375) requires it to be uniquely largest. `ρ = log 2`,
`F_n` the ordered Bell numbers, `P_n = a_n/F_n = E[J/K]` (1), `E_m` the
truncated exponential, `r_m` the root of `E_m(r) = 2`, `D_m = 2 − E_m(ρ)`.

- Section 1: the EGFs (4)–(6) and exact recurrences (7)–(8).
- **Theorem 2.1:** `|a_n/n! − Σ_m c_m r_m^{−n}| ≤ 11` for all `n ≥ 1`, by
  subtracting each positive pole before summing; (13) a relative form.
- **Theorem 4.1:** every fixed order as a finite sum over a moving window of
  `O(log n/log log n)` indices, with root-free amplitudes `T_m(n)` and
  polynomial corrections `Q_{m,l}`, relative error
  `O((log n)^{2L+2}/n^{L+1})`; explicit `Q_{m,1}`, `Q_{m,2}` (24)–(25).
- Proposition 5.1: a two-term phase law. **Theorem 6.1:**
  `limsup nP_n log log n/log n = 2/e`, `liminf nP_n/log log n = 2 log 2`,
  and the phase minimum `2ρ[log m + log log m + 1 − log ρ + o(1)]`.
- **Theorem 7.1:** `|u_n/n! − Σ (r_m/(m+1)) c_m r_m^{−n}| ≤ 4` and
  `u_n/a_n = (ρ/m)(1 + O(1/m))` uniformly over the phase, hence
  `u_n/a_n ~ ρ log log n/log n`.
- **Theorem 8.1** and Corollary 8.2: a finite-step Newton inverse of an
  explicit finite model started at `N + 1/2`, `N log(N/(eρ)) = log X`, and
  shrinking two-ceiling enclosures of the threshold `q(X)`.

(Section, statement and equation numbers are those of the committed PDF.)

## What the report does not claim

The moving-pole method, the factorial maximum-size scale, the pole
perturbation and the shrinking transition width are prior (Gourdon's 1996
thesis, Example 8; Flajolet–Sedgewick V.2); the constrained-Poisson profile
representation is prior (Carayol–Rotondo); no novelty for discrete ties or
Poisson approximation of maxima (Daly, Olofsson); non-overlap with Bender–Gao
is not established (abstract only). No worldwide novelty claim. The expansion
is a moving-window finite sum, not a power series in `1/n`; fixed orders
only; constants and onsets not certified; the inverse concerns the weak
sequence; the tables are floating fixed-range diagnostics; no unconditional
single-ceiling formula.

## The write's findings

- **The OEIS entries** (Remark 10.1): A386374 (#16, 27 July 2025) and
  A386375 (#12, 27 July 2025), both by John Tyler Rascoe (19 July 2025), with
  b-files by Alois P. Heinz (n = 0..425), and A308876 (#15, Ilya Gutkovskiy;
  the asymptotic signed by Václav Kotešovec, 2019) quoted. All 426 b-file
  terms of each entry equal the write's recurrence; no asymptotic formula, no
  conjecture, no literature reference in either entry, as the source says.
  No OEIS edit.
- **Recomputed with the write's own code:** brute-force words for `n ≤ 7`
  (counts and `P_n = E[J/K]` exactly); the EGF to degree 40; monotonicity;
  every numerical inequality of the proofs of Theorems 2.1, 7.1 and Section
  8 (the sampled circle minima are at least 1/2, well above the bounds); the
  deviations in (10), (33), (12) for `n ≤ 60` (at most 0.37, 0.12, 0.05;
  the last for `1 ≤ n ≤ 60`, see the independent check);
  the reversion coefficients (24) and `Q_{m,1}`, `Q_{m,2}` (25) (SymPy); the
  residue factorization `c_m(ρ/r_m)^n = T_m(n) G_{m,nD_m}(1/n)`; **every
  entry of Tables 2 and 3** (all correct roundings; truncations given in a
  dated note); the real-index phase minimum against the constant of (29)
  (differences −0.31, −0.25, −0.08, +0.08 at m = 10, 20, 40, 80); the
  strict/weak residue ratio times `m/ρ` (0.897 … 0.987 at the peaks).
- **Remark 8.4 (transseries volume):** growth outside `p0:def:model`; the
  Lambert scale `N` is an exact instance of `p0:thm:lambert-core` (positive
  branch); the real inverse and the Newton iterates are not shown to be
  instances of `plt:thm:lw-template` (the phase factor and the moving window);
  `B` is not an admissible interpolation (`B(n) ≠ a_n`), so Corollary 8.2 is
  an analogue of `p0:thm:staircase`(2), proved directly.

## Independent check of the write (7 October 2026)

An independent adversarial check of the write (`20f872d12`) read A386374
(#16), A386375 (#12) and A308876 (#15) again and recomputed every number the
write added, with its own code. It is recorded in a dated note at the end of
Section 10.

- **Confirmed:** both b-files (426 terms each), also against the two OEIS
  e.g.f.s expanded as exact rational series to degree 60 (a route that does
  not use the recurrences (7)–(8)); brute force over words for `n ≤ 7`
  (`P_n = E[J/K]` exactly); monotonicity to 425; the proof constants and the
  rational checks; the coefficients (24)–(25) by its own reversion; the
  residue factorization, which is an exact identity (`d_m(D_m) = r_m − ρ`);
  Tables 2 and 3 in every printed digit, with `D_m` summed as a tail and the
  roots taken at 100 and 320 digits; every truncation in the write's note;
  the phase minima and the strict/weak ratios at the peaks and troughs; the
  provenance figures, the byte identity of the ten staged files, the identity
  of the three inlined tables with the shipped table files, Remark 8.4, the
  label numbering (68 delivered labels unchanged) and the file listing.
- **Made precise (dated notes):** the Bell-pole deviation bound 0.05 holds
  for `1 ≤ n ≤ 60` (maximum 0.0406…); at `n = 0` the deviation is
  `1 − 1/(2ρ) = 0.2786…`, still inside 10. The strict/weak product
  `(u_n/a_n) m/ρ` "0.48–0.68 along the exact sequence" is the range of the
  write's five samples. Over every `50 ≤ n ≤ 425` it runs from 0.4697… at
  `n = 124`, the end of phase 2, to 0.7041… at `n = 125`, the start of phase 3.

No claim was found wrong in substance. Rebuilt: 20 pages, label numbers
unchanged.

## Further questions, and the standing rule

Section 10.1 (the source's three calculations: explicit constants and onset
with interval roots, higher phase corrections, a strict-sequence inverse),
with a dated note under Vladimir's standing rule of 4 October 2026; added from
the non-claims: a theorem-level comparison with Bender–Gao's full text and
interval-certified diagnostic tables. No claim of the source was found false;
nothing is refuted.

## Relation to the repository

No other file of the repository names A386374, A386375 or A308876. Ordered
set partitions occur with other statistics in
`a122399-surjection-diagonal`, `a261781-matrix-compositions` and
`a173217-ordered-tuple-relations` (batch 113, the same Fubini poles); none
treats block maxima. No shared result, so no reciprocal note. No Lean or
Rocq development treats these sequences.

## Labels and numbering

All labels carry the prefix `fbm:`: the 68 delivered labels (65 in the text,
3 in the generated tables), prefixed before anything cited them (64
references updated: 44 `\eqref`, 20 `\ref`), and the write's three
(`fbm:sec:provenance`, `fbm:rem:transseries`, `fbm:rem:oeis`); 71 in all.
The write's remarks are the last statements of their sections and its
additions contain no numbered display or table, so every number is delivered
(checked against the `.aux` of a build of the delivered text: 68 labels, 0
differences). Section 1.2 is the write's.

## Notation

No symbol was renamed. Letters with several senses are tabulated in Section
1.2 with the false readings: `a_n`/`α_m` (`α_m = E_{m−1}(ρ)` is not `a_m`),
`m` (block size, pole index, phase index), `P_n`/`p_m`, `D`/`d`/`Δ`, `B`,
`S`/`T`/`Q`/`q`, `N`/`x`/`y`/`z`, `t`/`v`/`λ`, `J`/`K`, `c`/`C`.

## The write's additions

The status note after the abstract, Section 1.2 (provenance, sources read,
checks, relation, collected non-claims, reading conventions), Remarks 8.4 and
10.1, the dated notes in Sections 9, 9.1 and 10.1, the label prefixes, the
bibliography entry `TSvol`, the `\file` macro and `writenote` environment, one
preamble line (`etoolbox`, a ragged-right bibliography, which removes the
delivered build's two underfull lines), and the generated tables printed
inline instead of `\input{tables/...}`. Everything else is delivered text.

## Files

```text
README.md                    this guide (replaces the delivered README.txt)
SOURCES.txt                  the source's public source list and reading limits
article.tex                  the report (delivered Report208.tex, written)
article.pdf                  compiled report, 20 pages
code/independent_check.py    word enumeration, rational EGF extraction, constants, corrections to order four
code/reproduce.py            driver: runs both checkers, regenerates data and tables, PDF and ZIP builder
code/verify.py               exact recurrences, composition and set-partition checks, SymPy identities, 100-digit diagnostics
data/independent.json        canonical output of independent_check.py (optimization flag omitted)
data/requirements.txt        mpmath 1.3.0 and SymPy 1.14.0
data/tables-diagnostic.tex   generated Table 2, printed inline in Section 9
data/tables-exact.tex        generated Table 1, printed inline in Section 1
data/tables-phase.tex        generated Table 3, printed inline in Section 9
data/validation.json         output of verify.py
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to its delivery (the delivered root programs moved to `code/`,
the requirements and `tables/*.tex` to `data/`). Not shipped (retrievable
from `60f54ea06`): the delivered `Report208.pdf` (15 pages) and the delivered
`README.txt` (replaced by this guide). The archive carries no checksum
manifest.

```sh
git show 60f54ea06:docs/incoming/Report208-reproducibility.zip > <scratch>/r208.zip
```

**Delivered text that names the delivery layout.** `SOURCES.txt` and Section
9.1 of the report describe the delivered archive (`Report208.tex`,
`tables/`, root programs; a dated note in Section 9.1 says what is shipped).
`code/reproduce.py` expects that flat layout and writes a PDF and ZIP, so it
runs only in a re-extracted archive.

**Third-party data.** `code/verify.py`, `data/independent.json` and
`data/tables-exact.tex` contain OEIS terms of A386374 and A386375 (CC BY-SA
4.0, https://oeis.org/LICENSE).

## Rerunning the checks (on scratch copies)

Never run the programs in place: both checkers write their JSON next to
themselves. From this directory (Git Bash):

```sh
T=$(mktemp -d); cp code/*.py "$T/"; D=$(cygpath -m "$PWD/data"); cd "$T"
py -B verify.py > /dev/null && py -B independent_check.py > /dev/null    # SymPy 1.14.0, mpmath 1.3.0; about 20 s
py -B -O verify.py > /dev/null && py -B -O independent_check.py > /dev/null
py -c "import json,sys; D=sys.argv[1]; s=json.load(open(D+'/independent.json')); strip=lambda d:{k:v for k,v in d.items() if k!='optimization'}
for a,b in [('validation.json','validation.json'),('validation_optimized.json','validation.json')]: print(a, json.load(open(a))==json.load(open(D+'/'+b)))
for a in ['independent_normal.json','independent_optimized.json']: print(a, strip(json.load(open(a)))==s)" "$D"
```

At the write (7 October 2026, Windows, Python 3.14.4) all four outputs
matched (`independent_*.json` apart from the recorded optimization flag,
which the driver omits), and the driver's table generator, applied to them,
reproduced the three `data/tables-*.tex` files byte for byte. The driver's
PDF/ZIP build was not run.

## Build

pdfLaTeX (lmodern, microtype, amsmath, amssymb, amsthm, booktabs, longtable,
array, needspace, geometry, hyperref, etoolbox). In a scratch copy:

```sh
B=$(mktemp -d); cp article.tex "$B/"; cd "$B"
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was rebuilt at the independent check from this file with
MiKTeX pdfLaTeX (three passes, 7 October 2026): 20 pages; no errors or warnings, no undefined references, no
multiply defined labels, no duplicate destinations, no overfull or underfull
boxes. The delivered text (with its `tables/`) gives 15 pages and two
underfull lines in the bibliography.

## Provenance

- Batch 113 of `docs/incoming`: bundle Report 208 (arrival `60f54ea06`),
  placed by `a4186a946`; written 7 October 2026.
- Sources cited by the report: OEIS A386374, A386375, A308876; Gourdon
  (1996 thesis; FPSAC 1995; Discrete Math. 1998); Flajolet–Sedgewick (2009);
  Daly (arXiv:2505.06088); Carayol–Rotondo (arXiv:2605.24068); Bender–Gao
  (CPC 2014, abstract only); Olofsson (1999, not retrieved); and the
  repository's transseries volume (added by the write).
