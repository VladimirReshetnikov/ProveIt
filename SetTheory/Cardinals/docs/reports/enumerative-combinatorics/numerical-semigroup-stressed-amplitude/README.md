# A Finite Positive Amplitude for Stressed Kunz Words

**Numerical semigroups of depth at most three, in Kunz coordinates: the
"stressed" words on {1,2,3} are claimed to satisfy `s_g = C_s ρ^g + O(ρ_2^g)`
with `0 < C_s < ∞`, `1/ρ` the positive root of `(x² + x³)(x + x² + x³) = 1`
(`ρ = 1.5151…`, Zhu's `r_{1.51}`), by an exact boundary renewal, an activity
transformation, a loop-aware container lemma, dense-window standardization
and an early-one penalty; with a two-pole expansion of the depth-at-most-three
count, an inverse threshold, and the vanishing of every fixed inverse-power
correction. The main theorem is not independently verified, and it runs
against the numerical expectation in Zhu's Conjecture 7.3.**

A single-source research report: Report 274 of an external research session,
which arrived alone in `764740f07` (6 October 2026), outside the session
bundle, and was placed by `2680aae95` in the enumerative-combinatorics
collection (no OEIS sequence is its object); written on 7 October 2026. The
author line reads "Research report 274" and the PDF author field is empty; the
manuscript names no person, tool or addressee.

| Source | Archive | Placed | Shipped as |
|---|---|---|---|
| *A Finite Positive Amplitude for Stressed Kunz Words: A Self Contained Proof with an Exponential Remainder* ("Research report 274", 6 October 2026) | `Report274_Stressed_Kunz_Finite_Amplitude.zip` (448,517 bytes, 9 files, wrapper `Report274/`; `article.tex`, 824 lines, 21 pp.) | `2680aae95` | `article.tex` |

The package records no ProveIt commit, so no pin is recorded. It names
Reports 270 and 271 as earlier reports of the same research sequence; they
were not delivered, and if they arrive they continue this report.

**Status:** AI-assisted, unrefereed, not formalized: no Lean or Rocq
declaration exists for any statement of this report, and its place in the
collection confers no formal status. **Trust boundary: the main theorem is
not independently verified.** The write read every step of its proof and
found no error, and every exact finite identity it tested holds, but the
constants are existential and astronomically weak (the early-one saving is
below `10⁻⁴` per letter), the finite data are far from the asserted limit,
and the source itself asks for an independent check of the all-length
argument.

## What the report claims and proves

A stressed word is a word on {1,2,3} ending in 3 with `w_i + w_j ≥ w_{i+j}`;
`s_g` counts them by genus (the sum of the letters), `t_g` counts semigroups of
depth at most three, `P = A·B` with `A = z² + z³`, `B = z + z² + z³`,
`P(ξ) = 1`, `ρ = 1/ξ`.

- Section 2: the Kunz bijection and the classical Fibonacci filter
  `𝒯 = (1 + 𝒮)/(1 − z − z²)` (Proposition 2.1).
- Proposition 3.1: an exact length-refined renewal for the class `U` of words
  whose first 1 lies beyond one third of the length: `𝒰 = N/(1 − P)` with
  boundary polynomials `D_r` (1.6).
- Proposition 4.1: an exact activity transformation
  `D_r = A·S_r(A², A²C, A²z³)` (and a general version with the map 𝔗).
- Lemma 5.1, Sections 6–7: a loop-aware container lemma, dense-window
  standardization with weighted preimages, and the criterion of
  Proposition 7.2 (`S_L ≤ Kθ^L` when three pair factors are below one).
- Proposition 8.1: `D_r(33/50)` decays exponentially (rational certificates).
- **Theorem 9.1:** at the critical point, words with a 1 in the first third
  have exponentially small total weight (three cases; translated forbidden
  pairs and a disjoint-block selection).
- **Theorem 1.1:** `s_g = C_s ρ^g + O(ρ_2^g)`, `C_s = N(ξ)/(ξP'(ξ)) ∈ (0,∞)`;
  Corollary 10.1 (ratios, roots, monotonicity); Corollary 11.1:
  `t_g = S_lead φ^g − κ C_s ρ^g + O(ρ_3^g)`; Corollary 12.1: a shrinking
  two-ceiling inverse bracket; Corollary 12.2: every fixed inverse-power
  correction vanishes.

(Section, statement and equation numbers are those of the committed PDF.)

## What the report does not claim

The stressed-word encoding, the lower family and the filter are Bacher's and
Zhu's; the dense-window standardization is Zhu's; the container method is
classical (Samotij). No comprehensive priority claim, no peer review. Not
claimed: a numerical value or useful approximation of `C_s`; a practical onset;
anything about depth at least four; the sign of the full secondary residual;
the next singularity or optimal remainder bases; a practical inverse; that the
finite tests prove the criterion or the three-case argument.

## The write's findings

- **Zhu read** (dated note at the end of Section 1.2): arXiv:2202.05755v3
  (7 September 2023). The "Section 7.3(c)" of the source is Conjecture 7.3(c)
  (p. 19), stated jointly for the depth-at-least-four count `n̂_g` and `s_g`;
  Zhu's text calls exponential asymptotics for them unlikely on the evidence
  and suggests exponents between 1.6 and 1.7. Theorem 1.1 would prove the
  `s_g` halves of Conjecture 7.3(a)–(c) with `α' = 0`. **Zhu's Table 2
  (`s_g`, `g ≤ 95`) gives `s_g/ρ^g` = 0.3276, 0.4937, 0.9137, 1.4309, 2.1860
  at `g = 20, 30, 50, 70, 95`, still increasing (local exponent 1.40 at
  `g = 95`)**; this does not contradict a theorem without effective constants,
  but its limit regime lies beyond all available counts.
- **The boundary series** (dated note in Section 14): at the critical point
  the terms `D_r(ξ)` are still increasing through `r = 33` (0.4386, …, 0.5907
  for odd `r = 23…33`), by factors between 1.04 and 1.10 every two steps,
  slowly decreasing, although the transformed activities satisfy the
  criterion with rate bound 0.9715; the lower approximants `C_s^(R)` reach
  2.4159 at `R = 33`. The proof's polynomial factors allow such a transient.
- **Recomputed with the write's own code:** every Kunz word on {1,2,3} of
  genus `g ≤ 26` (`s_g`, `t_g` equal Zhu's Table 2; the filter, which also
  holds throughout Zhu's table to `g = 95`; the class `U` equals `N/(1 − P)`,
  also with the length refinement (3.1)); the transformation (4.2) as a
  polynomial identity for `r ≤ 6` and modulo `z²⁷` for `r ≤ 8`, the general
  identity (4.4) at three rational triples, the iterates (4.6); every rational
  certificate ((1.4), (1.5), (8.2)–(8.5), `E(x)²` and its derivative (9.6),
  `E(2/3)² = 1120000/1121931`, `T_0(2/3) = 64/81`); `ξ`, `ρ`, `ξP'(ξ)`, the
  critical factors and the saving `τ ≈ 7.7·10⁻⁵` of (9.16).
- **Remark 12.3 (transseries volume):** conditional on Theorem 1.1, the growth
  is an exact instance of `p0:def:model` along the integers (exponent one,
  no logarithmic term, zero correction series); the inverse centre `x_0(y)` is
  an exact instance of `p0:thm:lambert-core`(1); Corollary 12.1 and the
  exact-count recovery are analogues of `p0:thm:staircase`(2) and (3).
- **The OEIS** (Remark 13.1): `n_g` is A007323 (#263, Zagier; with
  Bras-Amorós's conjecture `a(n) ≥ a(n−1) + a(n−2)`, which the report does not
  decide); `s_g` and `t_g` are not in the OEIS. No OEIS edit.

## Further questions, and the standing rule

Section 14 (the source's five directions: depth four and the full secondary
residual, a certified amplitude, the finite-genus regime, subdominant
singularities, general activity domains), with a dated note under Vladimir's
standing rule of 4 October 2026 adding: an **independent verification of
Theorem 1.1**, which the source requests, and a quantitative study of the
boundary series at the critical point. No claim of the source was found
false; nothing is refuted.

## Independent check of the write (7 October 2026)

An independent adversarial check of the write (`a08662116`) was asked to probe
the main theorem as far as light computation allows.

- **Proof re-read; no error found.** The check re-read the container lemma,
  the independence of the standardized prefix one-set, the eligibility budget
  and the criterion (Proposition 7.2), the certificates of Proposition 8.1,
  the three cases of Theorem 9.1 (the translated relations, the bound `η`,
  the block-disjoint selection, the parameter order) and the residue step. It
  found no error. This is again a reading, not a verification: the theorem
  stays marked as not independently verified. Its constants are existential
  (`τ = 7.686·10⁻⁵`), so no finite computation can confirm or refute it.
- **Confirmed with the check's own code:**
  - every rational certificate and critical constant;
  - `D_r(ξ)` for `r ≤ 33`, by a second code (enumeration of `J` in (1.6)),
    equal to the write's values to `4·10⁻¹²` relative, with
    `C_s^(33) = 2.41595…`;
  - `D_r = A·S_r(𝔗)` at `ξ` for `r ≤ 27`;
  - the length-refined renewal (3.1) at `ξ`, against an exact enumeration of
    all stressed words of length `L ≤ 29`;
  - Zhu's Table 2, parsed from the re-fetched arXiv v3: the filter, and every
    ratio and local exponent quoted in Section 1.2;
  - a brute force to `g = 26`;
  - A007323 and the OEIS searches;
  - the provenance, the staged bytes and the README listing;
  - the numbering: 96 labels, 0 differences against the `.aux` of a build of
    the placed text.
- **New exact computations (bracketed dated notes in Sections 1.2 and 14):**
  - *Zhu's counts split into the separated class `U` and the early-one class
    `V`.* Here `s^U_g = [z^g] N/(1−P)` is exact for `g ≤ 107`. The early-one
    share is 0.447 at `g = 20`, 0.623 at `g = 50` and 0.665 at `g = 90, 95`:
    rising, but flattening. At `g = 95`, `s^U_g/ρ^g = 0.7305…` and
    `s^V_g/ρ^g = 1.4555…`, both increasing.
    - If the theorem holds, the second tends to zero and the first to
      `C_s > 2.4159`. So `s_g/ρ^g` (2.186 at `g = 95`) must still pass 2.41,
      while two thirds of today's count become negligible.
  - *The critical length-weights* (exact, `L ≤ 29`). The early-one part `V_L`
    is 1.119, 1.327, 1.499, 1.593 at `L = 23, 25, 27, 29`: increasing, and
    about 60 % of the total.
  - *Two more boundary terms*: `D_34(ξ) = 0.4109…` and `D_35(ξ) = 0.6243…`.
    Both are still increasing, by a factor 1.057 over two steps in both
    parities, and `C_s^(35) = 2.6667…`.
- **Not reported in the article:** a forward sequential Monte Carlo. It
  reproduces `D_r` for `r ≤ 33`, but it misses the separated class at larger
  `L` (it gives `U_L ≈ 0` at `L = 81`, where the renewal gives 3.92). Its
  apparent decay of `D_r` beyond `r ≈ 100` is therefore not evidence.

No claim of the write was found wrong. The check is recorded at the end of
Section 1.3.

## Relation to the repository

No other report treats numerical-semigroup enumeration by genus.
`numerical-semigroup-leaf-types` treats the same objects with a structural
question (leaves of large type in the semigroup tree) and
`a069762-pyramidal-frobenius` treats Frobenius numbers; no shared result, so no
reciprocal note. No Lean or Rocq development treats these objects.

## Labels and numbering

All labels carry the prefix `ska:` (used nowhere else in the repository): the
96 delivered labels, prefixed before anything cited them (64 references
updated: 51 `\eqref`, 13 `\ref`), and the write's three (`ska:sec:provenance`,
`ska:rem:transseries`, `ska:rem:oeis`); 99 in all. The write's remarks are the
last statements of their sections and its additions contain no numbered
display, so every number is delivered (checked against the `.aux` of a build
of the delivered text: 96 labels, 0 differences). Section 1.3 is the write's.

## Notation

No symbol was renamed. Letters with several senses are tabulated in Section
1.3 with the false readings, notably `α, β, γ` (in Section 4 `β = u + v + w`,
in Sections 6–9 `β = v + w`), `A, B, C, P, Π`, `D, N, n`, `H, R`, `L, M`,
`q, Q`, `S_r` versus `𝒮`, `t, u, v`, `δ, λ, ρ`.

## The write's additions

The status note after the abstract, the dated note at the end of Section 1.2,
Section 1.3 (provenance, sources read, checks, relation, collected
non-claims, reading conventions), Remarks 12.3 and 13.1, the dated notes at the
ends of Sections 13 and 14, the label prefixes, the bibliography entry
`TSvol`, and the `\file` macro and `writenote` environment. Everything else is
delivered text.

## Files

```text
README.md                        this guide (replaces the delivered README.md)
SOURCES.md                       the source's sources and proof scope
article.tex                      the report (delivered article.tex, written)
article.pdf                      compiled report, 26 pages (a build of this text)
code/build.py                    delivered builder: allowlisted snapshot, tests, TeX, ZIP and pins (Linux only)
code/companion-exact_checks.py   delivered companion: bounded exact checks (delivered companion/exact_checks.py)
code/tests-test_build.py         33 builder regression tests (delivered tests/test_build.py; Linux only)
code/tests-test_companion.py     13 companion regression tests (delivered tests/test_companion.py)
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to its delivery (the builder and the companion and test files
moved to `code/`). Not shipped (retrievable from `764740f07`): the delivered
`article.pdf` (21 pages), `MANIFEST.sha256` (8 entries, all verified at the
write) and the delivered `README.md` (replaced by this guide).

```sh
git show 764740f07:docs/incoming/Report274_Stressed_Kunz_Finite_Amplitude.zip > <scratch>/r274.zip
```

**Delivered text that names the delivery layout.** Section 13 and
`SOURCES.md` describe the delivered archive (a dated note at the end of
Section 13 says what is shipped). `code/build.py` checks the exact delivered
seven-file layout (`companion/`, `tests/`) and needs Linux descriptor
features, so it runs only in a re-extracted archive on Linux.

## Rerunning the checks (on scratch copies)

The companion and its tests expect the delivered `companion/` and `tests/`
directories. From this directory (Git Bash):

```sh
T=$(mktemp -d); mkdir -p "$T/companion" "$T/tests"
cp code/companion-exact_checks.py "$T/companion/exact_checks.py"; cp code/tests-test_companion.py "$T/tests/test_companion.py"
cd "$T"
py -I -B -X int_max_str_digits=640 companion/exact_checks.py > normal.json
py -I -B -X int_max_str_digits=640 -O companion/exact_checks.py > optimized.json
cmp normal.json optimized.json && echo identical
py -I -B -X int_max_str_digits=640 tests/test_companion.py
```

At the write (7 October 2026, Windows, Python 3.14.4) the two outputs were
identical, every count in the delivered README's coverage list was
reproduced, and the 13 tests passed in both modes. The builder and its 33
tests were not run.

## Build

pdfLaTeX (fontenc, lmodern, geometry, amsmath, amssymb, amsthm, mathtools,
booktabs, array, microtype, enumitem, hyperref, fancyhdr). In a scratch copy:

```sh
B=$(mktemp -d); cp article.tex "$B/"; cd "$B"
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built from this file with MiKTeX pdfLaTeX (three
passes, 7 October 2026): 25 pages; no errors or warnings, no undefined
references, no multiply defined labels, no duplicate destinations, no
overfull or underfull boxes. The delivered text gives 21 pages, equally clean.
(MiKTeX prints 724 pdfTeX notices of duplicate font-map entries in both
builds; these are not LaTeX warnings.) The independent check rebuilt the PDF
on 7 October 2026, three passes: 26 pages (the check notes add one), equally clean, label numbers
unchanged.

## Provenance

- Report 274 (arrival `764740f07`, 6 October 2026), placed by `2680aae95`;
  written 7 October 2026.
- Sources cited by the report: Zhu, *Sub-Fibonacci behavior in numerical
  semigroup enumeration* (Combinatorial Theory 3(2), 2023; arXiv:2202.05755v3,
  read by the write); Bacher, *Generic numerical semigroups*
  (arXiv:2105.04200); Samotij (Eur. J. Combin. 48, 2015); the undelivered
  Reports 270 and 271; and the repository's transseries volume and OEIS
  A007323 (added by the write).
