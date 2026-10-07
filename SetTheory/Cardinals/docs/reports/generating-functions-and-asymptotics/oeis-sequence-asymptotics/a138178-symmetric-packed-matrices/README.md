# Symmetric Packed Matrices: All Fixed-Order Asymptotics (OEIS A138178)

**`A_n = e^{L²/4} I_n /(2 L^{n+1}) · (1 − L²/(6√n) + (−L²/4 + L⁴/18)/n + O(n^{−3/2}))`,
`L = log 2`, `I_n` the involution numbers, with every fixed further order,
uniformly for complex dimension and trace markers near one; independent
Gaussian limits of dimension and trace on the scales `n^{1/2}` and `n^{1/4}`;
independent Poisson(`L`) and Poisson(`L²/2`) laws of repeated diagonal and
off-diagonal cells with a sharp total-variation constant; and a Lambert-W
inverse with two-ceiling threshold bounds**

A research article ("Report 238" of a session bundle), built from one
manuscript dated 5 October 2026. Its author line and PDF author field read
"Report 238": it names no person, tool or addressee, and the phrase "private
review" does not occur in the package. The delivery README's build commands
used generic example paths; they are not reproduced here.

| Source | Bundle report | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | Report 238 (batch 108) | `Report238.zip` (30 files in a wrapper directory `Report238/`, 604,411 bytes, SHA-256 `255ba5ee…5f6eac3b`), arrival commit `60f54ea06`; main file `article.tex` with 12 files `sections/*.tex` (952 lines, 22 pp.) | none: the package names no ProveIt commit; its `SOURCES.md` describes a bounded look at existing reports | `602e5bd0f` (batch 108) | the whole report |

**Status:** AI-assisted, unrefereed, not formalized: no Lean or Rocq
declaration exists for any statement of this report. The only related Lean
material in the repository is the definition of the ordered Bell numbers and
their exponential generating function (see "Relation to the repository").
No proof uses a floating-point computation.

## Trust boundaries

- **Nothing is imported.** The proofs cite no published theorem: the exact
  geometric transform is proved (Proposition 1.1), although its unmarked case
  is Vladeta Jovovic's OEIS formula (2009), credited; the analytic estimates
  use classical tools only (Cauchy's formula and coefficient estimates, the
  partial-fraction expansion of the ordered-Bell kernel, Stirling's formula,
  Taylor's theorem with remainder, Gaussian integrals, Chernoff's
  inequality).
- **Credited prior results.** The leading equivalent of the symmetric binary
  companion (A135588) is Cameron–Prellberg–Stark's Proposition 4.2 (Electron.
  J. Combin. 13 (2006) R85), recovered in Section 7 as a consistency check,
  not used; their Section 2 is the (nonsymmetric) precedent for the Poisson
  collision mechanism. The write read both passages (arXiv:math/0510155v2)
  and found them as the source quotes them.
- **What the source proves.** Every theorem listed below, with complete
  proofs: a positive coefficient envelope that controls all nonreal ordered-
  Bell poles at every polynomial degree, global gamma and angular tail bounds,
  a finite Gaussian prescription for every coefficient with an integrable
  Taylor remainder, and compact-marker versions for the collision markers
  (including zero).
- **The package** checks finite identities exactly (counts to `n = 640`,
  three independent counting algorithms on smaller ranges, the OEIS
  prefixes), verifies the first coefficients symbolically, encloses
  `log 2` rationally to certify `1 < L + L² < 2`, and prints noncertified
  mpmath diagnostics. It proves nothing asymptotic.

## What it proves

`A_n(u,v) = Σ u^{D(M)} v^{T(M)}` over symmetric nonnegative integer matrices
`M` with no zero line, total entry sum `n` (an off-diagonal entry counts
twice), ordered positions; `D` the dimension, `T` the trace; `q = u/(1+u)`,
`L = log(1+1/u)`, `I_n(v) = n![x^n]e^{vx+x²/2}`. Statement numbers are the
delivered ones.

- **Proposition 1.1 (`spm:prop:transform`)**:
  `A_n(u,v) = (1+u)^{−1} Σ_{k≥0} q^k f_n(k,v)`, where
  `f_n(k,v) = [z^n](1−vz)^{−k}(1−z²)^{−(k²−k)/2}` counts all symmetric
  `k × k` matrices.
- **Theorem 2.1 (`spm:thm:main`)**: uniformly near `(u,v) = (1,1)`, for every
  fixed `J`,
  `A_n(u,v) = I_n(v) e^{S(L,v)} /((1+u)L^{n+1}) · (Σ_{j≤J} C_j(L,v) n^{−j/2} + O(n^{−(J+1)/2}))`,
  `S = (v²−1)L/2 + L²/4`, with `C_1`, `C_2` (and `D_2 = C_2 − C_1²/2`)
  explicit and every `C_j` given by a finite Gaussian prescription
  (Proposition 5.1, `spm:prop:algorithm`); derivatives of the remainder too.
- **Corollary 2.2 (`spm:cor:unmarked`)**: the display at the top; `1/(2L^{n+1})`
  may be replaced by `P_n/n!` (ordered Bell numbers) with exponentially small
  relative error.
- **Lemmas 3.1, 3.2, 4.1**: the positive majorant, the global gamma/Cauchy
  bound, uniform angular localization.
- **Proposition 6.1 (`spm:prop:cumulants`)**: `E D_n = n/(2L) + 1/(2L) − 1/2 − L/4 + O(n^{−1/2})`,
  `Var D_n = n(1−L)/(4L²) + …`, `E T_n = √n + L − 1/2 + …`, `Var T_n = √n + 2L − 1 + …`,
  `Cov(D_n,T_n) = −1/2 + (1−L)/(2√n) + O(n^{−1})`.
- **Theorem 6.2 (`spm:thm:gaussian`)**: `((D_n − n/(2L))/(σ_D√n), (T_n − √n)/n^{1/4})`
  tends to two independent standard normals, `σ_D² = (1−L)/(4L²) = 0.15966848…`.
- **Theorem 7.1 (`spm:thm:collision`)**: the marked expansion with repeated-cell
  markers `w` (diagonal), `ζ` (off-diagonal) on every fixed compact set,
  including `(0,0)`; `w = ζ = 0` is the binary model, giving (7.10)
  `B_n/A_n = e^{−L−L²/2}(1 + (L+L²)/√n + O(n^{−1}))`, `e^{−L−L²/2} = 0.39322485…`.
- **Theorem 8.1 (`spm:thm:joint`)**: dimension, trace and the two collision
  counts are asymptotically independent `N(0,1)`, `N(0,1)`, Poisson(`L`),
  Poisson(`L²/2`).
- **Theorem 8.2 (`spm:thm:TV`)**: `d_TV(Law(R_n,S_n), Pois(L)⊗Pois(L²/2)) = e^{−L−L²/2}L²(2+L)/√n + O(n^{−1})`
  (the constant is `0.50880570…`), and the adjusted means
  `L(1−n^{−1/2})`, `(L²/2)(1−2n^{−1/2})` give `O(n^{−1})`.
- **Corollary 8.3 (`spm:cor:massall`)**: all fixed-order signed (Charlier-type)
  corrections to the joint mass function, summable in `ℓ¹`.
- **Proposition 9.1 (`spm:prop:inverse`)** and **Theorem 9.2
  (`spm:thm:ceilings`)**: the smooth inverse
  `N + α√N + β + γ/√N + O(1/(NQ))` with `N = 2y/W(2y/(eL²))`, `Q = W + 1`,
  `y = log X`, its all-order form, and eventual two-ceiling bounds for
  `m(X) = min{n ≥ 1 : A_n ≥ X}`; `A_n` is strictly increasing for `n ≥ 1`.

Added by the write (6 October 2026), marked `[write]`:

- **Remark 1.2 (`spm:rem:oeis`)**: the OEIS entries, the b-file comparison and
  the Cameron–Prellberg–Stark passages (next section).
- **Remark 5.2 (`spm:rem:third`)**: the source's prescription (5.5) evaluated
  by the write at `u = v = 1` through `h³` (SymPy, own implementation, not
  shipped): it reproduces `C_1 = −L²/6`, `C_2 = −L²/4 + L⁴/18` and gives
  `C_3 = −L²(50L⁴ + 324L² − 1755)/6480 = 0.11772518…` at `L = log 2`
  (`D_3 = −L²(22L² − 65)/240`), so Theorem 2.1 with `J = 3` adds the term
  `C_3 n^{−3/2}` to Corollary 2.2, remainder `O(n^{−2})`. A table compares
  `A_n` with the expansion for `16 ≤ n ≤ 500`. One implementation only
  (Question 1); the independent check below confirmed the value numerically
  at three values of `L`.
- **Remark 9.3 (`spm:rem:transseries`)**, against the transseries volume:
  `m(X)` is exactly the staircase `N_*` of `p0:def:three-inverses` (an
  **instance**, `n_1 = 1`); the seed `N` is the core solution of
  `p0:prop:factorial-core` with `κ = 1/2`, `d = −1/2 − log L` (an
  **instance**), and the core equation alone is an instance of
  `plt:thm:lw-template` (data `(1, 1, −log 2, log(1 − (1 + 2 log L)t))`),
  which does not cover the `√x`, `c`, `b`, `d` terms; the coefficients
  `α, β, γ` are the first three terms of `p0:thm:core-reversion` after
  `x = N(1+E)`, `t = N^{−1/2}` (`Λ = Q`, `h(E) = (1+E)log(1+E) − E`, the
  volume's double-factorial `h`; an **instance after a change of variables**,
  formal part only; checked in SymPy), which also shows each coefficient to be
  a polynomial in `1/Q` without constant term; Theorem 9.2 and (9.10) are
  **analogues only** of `p0:thm:staircase`.
- **Section 12 (`spm:sec:further`)**: the open questions.
- Section 1.2 (`spm:sec:provenance`: provenance, the sources as the write
  read them, what was checked, relation to the repository, collected
  non-claims, reading conventions), a status note after the abstract, and
  dated notes in Section 1.1 (the rectangular counterpart in
  `a261781-matrix-compositions` Part IV, and the transseries volume's
  `q2:thm:fubini`), at the end of Section 4.3 (the passage from the auxiliary
  `k × k` matrices to packed ones, with a short proof), and in Sections 10.3
  and 10.4.

## The OEIS entries and the data

The live entry A138178 (revision #39, 18 December 2022, read 6 October 2026;
the revision the source inspected) is named, verbatim,

    Number of symmetric matrices with nonnegative integer entries and without zero rows or columns such that sum of all entries is equal to n.

Its 25 data terms (offset 0) equal the source's transcription (in
`code/exact_counts.py` and `data/count_receipt.json`). Its two generating
functions are the inclusion–exclusion form (Section 10, (10.4), at
`u = v = 1`) and Jovovic's `Σ_k 2^{−k−1}(1−x)^{−k}(1−x²)^{−C(k,2)}` of
9 December 2009 (Proposition 1.1 at `u = v = 1`); it has Wiseman's normal
semistandard-tableau comment and examples, and no asymptotic statement, so
Corollary 2.2 is the only asymptotic for A138178 in the entry or the
repository. The source could not retrieve Heinz's b-file (`n = 0..500`); the
write fetched it on 6 October 2026 and computed `A_0, …, A_500` exactly by its
own implementation (the recurrence (10.1) and the ordered Bell numbers): **all
501 terms agree**. A135588 (revision #17, 22 January 2024; 26 data terms)
agrees with the write's binary inclusion–exclusion count; it has no
asymptotic either. Nothing in either entry is corrected; nothing was
submitted to the OEIS.

**The expansion against the data** (Remark 5.2; exact counts, 50-digit
mpmath; `ϱ_n = A_n/(e^{L²/4} I_n/(2L^{n+1}))`, `h = n^{−1/2}`; rounded):

| n | ϱ_n | (ϱ_n−1)/h | (ϱ_n−1−C_1h)/h² | (ϱ_n−1−C_1h−C_2h²)/h³ | (ϱ_n−Σ_{j≤3}C_jh^j)/h⁴ |
|---|---|---|---|---|---|
| 16 | 0.97438 | −0.1025 | −0.0896 | 0.0709 | −0.1872 |
| 32 | 0.98295 | −0.0965 | −0.0927 | 0.0826 | −0.1986 |
| 50 | 0.98678 | −0.0935 | −0.0947 | 0.0889 | −0.2041 |
| 100 | 0.99102 | −0.0898 | −0.0976 | 0.0966 | −0.2112 |
| 200 | 0.99384 | −0.0872 | −0.1000 | 0.1024 | −0.2168 |
| 300 | 0.99504 | −0.0859 | −0.1012 | 0.1051 | −0.2194 |
| 400 | 0.99574 | −0.0852 | −0.1020 | 0.1067 | −0.2210 |
| 500 | 0.99621 | −0.0847 | −0.1025 | 0.1078 | −0.2222 |

with `C_1 = −0.08007550…`, `C_2 = −0.10728908…`, `C_3 = 0.11772518…`. The
delivered noncertified `data/diagnostic_receipt.json` records the second to
fifth columns at `n = 32, 80, 160, 320, 640` (at `n = 640`, `ϱ_n = 0.99667…`)
and agrees with the row `n = 32`. These are observations on a finite range;
they certify no coefficient and no rate.

## What is not claimed

From the source, kept in the article (collected in Section 1.2):

- The unmarked geometric transform is Jovovic's and "must not be mistaken for
  a newly discovered unmarked identity"; the binary leading equivalent is
  Cameron–Prellberg–Stark's, "recovered here as a consistency check"; the
  Poisson collision mechanism "has substantial precedent".
- The expansions are local in the dimension and trace markers (the trace
  marker is not carried through `v = 0`); the order `J` is fixed and "no
  uniform estimate in a growing order is asserted"; the diagnostics at
  `(u,v) = (2,2)` and `(1,1/2)` are "not an enlargement" of the theorem's
  neighbourhood.
- No span-one local limit of `T_n` and no total-variation approximation of
  `T_n` by an unrestricted Poisson law; the signed collision corrections are
  "not claimed positive"; the adjusted Poisson law is not claimed optimal; no
  effective `O(n^{−1})` constant or starting index.
- The inverse is "the inverse of the specified smooth approximation, not a
  definition of a noninteger combinatorial count"; the rounding shorthand
  (9.10) "does not claim that the ceiling of the bare displayed truncation is
  always correct"; Theorem 9.2 "is an asymptotic bound, not a certified
  finite-input inverse program".
- The bounded source check "is not a certificate of worldwide novelty"; no
  global priority, complete transseries or effective numerical onset.
- The exact checks' caps are implementation boundaries, "not a range
  restriction on the mathematical theorems"; the symbolic checks "do not
  constitute a machine-checked proof"; the diagnostics are noncertified;
  reproduction is claimed for the recorded toolchain only.

The delivery README adds that the manifest "is an integrity record, not a
digital signature or independent provenance proof". The write adds: `C_3` rests on one implementation by the write (Question 1),
confirmed numerically, not derived, by the independent check below.

## Further questions

Section 12 of the article (`spm:sec:further`) states every claim not proved
in full as an open question with its source, sketch and what is missing
(Vladimir's standing rule of 4 October 2026). The source's own seven
questions (Section 11: effective constants, the trace parity transition at
`v → 0`, lattice local limits, large deviations, higher collision
corrections and positive approximations, exponentially small sectors, other
matrix conventions) stay as printed. **Nothing in the source was found to be
wrong**, no claim was narrowed, and the source imports no unchecked input.

1. **The third coefficient** (`spm:q:third`, added by the write): a second,
   independent derivation of `C_3(L,1)` (for instance by the factorial-degree
   moments of `code/symbolic_coefficients.py`), and `C_3(L,v)` for `v ≠ 1`.
   The independent check below confirmed `C_3(L,1)` numerically, to eight to
   ten digits at `L = log 2, log(9/4), log(9/5)`; a derivation is still
   missing.
2. **The literature boundary** (`spm:q:priority`, source: Section 1 and
   `SOURCES.md`): whether the matrix-composition and Burge-polynomial papers
   (Munarini–Poneti–Rinaldi; Cerbai–Claesson), which the write did not read,
   or work on normal semistandard tableaux contain an asymptotic for this
   count; the source claims no priority.

## Checks made at intake

- At placement (batch-108 dossier, 6 October 2026; Windows, Python 3.14.4,
  SymPy 1.14.0, mpmath 1.3.0): the 28 staged files are byte-identical to a
  fresh extraction of the archive; `MANIFEST.sha256` 29/29. The dossier read
  the manuscript and found no error; it checked by hand the total-variation
  constant of Theorem 8.2 from the first mean corrections. On a copy,
  `build.py --verify-only` verified 29 files; `exact_counts.py` (`n ≤ 640`,
  about 15 s), `symbolic_coefficients.py` and `diagnostics.py` reproduced the
  three receipts; `guard_tests.py` stops on Windows at its own path guard; the
  PDF and ZIP rebuilds were not run.
- At the write (6 October 2026; same machine): the archive retrieved from the
  arrival commit again verified 29/29 and matches every staged file; Route B
  below reproduced `count_receipt.json`, `symbolic_receipt.json` and
  `diagnostic_receipt.json` byte for byte (about 50 s); the OEIS entries and
  b-file as above; by hand (and in part with SymPy) `C_1`, `B_1`, `G_1`, `H_1`
  of Section 5, `D_2` against the symbolic receipt, the cumulants of
  Proposition 6.1 and the residue (6.9), (7.3), (7.6), (7.7)–(7.10), the
  mass correction (8.3) and the constant of (8.4), the constants (9.2), the
  coefficients (9.5)–(9.7) (also by the volume's triangular recurrence), and
  the monotonicity argument; `C_3` and the table above.
- Sources read by the write: OEIS A138178 (with b-file) and A135588;
  Cameron–Prellberg–Stark, arXiv:math/0510155v2 (Proposition 4.2 and its
  proof, pp. 14–15; Section 2's first proof of Theorem 2.1, pp. 6–9); the
  transseries volume (`p0:def:core`, `p0:prop:factorial-core`,
  `p0:thm:core-reversion`, `p0:rem:core-instances`, `p0:def:three-inverses`,
  `p0:thm:staircase`, `plt:thm:lw-template`, `q2:thm:fubini`); Part IV of
  `a261781-matrix-compositions`. Not read: Munarini–Poneti–Rinaldi;
  Cerbai–Claesson.
- **Independent check of the write (6 October 2026).** An adversarial check
  made by the intake after the write (`c569b0b98`), with its own code, after
  fetching A138178, its b-file, A135588 and Cameron–Prellberg–Stark v2
  again. Counts by a route different from the write's (zero-line
  inclusion–exclusion (10.4) with `f_n(j)` from the first-order recurrence
  `(n+1)a_{n+1} = j a_n + (n−1+j+j(j−1)) a_{n−1}`): `A_0, …, A_2000` exactly,
  all 501 b-file terms and the 25 data terms agreeing; A135588's 26 terms by
  binomial cell factors. Remark 5.2: the table reproduced to every digit;
  Richardson extrapolation in `h` of the exact counts gives
  `C_3 ≈ 0.1177251847` (four node sets of 7–13 points up to `n = 2000`)
  against the formula's `0.1177251846518…`, and marked counts `A_n(u,1)` to
  `n = 1500` give `0.154285415` (`u = 4/5`) and `0.087284579` (`u = 5/4`)
  against `0.1542854152…` and `0.0872845791…` at `L = log(9/4)`,
  `log(9/5)`: numerical confirmation at three values of `L`, independent of
  the Gaussian prescription, not a derivation (Question 1 stays open).
  Remark 1.2: the entries, both generating functions, Proposition 4.2
  (`C_s ≈ 0.44341`, p. 14) and the Poisson(`(log 2)²/2`) limit with (8)
  (p. 9) as quoted. The notes in Sections 1.1 and 4.3 (`q2:thm:fubini`,
  Part IV of `a261781-matrix-compositions` with `r log 2 = 1.1046161…`, the
  Lean names; the identity in law) and Remark 9.3 (1)–(4) re-derived
  (`e_1, …, e_5` polynomials in `1/Q` without constant term, degrees
  1, 3, 5, 7, 9, `d` first in `e_4`). Archive facts and the 110/93 label and
  reference counts confirmed. No defect found. The check is recorded at the
  end of Section 5.

## Relation to the repository

**Formal status.** No statement of this report is formalized, and placement
in the collection confers none. The ordered Bell numbers of Corollary 2.2 are
defined in Lean as `Fabius.fubini`, with `Fabius.egfA_fubini` and
`Fabius.two_sub_exp_mul_egfA_fubini` (`(2 − e^t) Σ F_n t^n/n! = 1`), in
`Analysis/FabiusFunction/Lean/FabiusFunction/OrderedBell.lean`; nothing
asymptotic about them, and nothing about symmetric matrices, is formalized.

**The transseries volume**
(`Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/`):
see Remark 9.3 above. Its `q2:thm:fubini` (the exact pole-lattice formula for
the ordered Bell numbers) has the last sentence of Corollary 2.2 as its
one-pole truncation, and (3.3) at `L = log 2` as its first equality (note in
Section 1.1). No novelty is claimed for the inversions.

**Neighbouring reports** (under
`SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/`):

- `a261781-matrix-compositions`, **Part IV** (bundle Report 169, batch 108;
  labels `mxc:pm:`): the rectangular counterpart, packed matrices with `N`
  rows on the total-weight `2N` diagonal (A261784), by the same devices
  (geometric weighting of zero lines, the ordered-Bell pole at
  `log(1 + 1/u)`, complex-uniform marked expansions); its cells with entry
  ≥ 2 are Poisson of mean `r log 2 = 1.1046…`, `r = 2 + W₀(−2e^{−2})`,
  independent of the Gaussian column count (`mxc:pm:thm:joint`). Expansion
  in `N^{−1}` there, `n^{−1/2}` here; no theorem is shared, and neither
  report uses the other. That report already cites this one (Section 43 and
  its README); this report's note in Section 1.1 is the reciprocal one. The
  "Report 169" named in `SOURCES.md` is that Part.
- `a260700-parabolic-double-cosets`: the same ordered-Bell pole at `log 2`
  for a different sequence (a reciprocal note there is proposed separately).
- `a262810-diagonal-alignments` (bundle Report 177, batch 109): the other
  bundle report `SOURCES.md` names; a different model.
- `a007716-bipartite-multigraphs` (nonnegative matrices without zero lines up
  to row and column permutations) and `a027832-symmetric-sign-matrices`
  (symmetric `±1` matrices): different counts and methods.

**Stale claims.** Before batch 108 no file of the repository named A138178
or A135588; the source made no claim about the repository beyond its bounded
duplicate check.

## Notation

A table at the end of Section 1.2 fixes the letters the manuscript reuses,
with the tempting false readings: `L` (not the volume's target); `q`; `w`
(collision marker, Gaussian angular variable, and the Lambert value of
Section 9); `D(M)`, `D_n` against `D_2` and the exponent `D_J`; `S(L,v)`,
`S_*` against `S(M)`, `S_n`; `R`, `R_n`, `R_j`; `K` (auxiliary integer,
compact marker set); `B`, `B_n`, `B_J`; `a, b, c, d`; `h`, `H`, `H_j`, `H_±`;
`Q`, `Q_j` (and `COMPUTATION.md`'s `Q_n`); `N`; `M`, `M_n`; `P_n`, `P_j(u)`,
`P_1`, `P_2`; `λ, μ, κ, ρ` and `Λ`; `E_n`, `𝓔`; `r, s, t`. Symbols of the
volume carry the subscript "vol" in Remark 9.3. No symbol was renamed.

## Labels

Every label carries the prefix `spm:` (none existed in the repository). The
manuscript's 110 labels (`eq:` 84, `sec:` 11, `thm:` 6, `prop:` 4, `lem:` 3,
`cor:` 2) were prefixed before anything cited them, and the 93 references to
them updated. The write added 7: `spm:rem:oeis`, `spm:sec:provenance`,
`spm:rem:third`, `spm:rem:transseries`, `spm:sec:further`, and the questions
`spm:q:third`, `spm:q:priority`. The report has 117 labels; builds of the
delivered text and of this one give all 110 delivered labels the same numbers
(aux files compared). The added remarks are the last statements of their
sections, the added subsection and section follow the last delivered ones in
their places, and the added displays are unnumbered.

## Files

```text
README.md                          this guide (replaces the delivery README)
article.tex                        the report's main file (delivered; [write] macros and status note)
sections/01_model.tex              Section 1, notes, Remark 1.2 and the write's Section 1.2 (provenance, non-claims, notation)
sections/02_theorem.tex            Section 2, the marked expansion
sections/03_envelope.tex           Section 3, the positive envelope and the nonreal poles
sections/04_saddles.tex            Section 4, the two saddle variables (and the write's note at its end)
sections/05_all_orders.tex         Section 5, the finite Gaussian algorithm (and Remark 5.2)
sections/06_fluctuations.tex       Section 6, dimension and trace
sections/07_collisions.tex         Section 7, collision markers and the binary model
sections/08_total_variation.tex    Section 8, joint limits and total variation
sections/09_inverse.tex            Section 9, inversion (and Remark 9.3)
sections/10_computation.tex        Section 10, exact reproduction (two notes)
sections/11_outlook.tex            Section 11, further questions; Section 12 (the write's)
sections/12_references.tex         bibliography
article.pdf                        compiled report, 30 pages
COMPUTATION.md                     algorithms, bounds and limitations (delivered at the root)
SOURCES.md                         source attribution and its limits (delivered at the root)
code/build.py                      manifest-verified build and deterministic ZIP (delivered at the root)
code/common.py                     input bounds and exclusive output (delivered code/)
code/diagnostics.py                NONCERTIFIED mpmath diagnostics (delivered code/)
code/exact_counts.py               exact counts, independent deletion, enumeration, collision moments (delivered code/)
code/guard_tests.py                API, CLI, filesystem, manifest and ZIP guard tests (delivered code/)
code/reproduce_zip.py              actual-ZIP replay (delivered code/)
code/symbolic_coefficients.py      exact SymPy checks of C_1, C_2, collision and involution coefficients (delivered code/)
data/count_receipt.json            receipt of exact_counts.py (delivered code/)
data/diagnostic_receipt.json       receipt of diagnostics.py (delivered code/)
data/guard_receipt.json            receipt of guard_tests.py (delivered code/)
data/requirements.txt              sympy==1.14.0, mpmath==1.3.0 (delivered at the root)
data/symbolic_receipt.json         receipt of symbolic_coefficients.py (delivered code/)
```

Every file except `README.md`, `article.tex`, `sections/*.tex` and
`article.pdf` is byte-identical to the delivery; the `sections/` files differ
from the delivered bytes by the label prefixes and the marked additions
(`12_references.tex` is unchanged).

**Not shipped**, recoverable from the arrival commit (next section):
`Report238.pdf` (the delivered 22-page PDF, 440,783 bytes); `MANIFEST.sha256`
(2,547 bytes, 29 entries, verified at placement and at the write; repository
policy ships no checksum manifests); and the delivery `README.md` (5,430
bytes), staged at placement and replaced by this guide (summarized below).

**Delivered text that names the delivery layout or files not shipped.**
`code/build.py` takes its own directory as the package root, reads
`MANIFEST.sha256` there, expects the receipts in `code/` and the frozen
`Report238.pdf`, and refuses any other layout; `guard_tests.py` and
`reproduce_zip.py` use the delivered names, `build.py` and the manifest.
`COMPUTATION.md` ("All frozen files except MANIFEST.sha256 are listed in that
manifest"), `SOURCES.md` ("The package redistributes no third-party paper",
"Report238") and Section 10.4 of the article (dated note there) speak of the
package, its PDF, ZIP and manifest; those are in the arrival archive only.
`SOURCES.md`'s "Existing reports 169 (A261784 packed matrices) and 177
(A262810 diagonal alignments)" are the bundle reports now at
`a261781-matrix-compositions` Part IV and `a262810-diagonal-alignments`.
`code/common.py` sets `ROOT` to the parent of `code/` and refuses output
inside it; `guard_tests.py` stops on Windows at its own path guard, and the
PDF/ZIP builder needs POSIX and the delivering TeX toolchain. The three
mathematical programs read no data file, so they run from the shipped files
(Route B).

## Retrieving the delivered package

```sh
T=$(mktemp -d)
git -C /path/to/ProveIt show 60f54ea06:docs/incoming/Report238.zip > "$T/a.zip"
sha256sum "$T/a.zip"   # 255ba5ee21d187a7d35d274f8d6d5126c18ba54643ef99c64918eacb5f6eac3b, 604,411 bytes
cd "$T" && unzip -q a.zip && cd Report238 && sha256sum -c MANIFEST.sha256
```

## Rerun the checks (on a scratch copy)

Python 3.11 or later with `sympy==1.14.0` and `mpmath==1.3.0`
(`data/requirements.txt`). Never run anything in the repository.

**Route A, delivered layout** (as the delivery README gives it, from
`$T/Report238`; on a POSIX host for the guard tests and rebuilds):

```sh
python3 -B build.py --verify-only               # 29 files verified
python3 -B code/exact_counts.py                 # = code/count_receipt.json
python3 -B code/symbolic_coefficients.py        # = code/symbolic_receipt.json
python3 -B code/diagnostics.py                  # = code/diagnostic_receipt.json (noncertified)
python3 -B code/guard_tests.py
python3 -B -O code/guard_tests.py
python3 -B build.py --output-dir "$(mktemp -d)/build"   # PDF, ZIP, receipts; byte identity needs the delivering toolchain
```

The intake ran the first four on Windows (outputs equal to the receipts
after converting line endings);
`guard_tests.py` stops there at its path guard, and the rebuild and ZIP
replay were not run.

**Route B, from the shipped files, any OS** (tested at the write on Windows,
about 50 s in all):

```sh
R=/path/to/ProveIt/SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a138178-symmetric-packed-matrices
B=$(mktemp -d); mkdir "$B/code"
cp "$R/code/common.py" "$R/code/exact_counts.py" "$R/code/symbolic_coefficients.py" "$R/code/diagnostics.py" "$B/code/"
cd "$B"
P="uv run --no-project --with sympy==1.14.0 --with mpmath==1.3.0 python"
$P -B code/exact_counts.py          > ec.json   # = data/count_receipt.json
$P -B code/symbolic_coefficients.py > sc.json   # = data/symbolic_receipt.json
$P -B code/diagnostics.py           > dg.json   # = data/diagnostic_receipt.json
```

Any Python with those two packages can replace `$P`. The outputs equal the
receipts byte for byte. Outputs must go to standard output or to a new file
outside the copy (`--output`); the programs refuse anything else.

## Build the PDF

pdfLaTeX (fontenc, lmodern, microtype, geometry, amsmath, amssymb, amsthm,
mathtools, booktabs, array, longtable, xcolor, enumitem, fancyhdr,
hyperref); the bibliography is embedded in `sections/12_references.tex`.

```sh
B=$(mktemp -d); cp -r article.tex sections "$B/"; cd "$B"
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built this way with MiKTeX on 6 October 2026, after
the independent check (29 pages at the write; label numbers unchanged, aux
files compared): 30
pages; no errors, no LaTeX or package warnings, no undefined references or
citations, no multiply defined labels, no duplicate PDF destinations, no
overfull or underfull boxes. The delivered preamble's `\pdfmapfile` lines
make pdfTeX print 684 "fontmap entry … already exists, duplicates ignored"
notices, as many as in a build of the delivered text (22 pages, otherwise
clean but for one underfull line in the bibliography entry of
Cerbai–Claesson, which does not recur in this build). The delivered byte-identity claims apply to
`Report238.pdf` under the delivering toolchain, not to this build.

## From the delivery README

The delivery README (replaced by this guide) described the model (ordered
symmetric nonnegative matrices without zero lines, with dimension, trace and
repeated-cell markers), said that "The article supplies the mathematical
proofs" and that "The programs are bounded finite verifiers and
reproducibility tools, not proofs of asymptotic remainders", credited the
binary leading equivalent to Cameron–Prellberg–Stark and the unmarked
identity to Jovovic; listed the files under their delivery names; gave the
build, ZIP replay and individual-check commands of Route A (Python 3.11 or
newer, new output directories outside the package with existing parents,
"The commands never merge into an existing output directory", the optional
`--report-number 238`); described the manifest check, the receipt
regeneration, the private TeX build with shell escape disabled, the
byte-for-byte PDF requirement and the replay under normal and optimized
Python; stated the workload caps (`n ≤ 640` for the recurrences, 32 for
inclusion–exclusion, 12 for collision-marked deletion, 6 for direct
enumeration; diagnostics at 60 digits); and separated the exact count and
symbolic receipts from the mpmath diagnostics, which "are **not interval
certificates**".

## Rights

Repository contents are MIT-0. The article, `code/exact_counts.py` and
`data/count_receipt.json` quote the name or data terms of OEIS A138178
(`n = 0..24`) and A135588 (`n = 0..12`); OEIS content is published by The
OEIS Foundation Inc. under CC BY-SA 4.0 (https://oeis.org/LICENSE), and those
terms remain under that licence. The b-file was compared, not copied. No
third-party PDF is shipped. Nothing was submitted to the OEIS.

## Provenance

- Sources cited by the manuscript: OEIS A138178 and A135588;
  Cameron–Prellberg–Stark, Electron. J. Combin. 13 (2006) R85
  (arXiv:math/0510155); Munarini–Poneti–Rinaldi, J. Integer Seq. 12 (2009)
  09.4.8; Cerbai–Claesson, arXiv:2411.08426. No source was added by the
  write; it cites repository files by path.
- Batch 108 of `docs/incoming`, bundle Report 238; arrival `60f54ea06`,
  placement `602e5bd0f`, written 6 October 2026. Single source, so no merge
  choices. The delivered `article.tex` and `sections/` are shipped under the
  same names; the delivered programs and data as listed above.
