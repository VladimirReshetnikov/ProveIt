# Nonattacking Bishops: the Amplitude and the Diagonal Corrections (OEIS A002465, A238260)

**`B_n = b Γ(n) qⁿ (Σ_{j≤J} c_j^{(n mod 2)}(r) n^{-j} + O_J(n^{-J-1}))` for
every fixed `J`, with `r ∈ (1,2)` the root of `r/(1−e^{−r}) = 2`,
`q = e^r/r` and the closed form `b = e^r/(2π√(r²−1)) = 0.63126…` of the
OEIS constant A238260; rational `c_j`, parity first at `n⁻³`; a
parity-preserving two-ceiling inverse with a Lambert centre**

A research article ("Report 219" of a session bundle), built from one
manuscript dated 4 October 2026. Its author line reads "Report 219" and its
PDF author field "Research report": it names no person, tool or addressee.
The package carries no "prepared for private review" line, no e-mail address
and no personal data; the delivered README's `/tmp/report219-*` paths are
example output paths.

| Source | Bundle report | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | Report 219 (batch 109) | `Report219-reproducibility.zip` (27 files under the wrapper directory `Report219/`, 440,564 bytes, SHA-256 `a0561728…ceaa454cc7`), arrival commit `60f54ea06`; main file `Report219.tex` (534 lines, 13 pp.) | none: the package names no ProveIt commit and no repository path | `f7e9e5c2f` (batch 109) | the whole report |

**Status:** AI-assisted, unrefereed, not formalized: no Lean or Rocq
declaration exists for any statement of this report, and nothing in the
repository's formal developments concerns bishop placements or rook numbers
of Ferrers boards.

## Trust boundaries

- **What is proved by hand.** The exact formula (Section 2: the two Ferrers
  boards, the rook recurrences, the Stirling convolution, Proposition 2.1),
  Lemma 3.1 (the moving amplitude, uniformly), the saddle argument of
  Section 4 (unique torus maximum, domination), the finite coefficient rule
  of Section 5, the parity split of Section 6, Theorem 1.1 and Theorem 7.1.
  No proof uses a computation.
- **What rests on computation.** The explicit rational functions `c_1`, `c_2`
  (equation (4)) and `c_3^{(p)}` (Appendix A) are outputs of the finite rule
  (27), produced by the shipped programs and compared there with an
  independent affine route; only the parity difference
  `c_3^{(1)} − c_3^{(0)} = r³/(4(r+1))` is also derived by hand (Section 6).
  The order-4 receipt is angular-only.
- **What is diagnostic.** The decimal table of Section 1 and every numerical
  residual or inverse comparison (the shipped diagnostics use mpmath, not
  interval arithmetic). Every remainder constant and onset is existential.
- **What is prior.** The exact enumeration (Perott 1883, Arshon 1936,
  Kotěšovec, Santos 2025), the exponential base `q` (A002465, A238258) and
  the leading equivalent `B_n ~ b qⁿ (n−1)!` with numerical `b` (Kotěšovec's
  book, p. 249, as the source reports it). The source's comparison is "a
  bounded comparison, not a claim of global historical priority".

## What it proves

`B_n` counts placements of `n` indistinguishable nonattacking bishops on an
`n × n` board, without symmetry quotient (A002465, `B_0 = 1`). Statement and
equation numbers are the delivered ones.

- **Theorem 1.1 (`bsh:thm:main`)**: the expansion above, for each fixed `J`,
  with one error constant for both parities; `c_0 = 1`; `c_1`, `c_2`
  parity-free (4); `c_3^{(1)} − c_3^{(0)} = r³/(4(r+1)) > 0` (3).
- **Section 2 (`bsh:sec:exact`)**: the white and black Ferrers boards
  `1,1,3,3,…` and `0,2,2,4,…` (5), their rook recurrences (6)–(7) (Santos's
  Theorem 4), `B_n = Σ_k W(n,k)K(n,n−k)` (8), the Stirling convolution (10)
  (a reindexing of the Arshon–Kotěšovec formula), and **Proposition 2.1
  (`bsh:prop:exact`)**: `B_n = n! [xⁿyⁿ] F(x,y)ⁿ H_{n,h}(x) H_{n,g}(y)`,
  `F = eˣ + eʸ − 2`.
- **Lemma 3.1 (`bsh:lem:amplitude`)**: `H_{n,n/2+δ}(x) = e^{x/2}(Σ P_j(x,δ)n^{-j}
  + O(n^{-J-1}))` uniformly on discs, with Touchard-polynomial amplitudes
  `P_j` (15); `P_0, …, P_3` displayed (18).
- **Section 4 (`bsh:sec:saddle`)**: the Hessian `K = [[r,−1],[−1,r]]` (21),
  the origin as the unique maximum of `|F|` on the torus, the domination
  argument to every fixed order, and the normalization `b Γ(n) qⁿ`.
- **Section 5 (`bsh:sec:engine`)**: the finite rule (27) for every
  `c_J^{(p)}` as a Gaussian moment of a finite expansion; every `c_J^{(p)}`
  is a rational function of `r`; Section 5.1, the affine contour as a second
  symbolic route.
- **Section 6 (`bsh:sec:parity`)**: why parity first appears at `n⁻³`, by a
  short computation.
- **Theorem 7.1 (`bsh:thm:inverse`)**: for `N(y) = min{n ≥ n_0 : B_n ≥ y}`,
  `⌈t − ρ_J(t)⌉ ≤ N(y) ≤ ⌈t + ρ_J(t)⌉`, `ρ_J(t) = D_J/(t^{J+1} log(qt))`,
  around the root `t_J(y)` of a cosine-interpolated model `Φ_J` (29)–(30),
  "not a canonical interpolation"; Section 7.1, the Lambert centre
  `t = L/W(qL/e)`, `L = log y`, with one Newton correction (34)–(35).
- **Section 8 (`bsh:sec:checks`)**: the four kinds of finite checks, and the
  inclusion–exclusion formula (36) for `k`-matchings of a bipartite graph,
  with its proof.

Added by the write (6 October 2026), marked `[write]`:

- **Remark 1.2 (`bsh:rem:oeis`)**: the OEIS entries quoted (next section);
  the `J = 0` case of Theorem 1.1 is exactly A238260's limit definition, so
  `b` is a closed form for that constant, and the write's value agrees with
  **all 105 digits** the entry prints (the placement record mentioned only
  the 20 digits of the entry's example line); a **Lambert form**
  `b = −1/(π w₀ √((1+w₀)(3+w₀)))`, `w₀ = W₀(−2e⁻²)` (A226775), with
  `r = 2 + w₀` (A256500) and `q = −2/(w₀(2+w₀))` as in A238258, with proof.
- **Proposition 2.2 (`bsh:prop:doubling`)**: `B_{n+1} ≥ 2B_n` for every
  `n ≥ 1`, from the two rook recurrences (one term dropped, and the
  vanishing `K(n,n) = 0`, `W(n,n) = 0`); so the onset `n_0` of Section 7 may
  be `1`.
- **Remark 7.2 (`bsh:rem:transseries`)**: Section 7 against the transseries
  volume
  (`Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/`),
  statement by statement. (a) **Instance**: with `n_1 = 1`, `N(y)` is the
  staircase of `p0:def:three-inverses`, and `p0:thm:staircase`(1) gives
  `N(y) = ⌈ν_𝒜(y)⌉` for `y ≥ 1` and every admissible interpolation.
  (b) **Analogue, not instance**: Theorem 7.1 (and the enclosures about the
  centres of Section 7.1) is a direct two-ceiling bracket about the root of
  a model that does not interpolate the counts; it shares the conclusion of
  `p0:thm:staircase`(2). (c) The "parity-branch" alternative has the shape of
  `p0:thm:staircase`(4) with `r = 2`; its enclosures are not proved
  (Question 7). (d) **Instance**: the Lambert centre is
  `p0:prop:factorial-core` with `κ_vol = 1`, `d_vol = log q − 1`. (e) **Formal
  instance after the change of variable `x = t(1+E)`**: the centres (34),
  (35) are the first two coefficients of `p0:thm:core-reversion` with
  `Λ_vol = A`, `h_vol(E) = (1+E)log(1+E) − E`; only formally (the ring
  contains `A⁻¹` and `log t`), only before the cosine term enters, and with
  the source's own remainders.
- Section 1.1 (`bsh:sec:provenance`: provenance, the sources as the write
  read them, what was checked, relation to the repository, collected
  non-claims, reading conventions), a label on Section 1 (`bsh:sec:main`),
  notes after the abstract and at the ends of Sections 8 and 9, Questions 6
  and 7 in Section 9, three bibliography entries (A238258, A256500,
  A226775).

## The OEIS entries (Remark 1.2)

Read on 6 October 2026 in the internal format; quoted verbatim.

- **A002465** (revision #95, 19 July 2026): "Number of ways to place n
  nonattacking bishops on an n X n board.", offset 0 (`a(0) = 1` prepended
  1 December 2024). Formulas:

      Asymptotic: a(n)/(n-1)! ~ 0.631266 * 3.08827^n. - _Vaclav Kotesovec_, Mar 23 2011
      The second constant is 2/(z*(2-z)) = 3.0882773047417401791158400820254..., where z is the root z=1.593624260040... of the equation exp(z)*(2-z)=2. - _Vaclav Kotesovec_, May 27 2011
      For constants see A238258 and A238260. - _Vaclav Kotesovec_, Feb 21 2014

  So `z = r`, the second constant is `q`, and the first formula is the
  leading term of Theorem 1.1 with `b`, `q` truncated to six digits. The
  write compared all 376 terms of the b-file (`0 ≤ n ≤ 375`) with the
  Stirling convolution (10), and `n ≤ 40`, `n = 100, 101, 200, 201, 374, 375`
  with the rook recurrences: all agree.
- **A238260** (revision #6, 12 September 2015): "Decimal expansion of a
  multiplicative constant related to A002465."; its only formula is "Equals
  lim n->infinity A002465(n) / ((n-1)! * A238258^n)."; example
  "0.63126687887411546797..."; 105 digits of data; a link to page 249 of
  Kotěšovec's book. No closed form. The source's `b` gives one; at 150
  digits it agrees with all 105 printed digits, and continues
  `…3354635 57942…` (the write prints 110 decimals, truncated, in Remark 1.2).
  (Corrected after the independent check of 7 October 2026: the printed
  digits end `…33546355` and the constant continues `79420…`; the first
  wording put the break one digit early.)
  **This is a closed form, not a correction. Nothing was submitted to the
  OEIS.**
- **A238258** (revision #10): `q`, as "lim n->infinity
  (A002465(n)/(n-1)!)^(1/n)" and "-2 / (LambertW(-2*exp(-2)) * (2 +
  LambertW(-2*exp(-2))))"; all 105 digits agree. **A256500** (revision #36)
  is `r` ("Decimal expansion of the positive solution to x =
  2*(1-exp(-x))."); **A226775** (revision #38) is `w₀ = W(−2e⁻²)`.

## What is not claimed

From the source, kept in the article (collected in Section 1.1):

- Fixed order only: no convergence of the formal series, no bounds uniform
  in `J`; every remainder constant and onset existential, no numerical value
  of `D_J` or of an onset.
- The exact enumeration, the base and the leading equivalent are prior;
  "a bounded comparison, not a claim of global historical priority"; the
  Arshon and Robinson full texts were not inspected; the period-two theorem
  of Chaiken–Hanusa–Zaslavsky (fixed `k ≥ 3`) "does not assert the diagonal
  expansion when k=n"; standard saddle-point methods and fixed-piece parity
  phenomena are prior.
- Decimal values and residuals are diagnostics, not interval certificates;
  finite exact agreement checks implementations and conventions, not the
  theorem; the order-4 receipt has no independent order-4 comparison.
- The cosine interpolation is a chosen model; no single-ceiling formula and
  no uniform `N(y) = t + o(1)` follow.
- PDF byte stability refers to the pinned toolchain.

The write adds: its independent checks are floating or finite; Remark 1.2
gives a closed form for an OEIS constant and corrects nothing; Remark 7.2
claims no novelty for any inversion.

## Further questions

Section 9 of the article (`bsh:sec:sources`) keeps the source's five
questions (certified constants and onsets; growth of `c_J^{(p)}` as
`J → ∞`; later parity terms; `k = αn + O(1)` bishops and rectangular boards;
the older literature) and adds, under Vladimir's standing rule of 4 October
2026:

6. **An independent order-4 check** (`bsh:q:order4`): the receipt's
   `c_4^{(0)} = 8.11568…`, `c_4^{(1)} = 6.77647…` are angular-only. The
   write's extrapolation of exact counts agrees (8.1154, 6.7763; floating).
   Missing: an independent exact computation.
7. **Parity-branch enclosures** (`bsh:q:branch`): the source's "separate
   parity-branch roots and parity-adjusted ceilings offer an alternative",
   and the code's formal branch centres, come with no proved enclosure.
   Sketch: Theorem 7.1's proof per class, then `p0:thm:staircase`(4).

A dated note there records, on Question 1, that Proposition 2.2 makes the
monotonicity onset explicit; on Question 5, that A002465 links Arshon's 1936
paper and cites Ahrens (1921), neither read, and that Kotěšovec's book was
unreachable at the source's address. **Nothing in the source was found to be
wrong.**

## Independent check of the write (7 October 2026)

An adversarial check made by the intake after the write (`e1db00e99`), with
its own code, after fetching again A002465 (#95) and its b-file, A238260 (#6),
A238258 (#10), A256500 (#36), A226775 (#38) and Santos's paper.

- **Remark 1.2**: quotations verbatim; `b`, `q`, `r`, `−w_0` agree with all 105
  printed digits of A238260, A238258, A256500, A226775 (160-digit
  evaluation); the 110 printed decimals of `b` are its truncation; the three
  Lambert identities hold; the Section 1 table is correctly rounded; all 376
  b-file terms agree with the rook recurrences and the convolution (8), the
  Stirling form (10) for `n ≤ 40` and six large `n`; direct cell enumeration
  gives `B_0, …, B_6`.
- **Proposition 2.2**: the proof holds; each inequality checked for
  `1 ≤ n < 120`; `B_{n+1}/B_n ≥ 4` for `1 ≤ n ≤ 374`.
- **Remark 7.2**: (a)–(d) hold; (e) the master equation re-derived identically
  from the Stirling form of `Φ_J` and `e_1 = h`,
  `e_2 = −((h²−h)/2 + 1/12 + c_1)/A` (SymPy).
- **Section 1.1**: archive facts, the 49 delivered label numbers, the scaled
  residuals, the `P_1, P_2, P_3` check at `n = 4000, 4001` and the order-4
  extrapolation (through three points: 8.115677, 6.776466) reproduced; the
  book's address again answers 404.
- **Corrected**: Section 1.1 described Santos's Theorem 6 as the colour
  convolution (8); it is the closed double Stirling sum (Santos's (5), at
  `k = n` our (10)), and (8) is the identity (6) of its proof (dated note).
  Above, the digit boundary of A238260 (dated note).

The check is recorded at the end of Section 9.

## Checks made at intake

- At placement (batch-109 dossier, 6 October 2026; Windows 11): the 25
  staged files were byte-identical to the archive, `MANIFEST.json` 26/26
  (`verify_package.py`). The dossier read the manuscript in full and found no
  error; independently, cell enumeration gave `B_0, …, B_7`, its own rook
  recurrence gave `B_10 = 15915225216`, and the scaled third-order residual
  at `n = 200, 201, 400, 401` was `−4.2222, −3.8389, −4.2422, −3.8555`
  against `c_3^{(0)} = −4.2624`, `c_3^{(1)} = −3.8723`. It ran the suite on
  copies (next sections): `reproduce.py all --with-diagnostics` PASS in about
  36 s, normal and `-O` identical, receipts equal to the references up to
  CRLF; `test_contracts.py --out` equal; order 4 with `--skip-oracle` (2 min)
  equal.
- At the write (6 October 2026; same machine; SymPy 1.14.0, mpmath 1.3.0):
  every proof rechecked (the monotonicity bracket for `r`, the board row
  lengths, the factorial identity of Proposition 2.1, the radius and tail
  bound of Lemma 3.1, `F(r,r) = re^r`, the Hessian and the normalization,
  the parity computation term by term with `E(U−V)² = 2/(r+1)`); the printed
  numerators `C_1, C_2, C_3` equal the shipped data; the parity difference
  and the parity-freeness of `c_1, c_2` exactly; all seven decimals of the
  Section 1 table correctly rounded; `P_1, P_2, P_3` against `H_{n,n/2+δ}` at
  `n = 4000, 4001`; the OEIS comparisons above; the scaled residual at
  `n = 300, 301, 374, 375` (`−4.2355, −3.8499, −4.2408, −3.8543`); the
  order-4 coefficients against a linear-in-`1/n` extrapolation of the
  `n⁴`-scaled residuals at `n = 300, 374` and `301, 375` (8.1154 and 6.7763
  against 8.11568 and 6.77647); `B_{n+1} ≥ 2B_n` on the b-file; the Lambert
  centre and `T` at `y = B_n`; the coefficients `e₁, e₂` of Remark 7.2(e)
  (SymPy). The suite rerun from the shipped files (Route B below).
- Sources read by the write: the OEIS entries above and A002465's b-file;
  Santos, JIS 28 (2025), Article 25.8.6 (Theorems 3, 4, 6: the recurrences
  (6)–(7) as printed, the Arshon–Kotěšovec formula with Santos's alternative
  proof, and the attribution of the period-two theorem to
  Chaiken–Hanusa–Zaslavsky); the transseries volume (labels named above).
  Not read: Kotěšovec's book (the source's address returned 404 on
  6 October 2026, behind a certificate chain this machine does not trust),
  Perott (1883), Chaiken–Hanusa–Zaslavsky, Finch, Arshon (1936), Robinson
  (1976), Ahrens.

## Relation to the repository

**Formal status.** No statement is formalized, and placement in the
collection confers no formal status. The staircase arithmetic that Remark
7.2(a) applies is formalized generically as `Fabius.staircase_ceil` in
`Analysis/FabiusFunction/Lean/FabiusFunction/StaircaseInversion.lean` (a
lemma about an arbitrary monotone function); nothing about `B_n` is.

**The transseries volume.** Remark 7.2: the threshold is a staircase
instance; Theorem 7.1 an analogue of `p0:thm:staircase`(2); the Lambert
centre an instance of `p0:prop:factorial-core`; the centres (34)–(35) a
formal instance of `p0:thm:core-reversion` after `x = t(1+E)`.

**Neighbouring reports** (under
`SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/`):

- `a201513-sparse-chess-placements`: the same regime (`n` pieces on the
  `n × n` board) for kings and knights (and wazirs, ferses). It neither
  contains nor implies these results: its general theorem
  (`scp:thm:general`) assumes a finite symmetric move set, which excludes the
  bishop, a rider; the growth (`n^{2n} e^{α_2}/n!` against `b Γ(n) qⁿ`) and
  the method (cluster expansion against a saddle point on an exact
  coefficient formula) differ. Its `B_n` is its carrier, not this count. This
  report is not a Part of it: it answers no question there.
- `a137432-maximum-density-kings` (batch 109): kings at maximum density, a
  different regime.
- `a330266-balanced-smirnov-poisson` also uses rook numbers (a rook-number
  inclusion–exclusion), for a different counting problem; no shared result.

A reciprocal note for `a201513-sparse-chess-placements` is proposed
separately; none is needed elsewhere.

**Stale claims.** Before batch 109 no file of the repository named A002465,
A238260 or A238258, and no report counted nonattacking bishops.

## Notation

A table at the end of Section 1.1 fixes the letters the manuscript reuses,
with the tempting false readings: `B_n`, `b`, `b_n` (and `b` as a summation
index in (10)); the boards `W`, `K` against the Hessian `K` (21) and
Lambert's `W` (33); the three `h` (`⌈n/2⌉`, `n/2 + δ`, the inverse shift);
`t` (the variable of `𝒬_a`, the Lambert centre) and `T`, `T_m`; `L_s`, `L`;
`A_{j,k}`, `A`; `ρ_a`, `ρ`, `ρ_J`; `M_δ`, `M_{a,b}`, `M_J`; `Ψ`, `Φ_J`, `G`;
`r` against `r_k` and `e_k` of (36); the diagonal label `d` (and `d` = `δ`
in the shipped JSON); `π(n)`, `δ`, `ε`; `N(y)` against the volume's
staircase. No symbol was renamed; the volume's colliding letters carry the
subscript "vol" in Remark 7.2. Against `a201513`: its `B_n`, `K_n` and
`N_n` are different objects.

## Labels

Every label carries the prefix `bsh:` (none existed in the repository). The
manuscript's 49 labels (`eq:` 36, `sec:` 8, `thm:` 2, `prop:` 1, `lem:` 1,
`app:` 1) were prefixed before anything cited them, and the 32 references to
them (21 `\eqref`, 11 `\ref`) updated. The write added 7: `bsh:sec:main`,
`bsh:rem:oeis`, `bsh:sec:provenance`, `bsh:prop:doubling`,
`bsh:rem:transseries`, `bsh:q:order4`, `bsh:q:branch`. The report has 56
labels; builds of the delivered text and of this one give all 49 delivered
labels the same numbers (aux files compared). The added statements are the
last of their sections, the added subsection follows the last delivered text
of Section 1, and the added displays are unnumbered.

## Files

```text
README.md                                          this guide (replaces the delivery README)
code-README.md                                     the delivered code guide (delivered code/README.md)
article.tex                                        the report (delivered Report219.tex; labels prefixed, [write] additions)
article.pdf                                        compiled report, 20 pages
code/coefficients.py                               angular coefficient engine and independent affine oracle (delivered code/)
code/counts.py                                     five exact count routes (delivered code/)
code/inverse.py                                    logarithmic coefficients, inverse checks, diagnostics (delivered code/)
code/reproduce.py                                  CLI and receipts (delivered code/)
code/test_contracts.py                             quick regression and guard tests (delivered code/)
code/compare_receipts.py                           semantic receipt comparison (delivered code/)
code/verify_package.py                             checks MANIFEST.json, not shipped (delivered at the root)
code/build_pdf.py                                  offline PDF builder (delivered at the root)
code/build_archive.py                              deterministic ZIP builder (delivered at the root)
data/coefficients_c0_c3.json                       exact c_0..c_3 at both parities (delivered code/)
data/amplitudes_P0_P3.json                         exact P_0..P_3 (delivered code/)
data/requirements.txt                              sympy==1.14.0, mpmath==1.3.0 (delivered code/)
data/toolchain.json                                reference build versions (delivered at the root)
data/reference_receipts-reproduction-coefficients.json  receipt (delivered reference_receipts/reproduction/)
data/reference_receipts-reproduction-counts.json        receipt (same)
data/reference_receipts-reproduction-diagnostics.json   receipt (same)
data/reference_receipts-reproduction-inverse.json       receipt (same)
data/reference_receipts-reproduction-manifest.json      receipt list and PASS status (same)
data/reference_receipts-contracts-contracts.json        receipt (delivered reference_receipts/contracts/)
data/reference_receipts-contracts-manifest.json         receipt list and PASS status (same)
data/reference_receipts-order4-coefficients.json        angular-only order-4 receipt (delivered reference_receipts/order4/)
data/reference_receipts-order4-manifest.json            receipt list and PASS status (same)
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to the delivery. `data/requirements.txt` is byte-identical to
a generic pin file already in the repository (blob `de9542d36`, for
example
`Algebra/SurrealNumbers/docs/surcomplex/gamma-and-zeta-functions/data/01-inverse-zeta-requirements.txt`);
it is shipped here so that this package reruns on its own.

**Not shipped**, recoverable from the arrival commit (next section):
`Report219.pdf` (the delivered 13-page PDF, 395,044 bytes); `MANIFEST.json`
(3,902 bytes, 26 entries, verified at placement; repository policy ships no
checksum manifests); and the delivery `README.md` (4,313 bytes), staged at
placement and replaced by this guide (summarized below).

**Delivered text that names the delivery layout or files not shipped.**
`code-README.md` ("Run these commands from this directory", `requirements.txt`
beside the code, the JSON data files by bare name),
`code/reproduce.py` (reads `coefficients_c0_c3.json` and
`amplitudes_P0_P3.json` from beside itself), `code/verify_package.py` and
`code/build_archive.py` (`MANIFEST.json`, the `Report219/` root, and the
delivered file set), `code/build_pdf.py` (`Report219.tex`), and Section 8 of
the article ("The accompanying archive is self-contained and contains this
TeX source, its PDF, …", "The archive README"). So no program runs under the
shipped names; use one of the routes below.

## Retrieving the delivered package

```sh
T=$(mktemp -d)
git -C /path/to/ProveIt show 60f54ea06:docs/incoming/Report219-reproducibility.zip > "$T/a.zip"
sha256sum "$T/a.zip"   # a0561728f630bd4761a8f3f8e85174ca08b55ebac10dd6321f392bceaa454cc7, 440,564 bytes
cd "$T" && unzip -q a.zip && cd Report219
python3 verify_package.py                 # PASS: 26 manifest entries verified
```

## Rerun the checks (on a scratch copy)

Python 3.10 or later with SymPy 1.14.0 and mpmath 1.3.0 (for example
`uv run --no-project --with sympy==1.14.0 --with mpmath==1.3.0 python …`).
Never run anything in the repository. Each `--out` must be a new directory.

**Route A, delivered layout** (as the delivery README gives it), from
`$T/Report219`:

```sh
python3 code/reproduce.py all --with-diagnostics --out "$T/normal"
python3 -O code/reproduce.py all --with-diagnostics --out "$T/optimized"
python3 code/compare_receipts.py "$T/normal" "$T/optimized"
python3 code/compare_receipts.py reference_receipts/reproduction "$T/normal"
python3 code/test_contracts.py --out "$T/contracts"
python3 code/reproduce.py coefficients --order 4 --skip-oracle --out "$T/order4"   # about 2 min
```

On Windows the receipts are written with CRLF line endings, so a byte
comparison (`diff -r`, as the delivery README gives it) fails while
`compare_receipts.py` (semantic JSON) passes; strip the carriage returns
before comparing bytes.

**Route B, from the shipped files** (tested at the write on Windows): rebuild
the delivered layout under the delivered names, then run Route A there.

```sh
R=/path/to/ProveIt/SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a002465-nonattacking-bishops
B=$(mktemp -d)/Report219; mkdir -p "$B/code" "$B"/reference_receipts/{contracts,order4,reproduction}; cd "$B"
cp "$R"/code/{build_archive,build_pdf,verify_package}.py "$R/data/toolchain.json" .
for f in coefficients compare_receipts counts inverse reproduce test_contracts; do cp "$R/code/$f.py" code/; done
cp "$R"/data/{amplitudes_P0_P3,coefficients_c0_c3}.json "$R/data/requirements.txt" code/
cp "$R/code-README.md" code/README.md
for d in contracts order4 reproduction; do for f in "$R"/data/reference_receipts-$d-*.json; do
  n=$(basename "$f"); cp "$f" "reference_receipts/$d/${n#reference_receipts-$d-}"; done; done
```

At the write every file of this layout was byte-identical to the archive
(without `Report219.tex`, the PDF, `MANIFEST.json` and the delivered README,
which the suite does not read; `verify_package.py` therefore needs Route A);
`reproduce.py all --with-diagnostics` gave PASS and `compare_receipts.py`
found identical semantic JSON in all five receipts against
`reference_receipts/reproduction` (byte equality after removing carriage
returns); `test_contracts.py --out` gave PASS with receipts equal after the
same removal. The run took about 4 minutes on the loaded machine (36 s at
placement). Use `py` where `python3` is not on the path. The PDF and archive
builders (POSIX, TeX Live) were not run.

## Build the PDF

pdfLaTeX (fontenc, lmodern, amsmath, amssymb, amsthm, mathtools, booktabs,
longtable, array, geometry, microtype, hyperref, enumitem, fancyhdr); the
bibliography is embedded.

```sh
B=$(mktemp -d); cp article.tex "$B/"; cd "$B"
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built this way with MiKTeX on 6 October 2026, and
rebuilt after the independent check of 7 October 2026 (label numbers
unchanged, aux files compared): 20
pages; no errors or warnings, no undefined references or citations, no
multiply defined labels, no duplicate PDF destinations, no overfull or
underfull boxes (the delivered text also builds without any, 13 pages). The
article keeps the delivered preamble lines that suppress PDF dates and
trailer identifiers; the delivered byte-identity claims apply to
`Report219.tex` under the delivering toolchain, not to this build.

## From the delivery README

The delivery README (replaced by this guide) described the package as "a
13-page self-contained mathematical article on OEIS A002465 and A238260";
stated the amplitude, the parity split and the two-ceiling inverse, and that
"Remainder constants and onsets are not numerically certified"; credited the
leading equivalent to Kotěšovec and the exact counting formulas and the base
as prior ("a bounded source comparison, not a global priority claim");
listed the contents; gave the rebuild commands of Route A with `/tmp`
output paths and byte `diff -r` comparisons; noted that "The extra order-4
receipt is angular-only, with no independent order-4 affine comparison";
described the PDF builder (TeX Live, local files only, never overwriting)
and the archive builder (single `Report219/` root, sorted entries, fixed
timestamps); and closed: "Exact agreement of different finite counting and
symbolic routes validates implementation and normalization. The article's
analytic proof establishes the asymptotic theorem."

## Rights

Repository contents are MIT-0. The article and this README quote OEIS
entries A002465, A238260, A238258, A256500 and A226775, and the receipts
contain computed (not copied) terms of A002465; OEIS content is published by
The OEIS Foundation Inc. under CC BY-SA 4.0 (https://oeis.org/LICENSE), and
quoted OEIS text remains under that licence. No third-party PDF or code is
shipped. Nothing was submitted to the OEIS.

## Provenance

- Sources cited by the manuscript: OEIS A002465 and A238260; Kotěšovec,
  *Non-attacking chess pieces*, 6th ed. (2013), pp. 242–253; Perott (1883);
  Santos, JIS 28 (2025); Chaiken, Hanusa and Zaslavsky (arXiv:1609.00853,
  arXiv:1405.3001); Finch (arXiv:2001.00578). Added by the write: OEIS
  A238258, A256500, A226775.
- Batch 109 of `docs/incoming`, bundle Report 219; arrival `60f54ea06`,
  placement `f7e9e5c2f`, written 6 October 2026. Single source, so no merge
  choices. The delivered `Report219.tex` is shipped as `article.tex`; the
  delivered programs and data as listed above.
