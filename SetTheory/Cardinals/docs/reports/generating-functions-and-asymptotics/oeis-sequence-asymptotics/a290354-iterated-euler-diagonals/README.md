# Iterated Euler Diagonals

**OEIS A290353 and A290354: Kotěšovec's asymptotic form, the first logarithmic correction, and the logarithmic height crossover**

This is a research report built on 6 October 2026 (write batch 106) from
three manuscripts of one external research session, Reports 225, 226 and 228
of the session bundle of Reports 1–243, all dated 5 October 2026. They study
one object. Let `F_0(z) = z` and
`1 + F_{m+1}(z) = ∏_{d≥1} (1 − z^d)^{−[z^d]F_m(z)}`, the iterated Euler
transforms of `1 + x`. Then `A(n,m) = [z^n] F_m(z)` counts unlabeled rooted
trees with `n` leaves, all at level `m` (OEIS
[A290353](https://oeis.org/A290353)), and `a_n = A(n,n)` is
[A290354](https://oeis.org/A290354) (`1, 1, 2, 6, 30, 170, 1337, …`).
Throughout, `T = π/2`, `B = 1/2 − π/6 − π²/16 − (log 2)/6`, `β = n/m`, `P` is the
entire solution of `P(s+1) = e^{P(s)} − 1` whose inverse is the normalized Fatou
coordinate `Φ(w) = −2/w + (1/3) log w + O(w)`, and `h` is the density with
`P(s) = ∫_0^∞ e^{st} h(t) dt`.

- **Part I** (Report 225, the base): `P` is the Laplace transform of a positive
  measure with a smooth, strictly positive density `h`, and
  `a_n ~ c (2n/π)^n n^{−4/3}` with `c = T^{1/3} e^{−B} h(1) > 0` — the form
  that **Václav Kotěšovec stated as a conjecture on A290354** (Aug 14 2017,
  `c = 4.4923...`); the digits of `c` are **not certified** (floating value
  `4.4923299`). Also: proportional height for `β` in compact subsets of
  `(0,∞)`, fixed and square-root height shifts with the floor phase
  `e^{−{λn}/λ}`, and a Lambert-W inverse at exact sequence values.
- **Part II** (Report 226): the first correction
  `a_n = c (n/T)^n n^{−4/3} {1 + (−log²n/18 + A log n + C)/n + O(n^{−7/5})}`,
  with `A`, `C` exact in `h(1), h′(1), h″(1)` and the clock constant
  `κ = π³/96 + π²/12 − 13π/48 − 11/36 − G/6 − π log 2/24` (`G` Catalan's
  constant); the uniform correction for compact ratios; a sharpened inverse.
- **Part III** (Report 228): `A(n,m)/(2 T^{−n} m^{n−1}) → e^{−1/(3λ)}` when
  `m/(n log n) → λ ∈ (0,∞)`, with every fixed order in `1/(λ log n)` and
  coefficients `c_j = ρ_j − ζ(j)/(j 3^j)`, `ρ_j ∈ ℚ` (`c_2 = (9 − π²)/108`);
  `h(0) = 2`, an exact Hankel representation of `h` near zero, a smooth germ
  `t^{t/3} h(t)`; transfer to `(log m)^{−D} ≤ β ≤ B_0`; Kaneiwa's normalization;
  smooth height prescriptions.

| Source | Bundle report | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| *Diagonal and proportional height asymptotics for iterated Euler transforms* (author line "Report 225", 5 October 2026); the base | 225 | `Report225.zip` (676,600 bytes, 15 files; `src/report225.tex`, 639 lines, 16 pp.) | cites a139383 at `65969409c` | `47fc7a069` | Part I, Sections 1–11 |
| *First logarithmic correction for iterated Euler diagonals* (author line "Report 226", 5 October 2026) | 226 | `Report226.zip` (1,152,358 bytes, 23 files, 2 of them Report 225's source and PDF under `supporting/`, 8 byte copies of Report 225's code and data; `src/report226.tex`, 715 lines, 17 pp.) | none | `47fc7a069` | Part II, Sections 12–23 |
| *Logarithmic height crossover for iterated Euler transforms* (author line "Report 228", 5 October 2026) | 228 | `Report228.zip` (1,459,342 bytes, 19 files, 4 of them Reports 225 and 226 under `supporting/`; `src/report228.tex`, 729 lines, 17 pp.) | cites a139383 at `5fdc0d68a` | `47fc7a069` | Part III, Sections 24–36, plus the write's Section 37 |

All three archives arrived unchanged in `60f54ea06` ("Arrival: 177 research
archives from the session bundle of Reports 1-243") and survive there
(`git show 60f54ea06:docs/incoming/<archive> > <archive>`); the placement
commit `47fc7a069` (batch 106, cluster 106-EULERI) removed them from
`docs/incoming/`. Both pinned commits exist; the a139383 `article.tex` blob is
the same (`ab5014ec`) at both pins and at HEAD. The write is "Write batch 106
(a290354-iterated-euler-diagonals): new report, diagonals of iterated Euler
transforms".

**Status.** Unrefereed; not formalized; no statement has been checked by a
proof assistant. The manuscripts name no person, tool or addressee and do not
say whether AI assistance was used; their PDF author field is "Research
report". No "prepared for private review" wording. Every result, proof,
remark, question and limitation of the three manuscripts is printed.

## Why the Parts are in this order

Report 225 is the base (its `report225.tex` was staged as `article.tex`) and
is printed first: it constructs the analytic foundation (the nonautonomous
clock, the sectorial Fatou coordinate, the positive density `h`). Report 226
imports Part I's interface and refines it to the first correction; Report 228
imports Part I's coordinate and density and Part II's absolute derivative
estimates. Dependency order, which is also the order of writing.

**Embedded copies.** Report 226's `supporting/` and Report 228's `supporting/`
hold the sources and PDFs of Reports 225 and 226; all six files are
byte-identical to the standalone deliveries (SHA-256 at placement, `cmp` at
the write). They are printed once, as Parts I and II, and not shipped. Eight
code and data files of Report 226 are byte copies of Report 225's
(`code/{amplitude_diagnostic,coordinate_series,exact_euler,test_exact}.py`,
`data/{amplitude_diagnostic,amplitude_grid,exact414}.json`,
`sources/A290354_first22.json`; Report 226's ledger says "copied unchanged");
they were staged **once, from Report 225**, and are listed below under
Report 225's prefix. Report 228's `code/exact_euler.py` is a different file (a
fresh adaptation) and is shipped under its own prefix.

**Restatements.** Part II's Section 13 restates the Part I results it imports
(and repeats Part I's Corollary 6.2 with its proof); Part III's Section 25
restates Part I's coordinate and density and Part II's absolute estimates.
They are printed in full, with notes naming the Part I or Part II statement
behind each item, because nearly every display in them is cited later,
because Part II's states as interface items several estimates that Part I
proves only inside its proofs (the inverse-orbit bound, which is in Part I's
proof of Lemma 4.1, and the disk and neighbourhood forms of the tail and outer
bounds), and because Part III's contains material found nowhere else (its
`L¹` bound and its comparison with the iterated Bell report). (Corrected after
the independent check below; the write had said that each section contains
material found nowhere else, naming Part II's inverse-orbit bound.) The
intake dossier had suggested pointers instead, as a139383 did for its Part II.

## Files

The directory holds 33 files: 7 at the root, 13 in `code/`, 13 in `data/`.

**Report files**, written in the write: this guide, the merged article and its PDF.

```
README.md
article.pdf
article.tex
```

**Report 225, prefix `225-leading-`** (11 files): the source ledger; the
deterministic builder; the exact recurrence with an independent finite-product
check, the optimization-safe exact tests, the exact formal Fatou coefficients
(orders 0..12), the optional amplitude diagnostic (NumPy/SciPy); the builder's
receipt, the amplitude diagnostic and its parameter grid, the generated exact
diagonal fixture through `n = 414`, and the 22 displayed OEIS terms. The four
`code/225-leading-code-*.py` files and the four `data/225-leading-*` files
marked † are also, byte for byte, Report 226's `code/` and `data/`/`sources/`
files of the same names; they are shipped once.

```
225-leading-sources-SOURCE_LEDGER.md
code/225-leading-build.py
code/225-leading-code-amplitude_diagnostic.py    †
code/225-leading-code-coordinate_series.py       †
code/225-leading-code-exact_euler.py             †
code/225-leading-code-test_exact.py              †
data/225-leading-build_checks.json
data/225-leading-data-amplitude_diagnostic.json  †
data/225-leading-data-amplitude_grid.json        †
data/225-leading-data-exact414.json              †
data/225-leading-sources-A290354_first22.json    †
```

**Report 226, prefix `226-firstcorr-`** (9 files): the source ledger; the
builder; the SymPy clock identities (48 checks), the derivative diagnostic
(`h(1)`, `h′(1)`, `h″(1)`, uncertified), the guard tests; the receipt, the
code-validation summary, the derivative diagnostics, the symbolic checks.

```
226-firstcorr-sources-SOURCE_LEDGER.md
code/226-firstcorr-build.py
code/226-firstcorr-code-clock_checks.py
code/226-firstcorr-code-derivative_diagnostic.py
code/226-firstcorr-code-test_guards.py
data/226-firstcorr-build_checks.json
data/226-firstcorr-data-code_validation.json
data/226-firstcorr-data-derivative_diagnostics.json
data/226-firstcorr-data-symbolic_checks.json
```

**Report 228, prefix `228-logheight-`** (10 files): the code README and the
source ledger; the builder; its own exact recurrence, the rational endpoint
coefficient generator and finite inverse algebra, the reproduction driver;
the receipt, the pinned requirements (`mpmath==1.3.0`, `sympy==1.14.0`), the
generated crossover table (inlined in the article as Table 1) and the
reproduction record.

```
228-logheight-code-README.md
228-logheight-sources-SOURCE_LEDGER.md
code/228-logheight-build.py
code/228-logheight-code-exact_euler.py
code/228-logheight-code-finite_algebra.py
code/228-logheight-code-reproduce.py
data/228-logheight-build_checks.json
data/228-logheight-code-requirements.txt
data/228-logheight-results-crossover_table.tex
data/228-logheight-results-reproduction.json
```

**Not shipped** (all retrievable from `60f54ea06`): the three PDFs;
`report226.tex` and `report228.tex` (printed as Parts II and III) and the
delivery READMEs of Reports 226 and 228 (Report 225's was staged and is
replaced by this guide); the checksum manifests (`MANIFEST.sha256` of each,
`code/SHA256SUMS` of Report 228; verified at placement, 12/12, 20/20, 16/16
and 5/5; repository policy drops checksum manifests); the `supporting/`
copies; and Report 226's eight byte copies of Report 225's files (above).

## Labels and numbering

Label prefix **`ied:`** (none at HEAD before this report): Part I uses
`ied:lead:` (Report 225's 50 labels), Part II `ied:corr:` (Report 226's 65),
Part III `ied:log:` (Report 228's 77). The manuscripts share bare names:
`eq:constants` (all three), `eq:rec`, `eq:inverse`, `cor:inverse` (225 and
226), `eq:R` (225 and 228, for different objects: the subsidiary sum and the
ratio), `eq:density`, `eq:extract` (226 and 228); under the Part prefixes they
are distinct. The write added the three
Part labels; section and subsection labels for the unlabelled sections it
cites (17 in Part I, 15 in Part II, 6 in Part III, for example
`ied:lead:sec:further`, `ied:corr:sub:endpoint`, `ied:log:sub:polysmall`); the
front matter's `ied:sec:guide`, `ied:sec:status`, `ied:sec:oeis`,
`ied:sec:notation`, `ied:sec:provenance`, `ied:sec:trust`,
`ied:sec:neighbours`; and Section 37's `ied:sec:further`, the nine items
`ied:q:validated`, `ied:q:higher`, `ied:q:effective`, `ied:q:floorinverse`,
`ied:q:endpoint`, `ied:q:analytic`, `ied:q:polysmall`, `ied:q:other`,
`ied:q:ibd`, and the remarks `ied:rem:ibdnumbers`, `ied:rem:labelled`.
252 labels in all, all distinct.

| Part | Manuscript | Section here | Statement `k.j` | Equation `(k)` |
|---|---|---|---|---|
| I | Report 225 | `k` (1–11, unchanged) | `k.j` | `(k)` |
| II | Report 226 | `k + 11` (12–23) | `(k+11).j` | `(II.k)` |
| III | Report 228 | `k + 23` (24–36); 37 added | `(k+23).j` | `(III.k)` |

For example Report 226's Theorems 1.1, 1.2 and Corollary 10.1 are 12.1, 12.2
and 21.1; Report 228's Theorem 1.1, Lemma 3.1, Proposition 4.1, Theorems 5.1,
6.1, 8.1 and 11.2–11.3 are 24.1, 26.1, 27.1, 28.1, 29.1, 31.1 and 34.2–34.3;
its Table 1 keeps its number. A comparison of the build's `.aux` with separate
builds of the three delivered `.tex` files confirmed all 192 delivered labels
under these offsets and prefixes. The delivered READMEs, ledgers, code and
data use the manuscripts' own numbers.

## Notation

No delivered symbol was renamed. The front matter's "Notation across the three
Parts" lists every letter whose meaning changes, with the tempting false
readings, and each Part opens with a short reading-conventions table. The main
collisions: **`h`** (the density; the iteration height in `F_h`), **`K`**
(an integer entrance index in Parts I–II; Part III's constant
`K = (1 − γ + log(T/2))/3 − B`), **`κ`** (the clock constant of Parts II–III; a
small constant in Part I's `K ≤ κn`), **`ρ_j`** (Part II's `h^{(j)}(1)/h(1)`;
Part III's rational numbers, `ρ_2 = 1/12`), **`λ`** (Part I's `m = ⌊λn⌋`;
Part III's `m/(n log n) → λ`; a139383's `λ = m/n`), **`c`, `C`, `𝒞`** (the
amplitude; Part II's correction constant; the clocks `C_z`, `𝒞_z`; Part III's
`C_0 = 1 − γ − log 2`, Catalan's constant `𝒞` = Part II's `G`, the germ
`C(β)`), **`G`, `g`** (Part I's `G(u)`, `G_n(s) = F_n(T/(D_n − s))` versus
Part II's `G_n(s) = F_n(r e^{s/n})`; `g(w) = log(1+w)` versus Part III's germ
`g(t) = t^{t/3} h(t)`), **`L`** (the clock function; Part III's `log n`),
**`W`** (Lambert in Parts I–II; `P(−x)` in Part III), **`H`**, **`R`**,
**`Q`**, **`M`**, **`N`**, **`q`**, **`E`**, **`τ`**, **`X`**, **`y`**,
**`ℓ`**. Part II writes the array `b_{n,m}`.

## What the report claims

**Part I (Report 225).**
- Lemma 2.1 (subsidiary forcing), Lemma 2.2 (nonautonomous clock), Lemma 3.1
  (matching, constant `B`), Lemmas 3.2–3.3 (noncircular real entrance, Cauchy
  entrance), Lemma 4.1 (sectorial Fatou coordinate, entire `P`).
- Propositions 5.1–5.2, Lemma 5.3 (local limit, intermediate and outer
  angles); Proposition 6.1 (positive measure, full support, strict positivity
  via `(e^u − 1)ν = Σ_{k≥2} ν^{*k}/k!`), Corollary 6.2 (`h ∈ C^∞(0,∞)`).
- Theorem 1.1: `a_n ~ c (n/T)^n n^{−4/3}`, `c = T^{1/3} e^{−B} h(1) > 0`, with
  an absolutely convergent Fourier formula for `h(1)`.
- Theorem 8.1 (proportional height, compact `β`), Corollary 8.2 (ratio `e^k`;
  floor phase), Corollary 8.3 (Gaussian-shaped profile for `|k| ≤ C√n`; not a
  CLT), Corollary 9.1 (Lambert-W inverse, eventual rounding at exact values).
- Prior work credited: Kaneiwa 1980 (polynomiality in `r`, tangent/zigzag
  leading coefficient), Bechtloff Weising (algebraic), a139383 (labelled
  analogue).

**Part II (Report 226).**
- Lemma 14.1 (forcing through fifth scaled order), the clock functions `M`, `N`
  (Section 15) and `κ` in closed form, Lemma 16.1 (weighted fourth-power
  defect), Lemma 17.1 (finite Fatou expansion to `w²`, forced matching),
  Proposition 18.1 (local limit on a growing strip), thirtieth-derivative
  extraction (Section 19).
- Theorem 12.1: the first correction with `O(n^{−7/5})`; Theorem 12.2: the
  uniform correction `𝒬_β(d_m)/m`; Corollary 21.1: the inverse with error
  `O(X^{−7/5}/log X)`.

**Part III (Report 228).**
- Lemma 26.1 (finite Fatou expansions to every order, `a_1 = −1/36`,
  `a_2 = 1/540`, `a_3 = 1/7776`, `a_4 = −71/435456`), Proposition 27.1
  (`h(0) = 2`), Theorem 28.1 (Hankel representation), Theorem 29.1 and
  Corollary 29.2 (smooth germ; power-log series; `h` not `C¹` at 0),
  Proposition 30.1 (rational-plus-zeta coefficients, `ρ_2 … ρ_7`).
- Theorem 31.1 (transfer with explicit `β^{−30}` loss; logarithmic bands),
  Theorem 24.1 (the crossover, every fixed order), Section 33 (Kaneiwa:
  `K → K + 1`), Proposition 34.1 and Theorems 34.2–34.3 (inverses).
- Credits: Dudko–Sauzin, Prellberg/Mishna, Nagaev–Vakhtel, Kaneiwa, a139383.

**Added by the write** (all marked `[write]`, dated 6 October 2026): the front
matter (including the OEIS entries as read on 5 October 2026 and the
classification of the inverses); dated notes marking what later Parts extend
or answer; Section 37 (further questions); **Remark 37.1** (numerical
agreement of `2^{1/3} h(1)` with a139383's `I(1)`); **Remark 37.2** with its
proof, a *conditional* consequence for the labelled array: if
`I(β) = β 2^{β/3} h(β)` for small `β` and a139383's leading form
`H(n,m) ~ (n−1)! 2^{−n} m^n m^{−β/3} I(β)` holds on logarithmic bands, then
`H(n,m)/(n! m^{n−1} 2^{1−n}) → e^{−1/(3λ)}` when `m/(n log n) → λ`, with the
`1/L` coefficient `(1 − γ)/3` and the same `c_j`; exact values for
`n = 20, 40, 80` behave as predicted (uncertified).

**The inverses.** Parts I and II start from `X log(X/T) = Y`, the factorial
core `p0:prop:factorial-core` (`κ = 1`, `d = −log T`) of the transseries volume
`Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/transseries_and_inversion.tex`,
whose solution is `X = Y/W(Y/T)`. Their corrections and the rounding at exact
values are proved directly; they parallel `p0:thm:perturbed-inversion` and
`p0:thm:staircase`(3) but are **not instances** (the perturbation is not a
small analytic one; the smooth root is not an admissible interpolation).
Part III's inverses have **no Lambert W**: a linear core perturbed by a
smooth germ, reverted by Taylor's theorem (an analogue, not an instance, of
`p0:thm:perturbed-inversion`); its rounded prescriptions are not instances of
`p0:thm:staircase`. No manuscript claims novelty for inversion mechanics.

## What the report does not claim

Every limitation is printed in place. In short: no certified decimal of `c`,
`h(1)`, `h′(1)`, `h″(1)` (`c ≈ 4.4923` "agrees with Kotesovec's conjecture
only numerically"); no effective onset or finite-`n` bound; no all-orders
theorem (Part II's leading coefficient `(−1/18)^r/r!` of higher corrections is
conditional); no uniformity as `β → ∞`, and toward `β → 0` only Part III's
leading-order transfer on logarithmic bands; no discrete monotonicity, least
height or exact integer-height recovery; no threshold for a general input
between consecutive terms; no convergence of any infinite formal series; no
analyticity of the germ at zero; the Gaussian height profile is not a CLT; no
worldwide priority for parabolic-coordinate methods or the universal endpoint
calculus (Prellberg, Dudko–Sauzin, Nagaev–Vakhtel credited). The amplitude
relation with a139383 is a conjecture. **All companions**: finite exact checks
prove no asymptotic remainder; floating diagnostics carry no error control.

## Further questions, and the standing rule

Part I's Section 11, Part II's Section 23 and Part III's Section 36 are the
manuscripts' own; Section 37 collects them (Vladimir's standing rule of
4 October 2026), with sources, sketches and what is missing:

1. **validated constants** `c`, `h(1)`, `h′(1)`, `h″(1)` (all Parts);
2. **corrections beyond the first and an all-orders theorem**, including
   Part II's conditional leading coefficient `(−1/18)^r/r!` (all Parts);
3. **effective constants, onsets, certified thresholds**, least heights (all);
4. **inverses for `A(n,⌊λn⌋)`** with the floor phase (Part I);
5. **`n/m → ∞`** and the large-argument behaviour of `h`; corrections on
   shrinking bands (all);
6. **real analyticity of `h` on `(0,∞)`** (known on some `(0,ε)` by Part III's
   Theorem 28.1) and analyticity/summability of the germ at zero (Parts I, III);
7. **polynomially small ratios** and the transition to Kaneiwa's fixed-degree
   regime (all);
8. **other arrays and initial functions** (all);
9. **the identity `I(β) = β 2^{β/3} h(β)`** with a139383's Part II amplitude —
   shared with a139383 (Part III's Section 25; consequences: real analyticity
   of `h`, and the amplitude half of a139383's open endpoint `λ → ∞`).

**Answered inside the merge**, with dated notes at the questions: Part I's
"Higher corrections to the diagonal" at first order (Part II); Part I's
"Other height scales and the density" and Part II's "Endpoint height regimes"
for the expansion of `h` at zero and the side `n/m → 0` on logarithmic bands
(Part III). **Nothing in the three manuscripts was found to be wrong**, and
no claim was refuted.

**Independent check of the write (6 October 2026).** An adversarial check
made by the intake after the write (`84fc1aaed`) re-pulled A290354 (live
revision #26, Jun 21 2018) and A290353 (#28) and found every quoted line
character for character. The date "Aug 14 2017" that the write gives the
conjecture is not the date of the revision read but that of Kotěšovec's
revision #23, which added the formula line; it is correct. The check
recomputed `a_n` exactly (equal to the b-file for `n ≤ 40`;
`a_40 (T/40)^40 40^{4/3} = 4.6013347`), confirmed that Theorem 1.1 is exactly
the conjectured form and the rows `A(2,m)`, `A(3,m)`, `A(4,m)` for `m ≤ 12`.
It re-derived Remark 37.2, found it labelled conditional wherever it appears
(and not listed as proved in the status table), and reproduced its table to
every printed digit from an own exact computation of `H(n,m)`; extended to
`n = 160` it gives `R_lab = 0.73782182` at `λ = 1` (`m = 812`; distance
`0.0213` to the limit, `0.0014` after the `K_lab` term) and `0.54374893` at
`λ = 0.5` (`m = 406`; `0.0303`, `0.0018`). It evaluated the closed form of `κ`
to 35 digits (`−0.25434816985107480385506489650373339`) and matched it against
an independent quadrature of (II.23) to `5·10⁻²⁸`; recomputed `h(1)` (above);
and confirmed the classification of the inverses (factorial core and Lambert
core with `a = b = 1` instances; corrections, rounding and Part III's
reversion and prescriptions not). No mathematical error was found. Two
wordings are corrected, each with a dated note keeping the first wording:
the front matter's justification of the printed restatements (twice; likewise
the README above) overstated Part II's novelty, since its inverse-orbit bound
is in Part I's proof of Lemma 4.1; and the note after Part II's Section 13 now
flags the neighbourhood form of the outer bound (Lemma 5.3), as it already
flagged the disk form of the tail bound (Proposition 5.2), as proved only
inside Part I's proofs. Added: the name `L = log(Y/T)` of the Lambert-core
instance, and the independent `h(1)` and `c` (front matter, Remark 37.1). The
record is a dated note at the end of Section 37.

## Relation to neighbouring reports

- **`a139383-iterated-bell-diagonals`** (labels `ibd:`), the labelled
  analogue `H(n,m) = n![z^n](e^z − 1)^{∘m}` (A139383, A261280), by the same
  parabolic map without subsidiary forcing. No theorem is shared and neither
  report answers a question of the other (Part I: the labelled theorem
  "cannot be directly transferred"). They share the normalized orbit:
  `Ψ_IBD = −Φ + (log 2)/3`, and the unproved relation
  `I(β) = β 2^{β/3} h(β)`, which agrees to eight significant digits at `β = 1`
  (`2^{1/3} h(1) = 2.2862647816` against a139383's exploratory
  `I(1) = 2.2862647847 … 2.2862647982`; both uncertified). The independent
  check below evaluated Part I's constant integral (6) anew (four values of `σ`,
  Gauss–Legendre quadrature to `|u| = 4·10⁴` with an integration-by-parts
  tail; uncertified): `h(1) = 1.814609559835`, `2^{1/3} h(1) = 2.2862647818`,
  `c = 4.4923298971`; the shipped diagnostic is low by `1.6·10⁻¹⁰` (its
  vertical tail is cut at `|u| = 3000`), and the comparison is unchanged
  (differences `2.9·10⁻⁹ … 1.65·10⁻⁸`, eight significant digits). A reciprocal note
  for a139383 is proposed in the write's record (not applied here).
- No other report treats A290353 or A290354 (searched 6 October 2026; A290354
  occurs elsewhere only in a cross-reference line of a139383's OEIS data). The
  batch-106 reports `a252782-diagonal-euler-transforms` (one Euler transform
  with weights `j^n`) and `a005121-strict-partition-chains` (a depth sum of the
  labelled array) share only words with this one.
- The transseries volume `Transseries_And_Inversion` supplies the factorial
  core of which the leading inverses are instances (above).

## Relation to formal projects

Placement in the collection confers no formal status, and no statement of this
report is formalized: no Lean or Rocq file in the repository treats these
sequences (searched 6 October 2026).

## Delivery names, renames and discrepancies

- Every delivered file keeps its bytes (the 32 staged files were checked
  against the pristine extraction from `60f54ea06` at the write: 0
  differences; `article.tex` and this README then replaced the two staged base
  files). Only names changed (tables at the end). The delivered code, ledgers
  and receipts use delivery paths (`src/report22N.tex`, `code/…`, `data/…`,
  `sources/…`, `results/…`, `supporting/…`, `MANIFEST.sha256`,
  `code/SHA256SUMS`, `code/requirements.txt`, `Report22N.pdf`), which are
  shipped under other names or not at all; the receipts record SHA-256 values
  of unshipped PDFs and manifests.
- **Closed inventories: none of the builders runs in this directory.** Each
  checks its `MANIFEST.sha256` and its delivery layout; Report 226's builder
  and guard tests also need the eight Report 225 files beside them, and
  Report 228's builder needs `supporting/`. Rerun from the archive (below).
- `228-logheight-code-README.md` says "`requirements.txt`" and
  `code/requirements.txt`; the file is shipped as
  `data/228-logheight-code-requirements.txt`. The same blob (`mpmath==1.3.0`,
  `sympy==1.14.0`) is shipped elsewhere in the collection.
- The two later ledgers list SHA-256 values of the `supporting/` files, which
  are not shipped (they are Parts I and II); Report 226's ledger names the
  eight files "copied unchanged", shipped here once under Report 225's prefix.
- The three builders and Report 225's delivered README (replaced by this
  guide) use example paths under `/tmp` or the Debian TeX tree
  `/usr/share/texlive`; use a scratch directory outside the repository.
- Part III's `\input{crossover_table.tex}` is inlined in the article (the
  table text byte for byte; its two comment lines kept as comments).
- Report 225's ledger records that the A290354 b-file could not be retrieved
  (HTTP 403); the fixture through `n = 414` is generated data, and only the 22
  displayed terms are an external comparison. The live entry's b-file covers
  `n = 0..414`; the write did not compare it either.

## Rerunning the checks

Run on a copy in a scratch directory, never in this directory. Recreate the
delivered layout from the arrival commit:

```
git show 60f54ea06:docs/incoming/Report225.zip > r225.zip
git show 60f54ea06:docs/incoming/Report226.zip > r226.zip
git show 60f54ea06:docs/incoming/Report228.zip > r228.zip
mkdir x225 x226 x228 && unzip -q r225.zip -d x225 && unzip -q r226.zip -d x226 && unzip -q r228.zip -d x228
cd x225/Report225
python -B code/exact_euler.py --max-index 20
python -B code/coordinate_series.py --order 9
PYTHONINTMAXSTRDIGITS=640 python -B code/test_exact.py --cap 640
cd ../../x226/Report226
uv run --no-project --with sympy==1.14.0 python -B code/clock_checks.py
python -B code/test_guards.py
cd ../../x228/Report228
PYTHONINTMAXSTRDIGITS=640 uv run --no-project --with sympy==1.14.0 --with mpmath==1.3.0 python -B code/reproduce.py --check --output-dir <abs>/out228
```

`<abs>` must be an absolute directory outside the bundle that does not exist
beforehand. The exact code needs only the Python standard library (3.11 or
later); Report 226's clock checks need SymPy 1.14.0, Report 228's reproduction
SymPy and mpmath 1.3.0; the optional amplitude and derivative diagnostics
need NumPy and SciPy. The `build.py` scripts need the recorded TeX Live
pdfTeX 1.40.26 for byte-identical PDFs and were not run.

Results: at placement (5 October 2026, Python 3.14.4, Windows, on copies,
recorded in the batch-106 dossier) Report 225 `test_exact.py --cap 640`
passed (8.5 min under load; fixture through 414 and the 22 OEIS terms) and
`coordinate_series.py --order 9` ran; Report 226 `clock_checks.py`
regenerated `data/symbolic_checks.json` (JSON-equal) and `test_guards.py`
passed; Report 228 `reproduce.py --check` regenerated both result files byte
for byte. At the write (fresh copies, Windows) `exact_euler.py --max-index 20`
and `coordinate_series.py --order 9` ran (`a_4 = −71/435456`),
`clock_checks.py` reproduced the symbolic record (JSON-equal, 7 s),
`test_guards.py` passed (1 s), and `reproduce.py --check` reproduced
`reproduction.json` and `crossover_table.tex` byte for byte (4 s; SHA-256
`6d9f70ee…`). The three delivered `.tex` files compile with MiKTeX pdfLaTeX to
16, 17 and 17 pages; their only warnings are duplicate font-map entries from
their `\pdfmapfile` lines.

## Rights

Repository contents are MIT-0.
`data/225-leading-sources-A290354_first22.json` holds the 22 displayed terms
of A290354, and the test files compare against them; OEIS data are available
under CC BY-SA 4.0 ([OEIS license](https://oeis.org/LICENSE)). All other
counts are recomputed from the recurrence. The OEIS entries are credited for
the sequences (Alois P. Heinz), Václav Kotěšovec for the A290354 conjecture,
and Kaneiwa, Bechtloff Weising, Dudko–Sauzin, Prellberg–Mishna and
Nagaev–Vakhtel as the manuscripts cite them. Nothing was submitted to the
OEIS.

## Build

```
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

pdfLaTeX (MiKTeX), in a scratch copy; commit only `article.pdf`. The build
(69 pages after the independent check, 67 at the write: title, abstract and
contents 1–3, front matter 4–11, Part I 12–28, Part II 29–46, Part III 47–64,
Section 37 and references 65–69): no errors, no
undefined or multiply defined references or citations, no duplicate
destinations, no overfull or underfull boxes. The log carries two "Infinite
glue shrinkage found in box being split" messages from the two front-matter
longtables breaking across pages.

## Delivered path → shipped path

Report 225 (`225-leading-`; delivered under `Report225/`):

| Delivered | Shipped |
|---|---|
| `src/report225.tex` | `article.tex` (Part I) |
| `README.md` | replaced by this guide |
| `build.py`, `build_checks.json` | `code/225-leading-build.py`, `data/225-leading-build_checks.json` |
| `code/<name>.py` | `code/225-leading-code-<name>.py` |
| `data/<name>.json` | `data/225-leading-data-<name>.json` |
| `sources/A290354_first22.json` | `data/225-leading-sources-A290354_first22.json` |
| `sources/SOURCE_LEDGER.md` | `225-leading-sources-SOURCE_LEDGER.md` |
| `Report225.pdf`, `MANIFEST.sha256` | not shipped |

Report 226 (`226-firstcorr-`; delivered under `Report226/`):

| Delivered | Shipped |
|---|---|
| `src/report226.tex` | not shipped; printed as Part II of `article.tex` |
| `build.py`, `build_checks.json` | `code/226-firstcorr-build.py`, `data/226-firstcorr-build_checks.json` |
| `code/clock_checks.py`, `code/derivative_diagnostic.py`, `code/test_guards.py` | `code/226-firstcorr-code-<name>.py` |
| `data/code_validation.json`, `data/derivative_diagnostics.json`, `data/symbolic_checks.json` | `data/226-firstcorr-data-<name>.json` |
| `sources/SOURCE_LEDGER.md` | `226-firstcorr-sources-SOURCE_LEDGER.md` |
| `code/{amplitude_diagnostic,coordinate_series,exact_euler,test_exact}.py`, `data/{amplitude_diagnostic,amplitude_grid,exact414}.json`, `sources/A290354_first22.json` | byte copies of Report 225's; shipped once, as `225-leading-*` |
| `supporting/report225.tex`, `supporting/Report225.pdf` | byte copies of Report 225; not shipped |
| `README.md`, `Report226.pdf`, `MANIFEST.sha256` | not shipped |

Report 228 (`228-logheight-`; delivered under `Report228/`):

| Delivered | Shipped |
|---|---|
| `src/report228.tex` | not shipped; printed as Part III of `article.tex` |
| `build.py`, `build_checks.json` | `code/228-logheight-build.py`, `data/228-logheight-build_checks.json` |
| `code/exact_euler.py`, `code/finite_algebra.py`, `code/reproduce.py` | `code/228-logheight-code-<name>.py` |
| `code/README.md`, `code/requirements.txt` | `228-logheight-code-README.md`, `data/228-logheight-code-requirements.txt` |
| `results/crossover_table.tex`, `results/reproduction.json` | `data/228-logheight-results-<name>` |
| `sources/SOURCE_LEDGER.md` | `228-logheight-sources-SOURCE_LEDGER.md` |
| `supporting/` (4 files) | byte copies of Reports 225 and 226; not shipped |
| `README.md`, `Report228.pdf`, `MANIFEST.sha256`, `code/SHA256SUMS` | not shipped |

## Provenance

Three manuscripts (bundle Reports 225, 226, 228) → one report; base 225,
printed as Part I. Arrival `60f54ea06`, placement `47fc7a069`, write batch
106 (6 October 2026). Reports 225 and 228 cite a139383 at `65969409c` and
`5fdc0d68a`; Report 226 pins nothing. Merge choices (dependency order with the
base first, restatement sections printed in full with pointer notes, embedded
copies printed once, the merged bibliography with renamed keys and Reports 225
and 226 pointing to Parts I and II, the inlined table) are listed in the
article's front matter, "Provenance and merge decisions".
