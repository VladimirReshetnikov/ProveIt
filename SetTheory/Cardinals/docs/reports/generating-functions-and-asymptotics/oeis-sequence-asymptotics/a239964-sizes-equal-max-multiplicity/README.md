# Partitions Whose Number of Distinct Sizes Equals the Maximum Multiplicity (OEIS A239964)

**`a(n) ~ (π H′(1)/(12√2)) n^{−3/2} e^{π√(2n/3)}` and
`P(D = M) = a(n)/p(n) ~ π H′(1)/√(6n)`, `H(z) = ∏_{j≥1}(1 − e^{−jz})`, with a
full Bessel/polynomial expansion to every fixed order from an exact
inclusion–exclusion diagonal transform, four radial constants (the fourth
involving the marked support sum `Σ_{j∈S} j²`), a Lambert `W_{−1}` inverse with
all fixed-order smooth corrections, and two-ceiling brackets for the integer
threshold**

A research article dated 4 October 2026 ("Report 196" of a session bundle),
built from one manuscript. Its author line and PDF author field read "Report
196": it names no person, tool or addressee. The package carries no
"prepared for private review" line, no e-mail address and no personal data.

| Source | Bundle report | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | Report 196 (batch 111) | `Report196_TeX_and_Reproducible_Code.zip` (14 files, no wrapper directory, 590,659 bytes, SHA-256 `441b3e6f3e3d…1917a2090048cd8`), arrival commit `60f54ea06`; main file `Report196.tex` (943 lines, 22 pp.) | none: the package names no ProveIt commit and no repository path | `d451ef3d8` (batch 111) | the whole report |

**Status:** AI-assisted, unrefereed, not formalized: no Lean or Rocq
declaration exists for any statement of this report.

## Trust boundaries

- **What is proved by hand.** The exact diagonal transform (Proposition 3.1),
  the uniform normalized expansion and summable remainder (Lemma 4.1,
  Proposition 4.2), the whole-circle Fourier bound (Lemma 5.1, Proposition
  5.2), the terminating monomial transfer with explicit connectors (Lemma
  6.1), the forward and probability expansions (Section 7) and the inversion
  (Section 8). No proof uses a computation.
- **What rests on computation.** Nothing in the proofs. The closed forms of
  `c_1, …, c_4` are derived by hand; the package re-derives the jets in
  exact `Fraction` arithmetic and SymPy.
- **What is diagnostic.** The decimals (printed as "illustrative
  approximations"), the agreement with the 1001 b-file terms and the smaller
  independent checks. Every remainder constant and threshold is existential.
- **What is prior.** The definition, the capped product (Manyama's OEIS
  formula), the modular identity and the Bessel saddle-transfer mechanism
  (Grabner–Knopfmacher–Wagner), Mutafchiev's limit law for the maximum
  multiplicity, Goh–Schmutz and Hwang on distinct sizes, and
  Ralaivaosaona's results on multiplicities ("substantial related prior").

## What it proves

`a(n)` (A239964) counts nonempty partitions with `D = M`, `D` the number of
distinct sizes and `M` the largest multiplicity (`a(0) = 0`). With
`A = π²/6`, `B = 2√A = π√(2/3)`, `C = π H′(1)/(12√2)`, `ν = n − 1/24`,
`τ = √(A/ν)`, `x = 2√(Aν)`. Statement and equation numbers are the delivered
ones.

- **Proposition 3.1 (`dmm:prop:transform`)**: `F(q)/P(q) = Σ_{S≠∅}
  (−1)^{|S|+1} (1 − q^s) U_S(q)`, `s = ΣS`,
  `U_S = q^{s|S|} ∏_{j∉S}(1 − (1 − q^s)q^j)` (3.5).
- **Theorem 1.1 (`dmm:thm:main`)**: for every fixed `R`,
  `a(n) = (2π)^{−1/2} Σ_{r≤R} c_r τ^{r+3/2} I_{−r−3/2}(x) + O_R(e^x τ^{R+3})`
  (1.6), equivalently with the terminating polynomials `Q_r` (1.8);
  `c_1 = H′(1)`, `c_2 = H‴(1)/4`, `c_3` (1.9); forward form (1.10)–(1.11)
  with `d_1 = √A c_2/c_1 − 3/B − B/48`.
- **Corollary 1.2 (`dmm:cor:prob`)**: `P{D = M} = c_1τ + (c_2 − c_1/A)τ² +
  (c_3 − 5c_2/(2A) + c_1/(4A²))τ³ + O(τ⁴)` (1.12).
- **(4.23) (`dmm:eq:c4`)**: `c_4` through `(H 𝓛_2)″(1)` and `H^{(3..7)}(1)`,
  `𝓛_2(z) = Σ j²/(e^{jz} − 1)`; **(7.5)** `d_2`.
- **Theorem 1.3 (`dmm:thm:inverseintro`)**, **Proposition 8.1
  (`dmm:prop:inverse`)**: eventual strict increase;
  `r(X) = [−(3/B) W_{−1}(−(B/3)(C/X)^{1/3})]²`; smooth roots
  `s_J = r + Σ_{k<J} δ_k r^{−k/2} + O(r^{−J/2})` with `δ_0, δ_1, δ_2` (8.6);
  `⌈u_J⌉ ≤ N(X) ≤ ⌈v_J⌉` (8.11), `v_J − u_J = O(r^{−J/2})`; the logarithmic
  form (8.12) and `N(X) = …² /B² + O(1)` (8.13).

Added by the write (7 October 2026), marked `[write]`:

- **Remark 1.4 (`dmm:rem:oeis`)**: the OEIS entry quoted (next section).
- **Section 1.2 (`dmm:sec:provenance`)**: provenance, the sources as the
  write read them, what was checked, relation to the repository, collected
  non-claims, a table of reading conventions.
- **Note after Corollary 1.2**: three of the printed decimals are rounded,
  not truncated (below); `c_4`, `d_2` and residuals.
- **Remark 8.2 (`dmm:rem:transseries`)**: Section 8 against the transseries
  volume
  (`Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/`),
  statement by statement. (a) **Instance**: for large `X`, `N(X)` is the
  staircase of `p0:def:three-inverses`; `p0:thm:staircase`(1) applies.
  (b) **Instance**: `r(X)` is `p0:thm:lambert-core`(3), case `b < 0`, after
  `X_vol = √r` (`a_vol = B`, `b_vol = −3`, `L_vol = log(X/C)`).
  (c) **Instance**: `e^{f_J(X_vol²)}` is exactly of exponential–power type, so
  Proposition 8.1 is `p0:thm:lambert-centered`(5) with `N = J`, followed by
  squaring; the volume's Bell recurrence gives the three forms of (8.6)
  (checked symbolically); `u_J`, `v_J` likewise. (d) **Analogues**: (8.11),
  Theorem 1.3 and (8.13) are two-ceiling brackets proved directly, analogues
  of `p0:thm:staircase`(2). (e) **Formal instance**: (8.12) is
  `p0:thm:flattening`(4) with `a_vol = 1`, `b_vol = −3`, `q_1 = B d_1` in the
  variables `y`, `L − K`, re-expanded about `L`.
- A note after the abstract and a note closing Section 10.

## The OEIS entry (Remark 1.4)

Read on 7 October 2026 in the internal format.

- **A239964** (revision #17, 13 March 2026; _Clark Kimberling_, 30 March
  2014): "Number of partitions of n such that (number of distinct parts) =
  maximal multiplicity of the parts.", offset 0; formula "G.f.:
  Sum_{i>=1} [z^i] ( Product_{j>=1} (1 + z * Sum_{k=1..i} q^(j*k)) -
  Product_{j>=1} (1 + z * Sum_{k=1..i-1} q^(j*k)) ). - _Seiichi Manyama_, Mar
  13 2026" (the article's (3.2)); b-file `0 ≤ n ≤ 1000` by Manyama;
  Kimberling's Mathematica program; example `a(8)`: "8, 611, 422, 332,
  3311, 32111". No asymptotic formula, no conjecture.
- The b-file fetched on 7 October 2026 is byte-identical to the shipped
  `data/b239964.txt` and `data/generated-exact_terms.txt` (SHA-256
  `e215b0baba64…7a2814b`). The write's own enumeration by multiplicity
  vectors agrees for all `n ≤ 60` (the package's stops at 45). Nothing was
  submitted to the OEIS.

## The decimals (note after Corollary 1.2)

The source prints five constants to 30 decimals with "…" and one to 20. The
write recomputed them at 50 digits (pentagonal series, `|m| ≤ 60`):

- `c_1`, `c_2` and `c_2/c_1 − 1/A = −0.47962261605811850894…` are
  truncations.
- `c_3`, `C` and `d_1` are rounded in the last printed place: the truncations
  are `c_3 = −1.184135136978472079040268115605…`,
  `C = 0.110804651091708424586159594536…`,
  `d_1 = −1.058427881640711235980815635656…` (next digits 97, 53, 95).
- Also `c_4 = 9.9438995003…`, `d_2 = −3.0655427849…` (truncated). Against
  the b-file, the relative error of (1.8) with `R = 3`, divided by `τ³`, is
  `12.57…, 14.06…, 14.70…, 15.06…` at `n = 250, 500, 750, 1000`, moving
  towards `c_4/c_1 = 16.61…`; the forward residual after `d_1`, `d_2`, times
  `n^{3/2}`, is `38.2…, 41.7…, 44.1…` at `n = 250, 500, 1000`. Numerical
  observations, not proofs.

## What is not claimed

From the source, kept in the article (collected in Section 1.2):

- No worldwide novelty, exhaustive coverage or absence of a more general
  prior result; the Mutafchiev text read was an author version; the full
  Goh–Schmutz and Hwang papers were not retrieved, so their scope is not
  excluded; no novelty about Ralaivaosaona's multiplicity regimes.
- Fixed order only: no convergence, no uniformity in the order, no numerical
  remainder constants or effective onset; the two ceilings need not
  coincide; no certified finite-`X` envelope; (8.13) has an `O(1)` error, not
  `o(1)`.
- (4.15) is not claimed to reduce to derivatives of `H` at higher order; the
  decimals are illustrative; finite agreement supplies no onset; the
  nonnegativity of `B_S` is a bound, not positivity of `U_S` or `F/P`.
- Determinism is a same-toolchain statement.

The write adds: its checks are floating, finite or symbolic computations;
Remark 8.2 claims no novelty for any inversion.

## Further questions

Section 10 (`dmm:sec:questions`) keeps the source's six questions (effective
errors and thresholds; higher coefficient structure; shifted and scaled
diagonals `D = M + h`; the conditional law of `D` given `D = M`; beyond every
fixed order; complete prior scope). A dated note records that nothing was
moved there or refuted under Vladimir's standing rule of 4 October 2026, and
that the b-file increases strictly for `9 ≤ n < 1000` (last non-increase
`a(9) = 5 < a(8) = 6`), which proves no onset. **No claim of the source was
found to be wrong or unproved**; three printed decimals are rounded rather
than truncated.

## Checks made at intake

- At placement (batch-111 dossier, 7 October 2026; Windows 11): the staged
  files byte-identical to a fresh extraction; the delivered suite reproduced
  its outputs on copies (failures only Windows artifacts).
- At the write (7 October 2026; same machine; Python 3.14.4, SymPy 1.14.0,
  mpmath 1.3.0): `MANIFEST.json` 13/13 and `SOURCE_MANIFEST.json` 7/7; every
  proof read line by line; SymPy re-derivation of `L_S` through `w³` for a
  general set (4.20 and the `w³` coefficient, `k` cancelling), `T_1..T_3`,
  the fourth jet (4.24), the one-site expansion, `Q_0..Q_2` from (1.7), the
  probability coefficients (1.12), the polynomials (6.5) (recurrence and
  trigonometric form), `d_1` and (7.5) from the substitution, the three
  forms of (8.6) and the vanishing of (8.7) through `z³`; the 333 subsets;
  the brute force to 60; the constants and residuals above. The delivered
  verifier rerun from the shipped files (route below), `--full1000`:
  `verification.json` and the terms byte-identical to the shipped records
  (about 3 minutes).
- Sources read by the write: the OEIS entry and b-file; the transseries
  volume (labels above). Not read: Mutafchiev, Goh–Schmutz, Hwang,
  Ralaivaosaona, Grabner–Knopfmacher–Wagner.

## Relation to the repository

**Formal status.** No statement is formalized, and placement in the
collection confers no formal status. The staircase arithmetic of Remark
8.2(a) is formalized generically as `Fabius.staircase_ceil` in
`Analysis/FabiusFunction/Lean/FabiusFunction/StaircaseInversion.lean`;
nothing about `a(n)` is.

**The transseries volume.** Remark 8.2, summarized above.

**Neighbouring reports** (under
`SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/`):
`a239950-maximal-schreier-supports` (batch 111: least part equal to the
number of distinct sizes, another statistic of the same occupancy product)
and `a373271-distinct-multiplicity-values` (batch 111: the number of
distinct multiplicity values). The batch-111 placement kept this report
apart from the latter because `D = M` is not an occupied-value functional and
no source cites another. No shared result, so no reciprocal note is proposed.

**Stale claims.** Before batch 111 no file of the repository named A239964.

## Notation

A table at the end of Section 1.2 fixes the letters the manuscript reuses,
with the tempting false readings: `A`, `B`, `B_S`; `C` and generic
constants; `c_r` and unrelated small constants; `d_j`, `d(s)`, `d_{k,n}`;
`D`, `M`, `M_J`; `G_{≤m}`, `G`, `G_m(v)`; `H`, `𝓛_2`; the three `L`; `Q_r`,
`Q_s^*`; `J_b`, `𝒥_r`, `𝒥_t`; `T`, `T_r`; `K`; `r`; `s`, `s_J`; `x`, `y`;
`h`, `ℓ`; `δ`; the threshold `X` against the volume's core variable;
`p(n)`, `p_1`, `p_2`, `P`, `𝒫_R`; `E_{i,j}`, `𝔼`. No symbol was renamed; the
volume's colliding letters carry the subscript "vol" in Remark 8.2.

## Labels

Every label carries the prefix `dmm:` (none existed in the repository). The
manuscript's 105 labels (`eq:` 85, `sec:` 10, `prop:` 4, `lem:` 3, `thm:` 2,
`cor:` 1) were prefixed before anything cited them, and the 62 references to
them (53 `\eqref`, 9 `\ref`) updated. The write added 3: `dmm:sec:provenance`,
`dmm:rem:oeis`, `dmm:rem:transseries`. The report has 108 labels; builds of
the delivered text and of this one give all 105 delivered labels the same
numbers (aux files compared). The added remarks are the last statements of
their sections, the added subsection follows the last delivered text of
Section 1, and the added displays are unnumbered.

## Files

```text
README.md                          this guide (replaces the delivery README)
article.tex                        the report (delivered Report196.tex; labels prefixed, [write] additions)
article.pdf                        compiled report, 26 pages
code/verify.py                     exact checks: capped DP (251 or 1001 terms), enumeration, subset identity, jets (delivered at the root)
code/symbolic_checks.py            Fraction jets for the cubic logarithm, c_4 integrand, d_2 (delivered at the root)
code/build.py                      deterministic PDF and package builder (delivered at the root)
code/guard_tests.py                guard and rebuild tests (delivered at the root)
data/b239964.txt                   OEIS b-file, n = 0..1000, downloaded 4 October 2026 (delivered data/)
data/generated-exact_terms.txt     recorded terms, n = 0..1000 (delivered generated/; byte-identical to the b-file)
data/generated-verification.json   recorded --full1000 verification (delivered generated/)
data/generated-guard_results.json  recorded guard results (same)
data/generated-BUILD_INFO.json     recorded build parameters (same)
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to the delivery.

**Not shipped**, recoverable from the arrival commit: `Report196.pdf` (the
delivered 22-page PDF, 417,137 bytes); the checksum manifests
`MANIFEST.json` (1,950 bytes, 13 entries) and `SOURCE_MANIFEST.json` (1,089
bytes, 7 entries), verified at the write (repository policy ships no
checksum manifests); and the delivery `README.txt` (7,771 bytes), staged at
placement as `README.md` and replaced by this guide (summarized below).

**Delivered text that names the delivery layout or files not shipped.** The
programs (`build.py` and `guard_tests.py` require `SOURCE_MANIFEST.json`,
`README.txt` and `Report196.tex` beside them; they write `generated/`), and
Section 9.3 of the article ("The companion archive contains … the rendered
PDF … a strict complete hash manifest", "The README specifies the
commands"). `verify.py` needs only `data/b239964.txt` beside it.

## Retrieving the delivered package

```sh
T=$(mktemp -d)
git -C /path/to/ProveIt show 60f54ea06:docs/incoming/Report196_TeX_and_Reproducible_Code.zip > "$T/a.zip"
sha256sum "$T/a.zip"   # 441b3e6f3e3d04cf840ec0bb1af6ee2d3d7781786421d43af1917a2090048cd8, 590,659 bytes
cd "$T" && unzip -q a.zip
```

In the extraction the delivered commands are those of its README
(`python3 -I -S -B verify.py [--full1000]`, `build.py`, `guard_tests.py`).

## Rerun the checks (on a scratch copy)

Python 3.9 or later, standard library only. Never run anything in the
repository.

```sh
R=/path/to/ProveIt/SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a239964-sizes-equal-max-multiplicity
B=$(mktemp -d); mkdir -p "$B/pkg/data"; cd "$B/pkg"
cp "$R"/code/*.py .; cp "$R/data/b239964.txt" data/
python -I -S -B verify.py --full1000 --output "$B/v.json" --terms-output "$B/t.txt"
cmp "$B/v.json" "$R/data/generated-verification.json"
cmp "$B/t.txt" "$R/data/generated-exact_terms.txt"
```

At the write both comparisons were silent (byte-identical) after about
3 minutes; without `--full1000` the run takes about 2 s, checks 251 terms
and so differs from the shipped record in its `capped_sliding_dp` block. Use
`py` where `python` is not on the path. The builder and the guard tests
(which need the delivered manifests, README and TeX) were not rerun by the
write; take them from the archive.

## Build the PDF

pdfLaTeX (fontenc, lmodern, microtype, geometry, amsmath, amssymb, amsthm,
mathtools, booktabs, array, xcolor, enumitem, fancyhdr, hyperref, and
longtable for the write's table); the bibliography is embedded.

```sh
B=$(mktemp -d); cp article.tex "$B/"; cd "$B"
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built this way with MiKTeX on 7 October 2026 (26
pages): no errors or warnings, no undefined references or citations, no
multiply defined labels, no duplicate PDF destinations, no overfull or
underfull boxes (the delivered text also builds without any, 22 pages).

## From the delivery README

The delivery README (replaced by this guide) stated the scope ("Finite exact
computations are checks, not a substitute for its analytic proof. No
convergence of the infinite Poincare expansion, exhaustive novelty search,
or exact finite-threshold inverse based solely on an asymptotic truncation
is claimed."); gave the commands and the safe-output rules; described the
capped sliding-window DP, the enumeration through 45, the 333-subset `B_S`
check through 55, the `Fraction` jets and the saddle-polynomial recurrence
through `m = 13`; recorded the b-file provenance (downloaded 4 October 2026,
1,001 rows, SHA-256 `e215b0ba…`) and Manyama's formula; described the two
manifests ("integrity checks, not signatures") and the deterministic build;
and the guard tests.

## Rights

Repository contents are MIT-0. The article and this README quote OEIS entry
A239964, and `data/b239964.txt` (with its byte-identical copy
`data/generated-exact_terms.txt`) is its b-file (Seiichi Manyama); OEIS
content is published by The OEIS Foundation Inc. under CC BY-SA 4.0
(https://oeis.org/LICENSE), and that content remains under that licence. No
third-party PDF is shipped. Nothing was submitted to the OEIS.

## Provenance

- Sources cited by the manuscript: OEIS A239964; Mutafchiev, Ramanujan J. 9
  (2005); Goh–Schmutz, JCTA 69 (1995); Hwang, JCTA 96 (2001);
  Ralaivaosaona, Ann. Comb. 16 (2012); Grabner–Knopfmacher–Wagner, CPC 23
  (2014). Nothing added by the write.
- Batch 111 of `docs/incoming`, bundle Report 196; arrival `60f54ea06`,
  placement `d451ef3d8`, written 7 October 2026. Single source, so no merge
  choices.
