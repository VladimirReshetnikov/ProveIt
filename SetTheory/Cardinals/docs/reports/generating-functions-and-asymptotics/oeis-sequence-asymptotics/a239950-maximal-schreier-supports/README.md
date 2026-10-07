# Partitions on Maximal Schreier Supports (OEIS A239950)

**`p_n = K n^{-3/4} e^{2√(Sn)} (Σ_{j≤R} c_j n^{-j/2} + O_R(n^{-(R+1)/2}))` for
every fixed `R`, where `p_n` counts partitions of `n` whose least part equals
the number of distinct part sizes, `S = Li₂(2/3) − Li₂(1/3) + log(3/2) log 2`,
`K = S^{1/4}/(2√(6π(1−a)))`, `a = log(3/2)`; `c_1 < 0` and `c_2` explicit; a
Gaussian least-part law; a Lambert `W_{−1}` inverse with two-ceiling
brackets to every fixed order; and a rational certificate that `F(q)/q` has
a real zero in `(−4/5, −3/4)`, so it is no finite eta quotient**

A research article dated 4 October 2026 ("Report 195" of a session bundle),
built from one manuscript. Its title page and PDF author field read
"Prepared for Vladimir"; it names no tool and no other person. The package
carries no "prepared for private review" line, no e-mail address and no
personal data.

| Source | Bundle report | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | Report 195 (batch 111) | `Report195_TeX_and_Reproducible_Code.zip` (25 files, no wrapper directory, 687,972 bytes, SHA-256 `561bd3b3a4ce…a968e68412c0122`), arrival commit `60f54ea06`; main file `Report195.tex` (1084 lines, 27 pp.) | none: the package names no ProveIt commit and no repository path | `d451ef3d8` (batch 111) | the whole report |

**Status:** AI-assisted, unrefereed, not formalized: no Lean or Rocq
declaration exists for any statement of this report.

## Trust boundaries

- **What is proved by hand.** Everything in the article: the exact
  generating function, global radial localization (Lemmas 3.1–3.2), the
  full-torus Fourier bounds (Lemmas 5.1–5.2) and the bivariate lattice limit
  (Theorem 5.3), the leading equivalent (Section 6), the three-variable saddle
  expansion to every fixed order (Section 7), the sign of `c` (Section 8.1),
  the least-part law (Theorem 9.1), the inverses (Section 10) and the tail
  bound that turns two finite rational evaluations into Proposition 11.1.
- **What rests on computation.** The two Horner inequalities (11.5)–(11.6)
  (exact rational arithmetic over the regenerated counts), and the explicit
  values of `b_1` and `b_2` as finite Wick contractions ((8.4), (8.7)–(8.8),
  (8.17)–(8.18)), which
  the article states and the optional SymPy programs evaluate. The write
  re-verified (8.7)–(8.8) and the radial pieces symbolically, and tested
  `c_2` numerically against the exact counts; it did not redo the
  degree-twelve contraction (8.17).
- **What is diagnostic.** The finite agreement with the OEIS display, the
  write's decimals and residuals, and the Euler exponents of the shipped
  data. Remainder constants and thresholds are existential.
- **What is prior.** The Schreier terminology (Chu–Vasseur), Schreier-type
  sets and multisets (Beanland–Chu; Chu et al.), the occupancy product
  (Hwang–Yeh), limit theorems for distinct part sizes and summands
  (Goh–Schmutz; Hwang), general partition-statistics schemes
  (Grabner–Knopfmacher–Wagner) and related exact enumeration (Archibald et
  al.). The source claims no novelty of methods.

## What it proves

`p_n` (A239950) counts partitions `λ ⊢ n` with `min λ = |supp λ|`
(`p_0 = 0`); equivalently, positive multiplicities on a maximal Schreier set,
counted by total size. With `a = log(3/2)`, `S`, `D = 1/√(6(1−a))`,
`K = D S^{1/4}/(2√π)`, `V = 2a − 1/2`, `κ = 3(1−a)/V`, `W = 2S − a²κ`,
`κ_eff = 2Sκ/W`. Statement and equation numbers are the delivered ones.

- **Theorem 1.1 (`mss:thm:main`)**: the expansion above for every fixed `R`,
  `c_1 = c = B_*√S − 3/(16√S) < 0`, `B_* = −(26a²−82a+29)/(144(a−1)²)`;
  every `c_j ∈ Q(a, √S)` (Corollary 7.1, `mss:cor:field`).
- **(8.13)–(8.14) (`mss:eq:secondclosed`, `mss:eq:secondexpansion`)**:
  `c_2 = S B_** − (15/16)B_* − 15/(512S)` with
  `B_** = (676a⁴+3416a³−10200a²+22172a−7559)/(41472(a−1)⁴)`, remainder
  `O(n^{−3/2})`.
- **Theorem 1.2 (`mss:thm:consequences`)** and **Theorem 9.1
  (`mss:thm:clt`)**: the least part `M_n` satisfies
  `√(tκ_eff)(M_n − a/t) ⇒ N(0,1)`, `t = √(S/n)`, with a local law on bounded
  windows; `p_n` is eventually strictly increasing; `N(Y) = min{n : p_n ≥ Y}`
  lies between two ceilings about `r(Y) − c/√S`, where
  `r(Y) = [−(3/(4√S)) W_{−1}(−(4√S/3)(K/Y)^{2/3})]²`.
- **Theorem 10.1 (`mss:thm:inverseall`)**: two-ceiling brackets of width
  `O(r^{−J/2})` about `T_J(r) = r + Σ_{k<J} δ_k r^{−k/2}`, `δ_k ∈ Q(a, √S)`,
  `δ_0 = −c_1/√S`, `δ_1 = (3δ_0/4 − ℓ_2)/√S`.
- **Proposition 11.1 (`mss:prop:zero`)**: `F(q)/q` has a real zero in
  `(−4/5, −3/4)`; hence it is not a finite eta quotient (nor any product
  holomorphic and nonvanishing in the disk).

Added by the write (7 October 2026), marked `[write]`:

- **Remark 1.3 (`mss:rem:oeis`)**: the OEIS entry quoted (next section).
- **Section 1.2 (`mss:sec:provenance`)**: provenance, the sources as the
  write read them, what was checked, relation to the repository, collected
  non-claims, a table of reading conventions.
- **Note at the end of Section 8**: truncated decimals of the constants, and
  the residuals that confirm `c` and `c_2` numerically.
- **Remark 10.2 (`mss:rem:transseries`)**: Section 10 against the transseries
  volume
  (`Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/`),
  statement by statement. (a) **Instance**: for large `Y`, `N(Y)` is the
  staircase of `p0:def:three-inverses`, so `p0:thm:staircase`(1) applies.
  (b) **Instance**: `r(Y)` is `p0:thm:lambert-core`(3), case `b < 0`, after
  `X = √r` (`a_vol = 2√S`, `b_vol = −3/2`, `L_vol = log(Y/K)`).
  (c) **Formal instance**: the `δ_k` are the Lambert-centred coefficients of
  `p0:thm:lambert-centered`(4) in `X = √x`, squared
  (`δ_k = 2γ_{k+1} + Σ_{i+j=k} γ_iγ_j`); checked for `δ_0`, `δ_1`. **Instance**:
  the root estimates for the smooth envelopes `g_J^±` in the proof of Theorem
  10.1 are `p0:thm:lambert-centered`(5) with `N = J` (the envelopes are exactly
  of exponential–power type in `X`), followed by squaring.
  (d) **Analogues**: the brackets (1.10) and (10.8) are, as proved, analogues
  of `p0:thm:staircase`(2).
- A note after the abstract, a note closing Section 12.1, and labels on
  Section 1 and Subsections 1.1 and 12.1.

## The OEIS entry (Remark 1.3)

Read on 7 October 2026 in the internal format.

- **A239950** (revision #18, 17 November 2015; _Clark Kimberling_, 30 March
  2014): "Number of partitions of n such that (number of distinct parts) =
  least part.", offset 0; Arndt's comment (28 April 2014) gives the
  conjugate reading "(number of distinct parts) = multiplicity of the
  greatest part"; formula "A239948(n) + a(n) + A239951(n) = A000041(n) for
  n >= 0."; Heinz's Maple program and b-file (`0 ≤ n ≤ 1000`), Alcover's
  Mathematica. No asymptotic formula, no conjecture.
- The 58 data terms equal the shipped `data/oeis_prefix.json`. The b-file,
  which the package did not retrieve, was fetched by the write (SHA-256
  `72e8fed9e454…1cf55f`); all 1001 terms agree with the write's own signed
  Euler route, which also reproduces all 1501 shipped terms.
- The bibliography entry of the article quotes the name as "Number of
  partitions of n such that the number of different parts is equal to the
  smallest part.", a paraphrase rather than the entry's name; the delivered
  text is kept and Remark 1.3 says so. Nothing was submitted to the OEIS.

## What is not claimed

From the source, kept in the article (collected in Section 1.2):

- No worldwide novelty; no novelty of the Schreier family, the occupancy
  product or the saddle and local-limit methods; Hwang's theorems may cover
  part of the analysis (their applicability to the moving cutoff is
  unresolved).
- Fixed order only: no convergence, no uniformity as `R` grows, no effective
  onset of the expansion or of monotonicity, no algebraic independence of
  `a`, `S`; the radial equivalent alone would not give the coefficients.
- No higher-order centering and no relative local law beyond bounded windows
  for the least part.
- The inverses are smooth-envelope brackets; no convergent inverse series
  and no unconditional rounded equality.
- Proposition 11.1 excludes finite eta quotients only, not sums of products
  or `q`-hypergeometric identities.
- Finite checks do not prove the asymptotics; the symbolic programs compute
  two corrections only; determinism is a same-stack statement.

The write adds: its own checks are floating or finite computations (apart
from the exact certificates it reproduced); Remark 10.2 claims no novelty
for any inversion.

## Further questions

Section 12.1 (`mss:sec:questions`) keeps the source's six questions
(explicit higher `c_j` and effective constants; corrections to the least-part
law; moderate deviations; a non-product identity; variants
`min λ = r|supp λ| + s` or bounded multiplicities; the reach of Hwang's
theorems). A dated note records that nothing was moved there or refuted under
Vladimir's standing rule of 4 October 2026, and two finite observations:
`p_{n+1} > p_n` for `33 ≤ n < 1500` (last decrease `p_33 = 184 < p_32 = 190`;
no onset is proved), and no pure period `≤ 50` among the shipped Euler
exponents through degree 200. **No claim of the source was found to be wrong
or unproved.**

## Checks made at intake

- At placement (batch-111 dossier, 7 October 2026; Windows 11): the staged
  files byte-identical to a fresh extraction; the delivered suite reproduced
  its outputs on copies (failures only Windows artifacts: line-ending bytes,
  a recorded Python version, a console code page); `c_1 < 0` and `c_2`
  confirmed against the exact terms to `n = 1500`.
- At the write (7 October 2026; same machine; Python 3.14.4, SymPy 1.14.0,
  mpmath 1.3.0): `SHA256SUMS.json` 24/24; every proof read line by line;
  the counts `p_0..p_1500` by an independent signed Euler route and by brute
  force for `n ≤ 30`; the b-file; `det H = −2SVκ`, `C = −H⁻¹`, the plane form
  (7.7), `W`, `κ_eff`, the five pieces (8.7) summing to (8.8), the radial
  pieces (8.9) summing to `B_*`, `−h_v/12 = 1/8`, `B(a,s(a)) = a`,
  `V = B_s`; the sign certificate and both Horner certificates in exact
  arithmetic (left sides `0.2799…`, `−0.5046…`); the zero
  `−0.7743600362…` (numerical); the constants to 60 digits; the residuals
  `(p_n/(K n^{−3/4}e^{2√(Sn)}) − 1 − c/√n − c_2/n) n^{3/2} = −0.0202…,
  −0.0204…, −0.0203…` at `n = 800, 1200, 1500`; `δ_0 = 0.2511499825…`,
  `δ_1 = 0.2897638360…`; the instances of Remark 10.2. The delivered
  `reproduce.py` rerun from the shipped files (route below): both exact
  outputs byte-identical in normal and optimized mode.
- Sources read by the write: the OEIS entry and b-file; the transseries
  volume (labels named above). Not read: the eight cited works; the source's
  own record of what it inspected is `DATA_SOURCES.md`.

## Relation to the repository

**Formal status.** No statement is formalized, and placement in the
collection confers no formal status. The staircase arithmetic of Remark
10.2(a) is formalized generically as `Fabius.staircase_ceil` in
`Analysis/FabiusFunction/Lean/FabiusFunction/StaircaseInversion.lean` (a
lemma about an arbitrary monotone function); nothing about `p_n` is.

**The transseries volume.** Remark 10.2: the threshold is a staircase
instance; `r(Y)` a Lambert-core instance after `X = √r`; the `δ_k` a formal
Lambert-centred instance, and the envelope roots in the proof of Theorem 10.1
analytic instances of `p0:thm:lambert-centered`(5); the brackets analogues of
`p0:thm:staircase`(2).

**Neighbouring reports** (under
`SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/`):
`a239964-sizes-equal-max-multiplicity` (batch 111: distinct sizes equal to
the maximum multiplicity, a different statistic on the same occupancy
product) and `a098131-minimum-length-compositions` (the Schreier-type
condition on the length of ordered compositions). No shared result, so no
reciprocal note is proposed.

**Stale claims.** Before batch 111 no file of the repository named A239950.

## Notation

A table at the end of Section 1.2 fixes the letters the manuscript reuses,
with the tempting false readings: `a`, `b`; `c`, `c_j` against the unrelated
constants `c_0`, `c_1`, `c_2` of Section 5 and (7.9); `C`; `D`, `D_c`; the
five `p`; the four `P`; `B`, `B_*`, `B_**`, `𝖡_{2r}`; `V`; `W` (a constant)
and `W_{−1}` (Lambert); `K`, `K_m`; `N`; `Q`; `T`; `J`, `L`; `R`, `R_j`;
the two `ℓ` families; `E`, `𝔼`, `E_j`, `𝖤`, `ℰ_H`; `S`, `𝒢`, `G`. No symbol
was renamed; the volume's colliding letters carry the subscript "vol" in
Remark 10.2.

## Labels

Every label carries the prefix `mss:` (none existed in the repository). The
manuscript's 145 labels (`eq:` 120, `sec:` 12, `thm:` 5, `lem:` 4, `app:` 2,
`prop:` 1, `cor:` 1) were prefixed before anything cited them, and the 109
references to them (90 `\eqref`, 19 `\ref`) updated. The write added 6:
`mss:sec:results`, `mss:sec:classical`, `mss:sec:questions`,
`mss:sec:provenance`, `mss:rem:oeis`, `mss:rem:transseries`. The report has
151 labels; builds of the delivered text and of this one give all 145
delivered labels the same numbers (aux files compared). The added remarks are
the last statements of their sections, the added subsection follows the last
delivered text of Section 1, and the added displays are unnumbered.

## Files

```text
README.md                                 this guide (replaces the delivery README)
article.tex                               the report (delivered Report195.tex; labels prefixed, [write] additions)
article.pdf                               compiled report, 30 pages
DATA_SOURCES.md                           the source's data provenance and bounded source screen (delivered)
README_REPRODUCIBILITY.md                 algorithms, certificates, determinism and limits (delivered)
code-PROVENANCE.md                        code provenance disclosure (delivered code/PROVENANCE.md)
code-README.md                            guide to the exact and symbolic programs (delivered code/README.md)
data-README.md                            guide to the observed OEIS prefix (delivered data/README.md)
code/build.py                             deterministic PDF and release builder (delivered at the root)
code/reproduce.py                         exact replay, normal and optimized (delivered at the root)
code/test_build.py                        guard and integration tests (delivered at the root)
code/verify_manifest.py                   release-manifest verifier (delivered at the root)
code/partition_exact.py                   positive DP and independent partition generator (delivered code/)
code/check_exact.py                       counts, prefix, brute force, Euler exponents, certificates (delivered code/)
code/independent_wick_check.py            optional SymPy first-correction check (delivered code/)
code/second_wick_check.py                 optional SymPy second-correction check (delivered code/)
data/oeis_prefix.json                     the 58 OEIS terms observed on 4 October 2026 (delivered data/)
data/generated-exact_terms.txt            recorded p_0..p_1500 (delivered generated/)
data/generated-exact_checks.json          recorded exact checks (same)
data/generated-verification.json          recorded replay receipt (same)
data/generated-BUILD_INFO.json            recorded build parameters (same)
data/generated-build_guards.json          recorded guard results (same)
data/generated-symbolic_check.txt         recorded first-correction transcript (same)
data/generated-second_symbolic_check.txt  recorded second-correction transcript (same)
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to the delivery.

**Not shipped**, recoverable from the arrival commit (next section):
`Report195.pdf` (the delivered 27-page PDF, 472,601 bytes); the checksum
manifest `SHA256SUMS.json` (3,490 bytes, 24 entries), verified at the write
(repository policy ships no checksum manifests); and the delivery
`README.md` (2,661 bytes), staged at placement and replaced by this guide
(summarized below; also at `d451ef3d8`).

**Delivered text that names the delivery layout or files not shipped.**
`README_REPRODUCIBILITY.md`, `DATA_SOURCES.md`, `code-README.md`,
`code-PROVENANCE.md` and `data-README.md` (`Report195.tex`, `README.md`,
`code/PROVENANCE.md`, `generated/`, `SHA256SUMS.json`, the root scripts);
the programs (closed source inventories under the delivered names, and
`generated/` outputs); and Section 12 of the article ("The companion
archive", "the README gives the exact commands"). So no program runs under
the shipped names; use the route below.

## Retrieving the delivered package

```sh
T=$(mktemp -d)
git -C /path/to/ProveIt show 60f54ea06:docs/incoming/Report195_TeX_and_Reproducible_Code.zip > "$T/a.zip"
sha256sum "$T/a.zip"   # 561bd3b3a4ce8a6590b61d65855d2c815b1117a57aa99d3b0a968e68412c0122, 687,972 bytes
cd "$T" && unzip -q a.zip    # SHA256SUMS.json: 24 entries
```

In the extraction the delivered commands are those of its README
(`python -B reproduce.py --output-dir /absolute/new/path`,
`python -B test_build.py`, `python -B build.py --output …`).

## Rerun the checks (on a scratch copy)

Python 3.10 or later, standard library only (SymPy only for `--symbolic`).
Never run anything in the repository. Rebuild the delivered layout from the
shipped files; the source inventory also needs the delivered `README.md` and
`Report195.tex`, which are the files of the placement commit.

```sh
R=/path/to/ProveIt/SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a239950-maximal-schreier-supports
P=SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a239950-maximal-schreier-supports
B=$(mktemp -d); mkdir -p "$B/pkg/code" "$B/pkg/data"; cd "$B/pkg"
cp "$R"/code/{build,reproduce,test_build,verify_manifest}.py .
cp "$R"/code/{partition_exact,check_exact,independent_wick_check,second_wick_check}.py code/
cp "$R/DATA_SOURCES.md" "$R/README_REPRODUCIBILITY.md" .
cp "$R/code-PROVENANCE.md" code/PROVENANCE.md; cp "$R/code-README.md" code/README.md
cp "$R/data-README.md" data/README.md; cp "$R/data/oeis_prefix.json" data/
git -C /path/to/ProveIt show "d451ef3d8:$P/README.md" > README.md
git -C /path/to/ProveIt show "d451ef3d8:$P/article.tex" > Report195.tex
python -B reproduce.py --output-dir "$B/out"
cmp "$B/out/normal/exact_terms.txt" "$R/data/generated-exact_terms.txt"
cmp "$B/out/normal/exact_checks.json" "$R/data/generated-exact_checks.json"
```

At the write this printed `"status": "PASS"` in about 6 s, and both files
(and their `optimized/` twins) were byte-identical to the shipped records.
Use `py` where `python` is not on the path. The PDF builder, the integration
test and the symbolic programs were not rerun by the write.

## Build the PDF

pdfLaTeX (fontenc, lmodern, microtype, geometry, amsmath, amssymb, amsthm,
mathtools, booktabs, array, longtable, xcolor, enumitem, fancyhdr,
hyperref); the bibliography is embedded.

```sh
B=$(mktemp -d); cp article.tex "$B/"; cd "$B"
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built this way with MiKTeX on 7 October 2026 (30
pages): no errors or warnings, no undefined references or citations, no
multiply defined labels, no duplicate PDF destinations, no overfull or
underfull boxes (the delivered text also builds without any, 27 pages). The
delivered byte-identity claims apply to `Report195.tex` under the delivering
toolchain, not to this build.

## From the delivery README

The delivery README (replaced by this guide) described the package ("This
self-contained research package studies A239950"); said that the
authoritative computation is "a positive integer dynamic program through
n=1500, independently checked by enumerating all partitions through n=35 and
comparing precisely the 58 displayed OEIS terms observed on 2026-10-04", and
that "Finite computation supports these checks; it does not replace the
asymptotic proof"; gave the quick-start, build and verification commands
(fresh absolute output paths only; relative paths, symlinks and existing
outputs rejected), including the optional `--symbolic` runs, which are "not
an unrestricted all-orders coefficient engine"; and pointed to
`README_REPRODUCIBILITY.md` and `DATA_SOURCES.md`.

## Rights

Repository contents are MIT-0. The article and this README quote OEIS entry
A239950, and `data/oeis_prefix.json` holds its 58 displayed terms; OEIS
content is published by The OEIS Foundation Inc. under CC BY-SA 4.0
(https://oeis.org/LICENSE), and that content remains under that licence. No
third-party PDF is shipped. Nothing was submitted to the OEIS.

## Provenance

- Sources cited by the manuscript: OEIS A239950; Chu–Vasseur, Fibonacci
  Quart. 62 (2024); Beanland–Chu (2024); Chu et al., Integers 26 (2026);
  Goh–Schmutz, JCTA 69 (1995); Hwang, JCTA 96 (2001); Hwang–Yeh;
  Grabner–Knopfmacher–Wagner, CPC 23 (2014); Archibald et al., AJC 66 (2016).
  Nothing added by the write.
- Batch 111 of `docs/incoming`, bundle Report 195; arrival `60f54ea06`,
  placement `d451ef3d8`, written 7 October 2026. Single source, so no merge
  choices. The delivered `Report195.tex` is shipped as `article.tex`; the
  delivered programs and data as listed above.
