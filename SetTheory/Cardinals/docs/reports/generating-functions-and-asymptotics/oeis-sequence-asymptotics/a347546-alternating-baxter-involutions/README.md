# Alternating Baxter Involutions

**OEIS A347546: the corrected count of the class, a correction of Min's 2021 recurrence (J. Chungcheong Math. Soc. 34 (2021), Theorem 2.7), asymptotics and length inverses, and the refinement by pairs of fixed points**

This is a research report built on 5 October 2026 (write batch 106) from
two manuscripts of one external research session, Reports 149 and 151 of the
session bundle of Reports 1–243, both dated 3 October 2026. They study one
class. A permutation is *doubly alternating* if it and its inverse both
alternate as `π₁ < π₂ > π₃ < ⋯`; it is *Baxter* if it avoids the vincular
patterns `2-41-3` and `3-14-2` (equivalently, Min's strict four-index
definition). `a_n` is the number of involutions among the doubly alternating
Baxter permutations of length `n` — exactly what
[A347546](https://oeis.org/A347546) is named — with `e_m = a_{2m}`,
`o_m = a_{2m+1}`, and `C_j` the Catalan numbers.

- **Part I** (Report 149, the base): the **correction**. In an even-length
  involution the two outer blocks are inverses of each other, not
  involutions, so the outer factor is Catalan:
  `o_m = Σ e_i o_{m−1−i}`, `e_m = o_{m−1} + Σ_j C_j e_{m−2j−2}`, proved from
  three published necessity lemmas of Min–Park (2006). The class has
  **2168** members of length 20, not 2166; two omitted involutions are
  printed. Algebraic generating functions with dominant singularity
  `ρ = (√5 − 1)/4`; `s_m ~ 𝒜_s (1+√5)^m m^{−3/2}` with every fixed order;
  Lambert-`W₋₁` length inverses; ceiling brackets leaving at most two
  adjacent candidates.
- **Part II** (Report 151): the refinement by **pairs of fixed points** (`q`;
  `q = 1` gives Part I back): `E = (1 + xqR)/M`, `R = 1/(1 − xE)`, positive
  factorizations, all fixed orders of `T_{s,m}(w)` uniformly on compact
  complex windows of the sparse weight `q = w/m` with entire profiles, an
  exact criterion for inverting in the weight, interior inverses in powers of
  `m^{−1/2}`, and Poisson-type laws with total-variation rate `O(m^{−1/2})`.

| Source | Bundle report | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| *Corrected enumeration and asymptotics of alternating Baxter involutions: the class intended by OEIS A347546 and its parity inverses* (author line "Report 149", 3 October 2026); the base | 149 | `Corrected_Baxter_Involutions_Asymptotics_and_Inverses_Source.zip` (496,609 bytes, 16 files; `Report149.tex`, 917 lines, 15 pp.) | none | `47fc7a069` | Part I, Sections 1–11 |
| *Sparse fixed point crossover for alternating Baxter involutions: entire profiles, exact thresholds, and weighted inverses* (author line "Report 151", 3 October 2026) | 151 | `Baxter_Fixed_Point_Crossover_Profiles_and_Inverses_Source.zip` (912,824 bytes, 9 files, 2 of them Report 149's source and PDF under `foundation/`; `Report151.tex`, 977 lines, 17 pp.) | none | `47fc7a069` | Part II, Sections 12–22, plus the write's Section 23 |

Both archives arrived unchanged in `60f54ea06` ("Arrival: 177 research
archives from the session bundle of Reports 1-243") and survive there
(`git show 60f54ea06:docs/incoming/<archive> > <archive>`); the placement
commit `47fc7a069` (batch 106, cluster 106-BAXTER) removed them from
`docs/incoming/`. The write is "Write batch 106
(a347546-alternating-baxter-involutions): new report, the corrected count of
alternating Baxter involutions".

**Status.** Unrefereed; not formalized; no statement has been checked by a
proof assistant. Neither manuscript names an author, a tool or an addressee,
says it is AI-assisted, or carries "prepared for private review" wording;
each sets an empty PDF author field. Every result, proof, remark and
limitation of the two manuscripts is printed; Report 151's restatement of
Report 149 is printed once, in Part I.

## The correction on record

- **Min (2021), Theorem 2.7** (S. Min, *The enumeration of involutions of
  doubly alternating Baxter permutations*, J. Chungcheong Math. Soc. 34(3)
  (2021) 253–257, doi:10.14403/jcms.2021.34.3.253), with `b_n = |B_n(I)| = a_n`:
  `b_{2n−1} = Σ_{k=1}^{n−1} b_{2k−2}·b_{2n−2k−1}` (n ≥ 2) and
  `b_{2n} = b_{2n−1} + Σ_{k=⌈n/2⌉}^{n−1} b_{2n−2k−1}·b_{4k−2n}` (n ≥ 3), with
  `b_0 = b_1 = b_2 = 1` (and `b_4 = 2` in the proof). **The odd formula is
  right; the even formula is wrong.** The faulty step (p. 256): writing
  `π = π₁π₂π₃`, the proof asserts `π₁* ∈ B_{2n−2k}(I)` and "Since π is an
  involution, π₁* = π₃". In fact `std(π₃) = (π₁*)⁻¹`: the outer blocks are
  mutual inverses, and `π₁* = 1 ⊕ σ ⊕ 1` with `σ` ranging over **all** of
  `RB_{2n−2k−2}`, which has `C_{n−k−1}` elements, so the factor
  `b_{2n−2k−1}` should be `C_{n−k−1}`. Since `C_j = o_j` for `j ≤ 3` and
  `C_4 = 14 > 12 = o_4`, the first difference is at `n = 20`, a deficit of
  exactly 2 (Remark 23.1).
- **Counterexample** (Remark 23.3): the two length-20 involutions of Part I's
  Section 5,
  `π⁽¹⁾ = (11,19,15,17,16,18,13,14,12,20,1,9,7,8,3,5,4,6,2,10)` and
  `π⁽²⁾ = (11,19,17,18,13,15,14,16,12,20,1,9,5,7,6,8,3,4,2,10)`, satisfy
  Min's own definition (all 4845 strict quadruples, alternation,
  involution), have the shape of her Lemma 2.1 with `k = 5`, and have a
  non-involutive `π₁*`; they are the two objects her count misses.
- **Explicit proof** (`[write]` Proposition 23.2): the even formula holds
  for the class for `3 ≤ n ≤ 9` and fails for every `n ≥ 10`, by
  `Σ_{j≥4}(C_j − o_j) e_{n−2j−2} ≥ 2`; the recurrence-defined sequence equals
  the class for `n ≤ 19` and `n = 21` and is **strictly smaller for `n = 20`
  and every `n ≥ 22`**.
- **Min's printed list** (p. 257) is wrong at `n = 20, 22, …, 26`
  (2166, 6012, 14592, 17234, 42198, 49336 for 2168, 6014, 14594, 17252,
  42204, 49360) (Remark 23.4).
- **OEIS A347546** (revision #20, Jun 29 2022, read 5 October 2026): the
  **definition is right**, but the data and the `%o` Python program implement
  Min's recurrence, so **21 of the 42 terms are wrong**: `n = 20` and
  `n = 22, …, 41` (first wrong odd term `n = 23`; `a_21 = 5080` is right).
  Remark 23.5 tabulates them. Barnabei–Bonetti–Castronuovo–Silimbani (ECA 3:1
  (2023) S2R4, Section 10; arXiv:2206.13877) cite the recurrence for this
  sequence but print no value of it.
- Nothing has been submitted to the OEIS, and no erratum has been sent to
  the journal or the author; the report records the correction.

**Prior art credited.** The Catalan count `|B_{2j}| = |R_{2j}| = C_j` that
Part I's Section 3 derives (`abx:en:eq:catalan-factor`) is Guibert and
Linusson's theorem (Discrete Math. 217 (2000) 157–166; doubly alternating
Baxter permutations of lengths `2n` and `2n+1` are counted by `C_n`), proved
again by Min–Park (2006); Report 149 does not cite Guibert–Linusson. Part I's
Section 3 is a second route to it, from Min–Park's necessity lemmas; the new
enumeration is the involution count. (The write could not read
Guibert–Linusson's paper — the publisher's page refused access; the statement
is quoted from Min (2021), p. 254, and from Dokos–Pak, arXiv:1401.0770.)
General algebraicity is Brignall–Huczynska–Vatter's (2008), as Part I says.

## Why the Parts are in this order

Report 149 is the base and Part I: it is self-contained (given the three
Min–Park lemmas), proves the decomposition and the correction, and carries the
length asymptotics and inverses. Report 151 refines its count by a second
variable and imports its decomposition ("those established in Report 149"),
so it is Part II. They prove different theorems; neither supersedes the
other.

**Embedded copy.** Report 151's `foundation/Report149.tex` and
`foundation/Report149.pdf` are byte-identical to the standalone delivery
(SHA-256 at placement, `cmp` again at the write); printed once, as Part I, and
not shipped.

## Files

The directory holds 19 files: 4 at the root, 12 in `code/`, 3 in `data/`.

**Report files**, written in the write: this guide, the merged article and its PDF.

```
README.md
article.pdf
article.tex
```

**Report 149, prefix `149-enum-`** (12 files): the companion's README; the
exact companion (`exact.py` recurrences and rational radicals, `permutations.py`
literal Baxter predicates and generators, `safeio.py` POSIX output layer,
`verify.py`, the unit tests); the release tools (deterministic PDF builder,
ZIP builder, output-safety primitives and their tests); the frozen evidence;
the source-provenance record.

```
149-enum-companion-README.md
code/149-enum-build_pdf.py
code/149-enum-companion-exact.py
code/149-enum-companion-permutations.py
code/149-enum-companion-safeio.py
code/149-enum-companion-tests-test_companion.py
code/149-enum-companion-verify.py
code/149-enum-make_zip.py
code/149-enum-release_tools.py
code/149-enum-test_release.py
data/149-enum-SOURCE_PROVENANCE.json
data/149-enum-companion-evidence.json
```

**Report 151, prefix `151-fixedpt-`** (4 files): the exact and numerical
companion, its tests, the deterministic builder, the pinned requirement
(`mpmath==1.3.0`).

```
code/151-fixedpt-build.py
code/151-fixedpt-companion.py
code/151-fixedpt-test_companion.py
data/151-fixedpt-requirements.txt
```

**Not shipped** (all retrievable from `60f54ea06`): the two PDFs;
`Report151.tex` (printed as Part II) and its `README.txt`; Report 149's
delivered `README.md` (staged at placement, replaced by this guide; its
content is summarized here); Report 149's `SHA256SUMS` (a pure checksum list,
15/15 verified at placement and again at the write; repository policy drops
checksum manifests); Report 151's `foundation/` (byte copies of Part I).

## Labels and numbering

Label prefix **`abx:`** (none at HEAD before this report): Part I uses
`abx:en:` (Report 149's 47 labels), Part II `abx:fp:` (Report 151's 63). Five
bare names collide between the manuscripts (`eq:erec`, `eq:quadratic`,
`eq:system`, `eq:thresholds`, `thm:inverse`); under the Part prefixes they are
distinct. The write added the two Part labels, labels for the 38 sections and
subsections that had none (Report 151's Section 6 already had `sec:low`), the front matter's
`abx:sec:guide`, `abx:sec:status`, `abx:sec:oeis`, `abx:sec:notation`,
`abx:sec:provenance`, `abx:sec:trust`, `abx:sec:neighbours`, and Section 23's
`abx:sec:further`, `abx:sub:corrections`, `abx:sub:questions`,
`abx:rem:min`, `abx:prop:hat`, `abx:eq:hateven`, `abx:rem:witness`,
`abx:rem:list`, `abx:rem:oeis` and the eight items `abx:q:effective`,
`abx:q:monotone`, `abx:q:hat`, `abx:q:thesis`, `abx:q:minpark`,
`abx:q:exponential`, `abx:q:clt`, `abx:q:boundary`. 174 labels in all, all
distinct.

| Part | Manuscript | Section here | Statement and equation `k.j` |
|---|---|---|---|
| I | Report 149 | `k` (1–11, unchanged) | `k.j` |
| II | Report 151 | `k + 11` (12–22); 23 added | `(k+11).j` |

Both manuscripts number equations within sections, so Report 151's Theorem 2.1
is Theorem 13.1 here, its equation (2.1) is (13.1), its Proposition 7.2 is
18.2, its Theorem 8.1 is 19.1. A comparison of the build's `.aux` with
separate builds of the two delivered `.tex` files confirmed all 110 delivered
labels under these offsets and prefixes. The delivered READMEs, code and data
use the manuscripts' own numbers.

## Notation

No delivered symbol was renamed. The front matter's "Notation across the two
Parts" lists every letter whose meaning changes, with the tempting false
readings, and each Part opens with a reading-conventions table. The main
collisions: **`𝓑`** (Part I's class `𝓑_n`; Part II's Bernoulli polynomials
`𝓑_j` — not the class), **`R`, `r_m`** (Part I's reverse class and its
involutions; Part II's series `R(x,q)` and `r_m(q)`, which are Part I's `O`,
`o_m = r_m` at `q = 1`), **`ε`** (`1/X_s` in Part I; the parity `(−1)^m` in
Part II), **`y`** (a target value; `y = 2x`), **`D`** (the discriminant
`M·P`; the Euler operator `w d/dw`), **`H`**, **`P`**, **`ρ`** (the
singularity `(√5 − 1)/4`; a circle radius `> 1`), **`t`**, **`K`**, **`b`,
`d`**, **`N`, `θ`** — and the word "threshold": Part I inverts in the
*length*, Part II in the *weight* at fixed `m`. In Section 23 Min's `B_n`,
`RB_n`, `b_n` are Part I's `𝓑_n`, `𝓡_n`, `a_n`.

## What the report claims

**Part I (Report 149).**
- Theorem 1.1: the corrected recurrences and the system
  `O = 1/(1 − xE)`, `E = 1 + xO + x²E C(x²)`, from Min–Park's Theorem 4.1 and
  Corollaries 4.5, 4.7 (accepted as published inputs; converses, inverse
  restrictions, multiplicities and uniqueness proved); Lemma 2.1 (sum
  closure, interval blocks); decompositions (3.1)–(3.2) and the Catalan count
  (3.3) (Guibert–Linusson's theorem, re-derived); the involution restriction
  `π = A ⊖ η ⊖ A⁻¹` and the block interpretation `E = (1 + xO)/(1 − x²C(x²))`.
- Section 5: the published error, the two omitted involutions, the exact
  deficit 2 at length 20.
- Section 6: radicals, the quartic relation, `ρ = (√5 − 1)/4`, the Delta
  domain.
- Theorem 7.1: every fixed order; `𝒜_o = 1.6409417…`, `𝒜_e = 0.5677893…`,
  `λ_o = −2.6217198…`, `λ_e = −0.7136903…`, exact; the coefficient algorithm
  (7.8); the ratios (7.9) and eventual monotonicity.
- Theorem 8.1: the fixed-order inverse around the `W₋₁` centre (8.3);
  Theorem 9.1 and Corollary 9.2: safe ceilings, at most two adjacent
  candidates, `δ = 0.9037058…`.

**Part II (Report 151).**
- Theorem 13.1: the bivariate system (at `q = 1` Part I's Theorem 1.1);
  closed forms (13.5)–(13.11), `h_{2j} = h_{2j+1} = binom(2j,j)/4^j`,
  `[q]e_m(q) = 2^{m−1}h_m`, the degrees.
- Theorem 14.1: all fixed orders on compact complex discs, entire profiles;
  the first profiles (14.4)–(14.8); the finite algorithms of Section 15;
  Lemma 16.1 and the factorial tails; Lemma 17.1 (growing-shift remainder).
- Theorem 18.1: exact nonnegative inverse in the weight, thresholds
  `θ_{s,m}`; (18.2): no nonnegative exact root at the limiting reverse
  target for all large odd `m`; Proposition 18.2: the two even boundary roots.
- Theorem 19.1: interior inverse in powers of `m^{−1/2}`; leading inverses
  (19.5) and (19.6) (`W₋₁`).
- Theorem 20.1: sparse Poisson-type laws, total variation `O(m^{−1/2})`.

**Added by the write** (all marked `[write]`, dated 5 October 2026): the
front matter (including Min's paper and the OEIS entry as read on 5 October
2026, and the transseries-volume relations below); dated notes (the
Guibert–Linusson credit, the `q = 1` reduction, numerical checks, pointers);
Section 23 with **Remark 23.1** (Min's theorem and the faulty step),
**Proposition 23.2** with its proof (the exact extent of the error), Remarks
23.3–23.5 (the counterexample, Min's list, the OEIS table), and the further
questions.

**The inverses and the transseries volume**
(`Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/transseries_and_inversion.tex`).
Part I's centre (8.3) is an **instance** of `p0:thm:lambert-core`(3)
(`a = log(1+√5)`, `b = −3/2`, `L = log(y/𝒜_s)`, branch `W₋₁`); its formal
coefficients (8.5) are those of `p0:thm:lambert-centered`, and Theorem 8.1 is
that theorem's part (5) applied to the model `exp F_{s,J}` (instance, orders
`K ≤ J`). Its ceiling brackets (Theorem 9.1) and the parity identity (9.5)
have the form of `p0:thm:staircase`(2) and (4) but are proved directly at the
integers, with no interpolation: **not instances**. Corollary 9.2 has no
counterpart. Part II's reverse leading inverse (19.6) is an **instance** of
`p0:thm:lambert-core`(3) after the change of variable `X = w₀ + 1/h`
(`a = 1`, `b = −1`, `L = log h + 1/h`); its ascent inverse (19.5) is a
logarithm; its interior and boundary expansions are reversions of a simple
root, **analogous** to `p0:thm:perturbed-inversion` but not instances. No
manuscript cites the volume or claims novelty for the inversion.

## What the report does not claim

Every limitation is printed in place. In short: finite computation is not
the all-length proof; Min–Park's necessity lemmas are accepted, not re-proved;
no exhaustive priority claim (bounded searches only; Min's 2002 thesis not
inspected); general algebraicity predates the report (BHV 2008), and so does
the inverse-pair skew decomposition; the bracket constants and onsets are
existence constants, not certificates; no convergence, uniformity in the
order, exponentially improved or global expansion; eventual (not all-index)
monotonicity; no claim about the recurrence-defined sequence beyond
Proposition 23.2; Part II is a refinement of the corrected class, not of the
printed recurrence; no central limit theorem at fixed positive weight, no
growing-window or growing-order expansion, no boundary-uniform, moving-target
or global complex inverse; Part II's boundary expansions are for the two
specified targets only; remainder constants are qualitative and numerics are
diagnostics; fixed-point bias, parity limits and phase transitions are not
introduced here (Park–Rizzolo, arXiv:2512.25006v2). **Both companions**:
finite exact checks prove no asymptotic remainder; no public sequence edit,
erratum, submission or correspondence.

## Further questions, and the standing rule

Neither manuscript has a section of questions. Section 23 records the
corrections (above) and collects, under Vladimir's standing rule of
4 October 2026, every unproved claim and stated limitation as a question, with
source, sketch and what is missing:

1. **effective constants and certified brackets** (both Parts) — an
   uncertified hint: Proposition 18.2's `w_{E,m}` has an `O(m⁻³)` constant
   near −450;
2. **all-index monotonicity** of `a_n` (Part I proves eventual monotonicity)
   — true for `n ≤ 2001`, strictly from `n = 5` (write, uncertified);
3. **the nature of the recurrence-defined sequence** (Part I makes no claim);
4. **priority and Min's 2002 thesis** (Part I);
5. **a proof of Min–Park's necessity lemmas inside the report** (the one
   external trust boundary of the enumeration);
6. **convergence, uniformity in the order, global expansions** (both Parts);
7. **a central limit theorem at fixed weight `q > 0`** (Part II);
8. **inverses near the threshold and globally** (Part II).

**Wrong claims on record:** Min (2021) Theorem 2.7, even formula; her list
of values at `n = 20, 22–26`; the data and program of A347546 at `n = 20,
22–41` — each with a proof (Proposition 23.2) and the counterexample
(Remark 23.3). **Nothing in the two manuscripts was found to be wrong.**

## Relation to neighbouring reports

- No other report of the collection treats A347546, Baxter involutions or
  doubly alternating permutations (searched 5 October 2026; "Baxter"
  occurs elsewhere only for Rota–Baxter algebras and A. M. Baxter's ascent
  sequences).
- Related in subject, no shared statement:
  `a113226-vincular-avoiders`, `a239144-forbidden-distance-involutions`,
  `../../../enumerative-combinatorics/mesh-avoidance-catalan-inflation`, and
  batch 105's `a217057-unique-pattern-occurrences` and
  `a224182-unique-1432-order`.
- The transseries volume supplies the Lambert core of which the leading
  inverses are instances (above). No reciprocal note is proposed.

## Relation to formal projects

Placement in the collection confers no formal status, and no statement of
this report is formalized: no Lean or Rocq file in the repository treats
these permutations (searched 5 October 2026).

## Delivery names, renames and discrepancies

- Every delivered file keeps its bytes (the 16 staged code, data and
  companion-README files were checked against a fresh extraction from
  `60f54ea06` at the write: 0 differences; `article.tex` and this README
  replaced the two staged base files). Only names changed (tables below).
- **Imports and inventories use delivery names, so nothing runs in this
  directory.** Report 149's `verify.py` imports `exact`, `permutations` and
  `safeio` by module name, and its tests import the companion modules;
  `make_zip.py` verifies the unshipped `SHA256SUMS` and `build_pdf.py` builds
  `Report149.tex`. Report 151's tests import `companion` and `build`, and
  `build.py` hard-codes its allowlist (`Report151.tex`, `foundation/…`) and
  the SHA-256 of the two foundation files. Rerun from the archives (below).
- `149-enum-companion-README.md` is titled for "Report149" and uses
  `companion/…` paths; it and Report 151's README use `/tmp/…` examples.
  Both builders use the Debian TeX trees `/usr/share/texlive/texmf-dist` and
  `/usr/share/texmf`.
- `data/149-enum-SOURCE_PROVENANCE.json` records SHA-256 hashes of
  downloaded third-party PDFs (Min–Park, Min, Ouchterlony, Barnabei et al.,
  BHV) and of an OEIS snapshot; none of those files is shipped. The write
  confirmed the hash of Min (2021) against the publisher's PDF.
- Report 151's delivered README and its Section 10 (Section 21 here) describe
  the "unchanged Report 149 source and PDF" under `foundation/`; that copy is
  Part I and is not shipped.

## Rerunning the checks

Run on a copy in a scratch directory, never in this directory. Recreate the
delivered layout from the arrival commit (both archives extract to their
root, without an inner directory):

```
git show 60f54ea06:docs/incoming/Corrected_Baxter_Involutions_Asymptotics_and_Inverses_Source.zip > r149.zip
git show 60f54ea06:docs/incoming/Baxter_Fixed_Point_Crossover_Profiles_and_Inverses_Source.zip > r151.zip
mkdir x149 x151 && unzip -q r149.zip -d x149 && unzip -q r151.zip -d x151
cd x149
sha256sum -c SHA256SUMS
python3 companion/verify.py --check companion/evidence.json
python3 companion/verify.py --output <new-dir>/evidence.json
python3 -m unittest discover -s companion/tests -v
cd ../x151
uv run --no-project --with mpmath==1.3.0 python -m unittest -v test_companion
python companion.py exact --m 12
uv run --no-project --with mpmath==1.3.0 python companion.py diagnostics --dps 80
```

Report 149's companion needs only the standard library (Python 3.10 or
later); Report 151's numerical parts need `mpmath==1.3.0`. The PDF and ZIP
builders need Linux and the recorded TeX Live toolchain for byte-identical
output and were not run.

**Windows.** Report 149's `safeio.py` needs POSIX `O_NOFOLLOW` and
`O_DIRECTORY`, so `verify.py --check` and `--output` stop with "safe path
operations require O_NOFOLLOW and O_DIRECTORY". The mathematics runs; to
regenerate the evidence in memory and compare it with the delivered file, run
from `x149/companion`:

```
python -c "import verify; d=verify.build_evidence(); b=verify.canonical_bytes(d); print(b==open('evidence.json','rb').read()); verify.validate_evidence(verify.decode_evidence(open('evidence.json','rb').read()))"
```

Report 149's unit tests (21) and Report 151's (26) fail on Windows only in
their file-safety checks (7 and 6 tests: `O_NOFOLLOW`, `os.mkfifo`, path
traversal); every exact and numerical test passes.

Results: at placement (5 October 2026, Python 3.14.4, Windows, on copies,
recorded in the batch-106 dossier) the checksum list verified 15/15; Report
149's evidence regenerated in memory byte-identical to the delivered
`evidence.json` (24,185 bytes) under `python` and `python -O`, and the
delivered file validated; its unit tests ran 21, 14 passing, the 7 failures
all POSIX-only; Report 151's tests ran 26, 20 passing, the 6 failures all in
`BuildSafetyChecks`; `companion.py exact --m 12` and `diagnostics --dps 80`
ran. At the write (5 October 2026, fresh extractions, Windows) the checksum
list (15/15), the in-memory evidence check (identical, validated, 20 s),
Report 151's tests (26 run, the same 6 POSIX-only failures) and
`companion.py exact --m 12` were repeated with the same results. The two
delivered `.tex` files compile with MiKTeX pdfLaTeX to 15 and 17 pages
without warnings.

## Rights

Repository contents are MIT-0. The OEIS data quoted in the article (the
terms of A347546 in Remark 23.5 and Part I's table) and the OEIS snapshot
hashed in `data/149-enum-SOURCE_PROVENANCE.json` are OEIS material, available
under CC BY-SA 4.0 ([OEIS license](https://oeis.org/LICENSE)); the companions
recompute every class value from the recurrence. Credited as the manuscripts
and the write cite them: the OEIS entry (Sook Min), Min (2021), Min–Park
(2006), Guibert–Linusson (2000), Ouchterlony (2006), Barnabei et al. (2023),
Brignall–Huczynska–Vatter (2008), Flajolet–Sedgewick, the DLMF, Park–Rizzolo,
Dokos–Pak. Nothing was submitted to the OEIS.

## Build

```
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

pdfLaTeX (MiKTeX), in a scratch copy; commit only `article.pdf`. The build
(44 pages): no errors, no undefined or multiply defined references or
citations, no duplicate destinations, no overfull or underfull boxes, no
warnings.

## Delivered path → shipped path

Report 149 (`149-enum-`; delivered at the archive root):

| Delivered | Shipped |
|---|---|
| `Report149.tex` | `article.tex` (Part I) |
| `README.md` | replaced by this guide |
| `companion/README.md` | `149-enum-companion-README.md` |
| `companion/exact.py`, `permutations.py`, `safeio.py`, `verify.py` | `code/149-enum-companion-<name>` |
| `companion/tests/test_companion.py` | `code/149-enum-companion-tests-test_companion.py` |
| `build_pdf.py`, `make_zip.py`, `release_tools.py`, `test_release.py` | `code/149-enum-<name>` |
| `companion/evidence.json` | `data/149-enum-companion-evidence.json` |
| `SOURCE_PROVENANCE.json` | `data/149-enum-SOURCE_PROVENANCE.json` |
| `Report149.pdf`, `SHA256SUMS` | not shipped |

Report 151 (`151-fixedpt-`; delivered at the archive root):

| Delivered | Shipped |
|---|---|
| `Report151.tex` | not shipped; printed as Part II of `article.tex` |
| `companion.py`, `test_companion.py`, `build.py` | `code/151-fixedpt-<name>` |
| `requirements.txt` | `data/151-fixedpt-requirements.txt` |
| `foundation/Report149.tex`, `.pdf` | byte copies of Report 149; not shipped |
| `README.txt`, `Report151.pdf` | not shipped |

## Provenance

Two manuscripts (bundle Reports 149, 151) → one report; base 149, printed
as Part I. Arrival `60f54ea06`, placement `47fc7a069`, write batch 106
(5 October 2026). No manuscript pins a ProveIt commit. Merge choices
(dependency order, Report 151's restatement of Report 149 printed once,
Report 151's hard-coded section numbers printed as references, the merged
bibliography) are listed in the article's front matter, "Provenance and merge
decisions".
