# One-Sided Rectangulations (OEIS A348351)

**The logarithmic power `log a(n) = n log Γ − α log n + o(log n)`,
non-D-finiteness, and the two-term threshold inverse**

A research article dated 2 October 2026 ("Research Report 111" of a session
bundle), built from one manuscript. Its title page and PDF metadata name no
person (author "Research report"). The package carries no "prepared for
private review" line, no e-mail address and no personal data.

| Source | Bundle report | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | Report 111 (batch 103) | `A348351_Rectangulations_Exponent_and_Non_D_Finiteness_Source.zip` (wrapper directory `report111/`, 23 files, 436,299 bytes, SHA-256 `e3f191bd…143b`), arrival commit `60f54ea06`; main file `report111.tex` | none: the package names no ProveIt commit, path or report | `9c995cefe` (batch 103) | the whole report |

**Status:** AI-assisted, unrefereed, not formalized: no Lean or Rocq
declaration exists for any statement of this report. The proofs are
conventional mathematical proofs. The delivered checks are exact finite
algebra and bookkeeping; they certify no limit theorem and no asymptotic
statement.

## Trust boundaries

- **The walk model is inherited, not re-proved.** The bijection between
  one-sided (area-universal) rectangulations and weak left/right four-colour
  quadrant walks is Asinowski, Cardinal, Felsner and Fusy, *Combinatorics of
  rectangulations: Old and new bijections*, Combinatorial Theory 5(1) (2025),
  art. 14, §4.6, Fig. 4.16. **The intake did not consult that paper**; it
  reconstructed the step table from the two weak inequalities printed in
  Section 2 and recomputed `a(0..16)`, which agree with the OEIS.
- **Two external theorems are cited:** Whitt's martingale functional limit
  theorem (Probab. Surveys 4 (2007), Thm 2.1(ii)) and the
  André–Chudnovsky–Katz theorem on G-functions in the formulation of
  Fischler–Rivoal (Comment. Math. Helv. 89 (2014), Def. 1, Thm 6, Cor. 1).
  Their page locations are the source's readings, not checked by ProveIt.
- **Four proof steps are condensed** (marked in the article): the write
  completes two (Whitt's hypotheses after Lemma 3.1; the non-normal uniform
  decay in Section 4) and lists the other two (the bridge limit of
  Lemma 5.1; the uniformity arguments of Section 7.2) as Question 6.
- **Priority is not established.** The source's literature search was
  bounded (through 2 October 2026); an intake web search on 5 October 2026
  found no later proof either.

## What it proves

`a(n)` is OEIS A348351 (offset 0, `a(0) = 1`): one-sided, equivalently
area-universal, rectangulations with `n` rectangles; equivalently
permutations of `[n]` avoiding the vincular patterns 2-41-3, 3-14-2, 2-14-3,
3-41-2. Put `Γ = (7+√17)/2 ≈ 5.5615528128`, `ρ = (29−7√17)/4`,
`θ = arccos(−ρ)`, `p = π/θ`, `α = 1 + p ≈ 2.9569294595`. Numbers follow
the section counter.

- **Theorem 1.1 (`osr:thm:main`):** `log a(n) = n log Γ − α log n + o(log n)`,
  i.e. `a(n) = Γⁿ n^{−α+o(1)}`, and `a(n)^{1/n} → Γ`; the generating function
  is **not D-finite** over `ℂ(z)`; and the threshold
  `N(y) = min{n : a(n) ≥ y}` satisfies
  `N(y) = log y/log Γ + (α/log Γ) log log y + o(log log y)`.
  This proves the **exponent part** of the conjecture
  `a(n) ~ cΓⁿn^{−α}` stated after Proposition 4.23 of Asinowski–Cardinal–
  Felsner–Fusy (whose Proposition 4.23 gives the upper rate `Γ`); the
  **amplitude part** (existence of `c > 0`) remains open.
- **Sections 2–3:** the exact multistate recurrence, the primitive matrix `A`
  with `det(tI − A) = t(t+1)(t² − 7t + 8)`, the Perron tilt, an explicit
  bounded Poisson corrector and the effective covariance
  `Σ = (1/272)[[51+13√17, −17+5√17], [−17+5√17, 51+13√17]]` (also the Hessian
  of `log λ`), whose correlation is `ρ`; the stationary dual chain and the
  count identity `a(L+1) = Γ^L Σ_c r_c K_L((0,c),(0,W))`, giving
  `a(n) ≤ (3+√17)Γ^{n−1}`. **Lemma 3.1 (`osr:lem:fclt`):** the unrestricted
  functional limit.
- **Section 4:** a lattice local limit theorem (aperiodicity by red return
  cycles of length 3). **Lemma 5.1 (`osr:lem:bridge`):** exact-time interior
  bridges `K_m ≥ c/n`.
- **Sections 6–8:** wedge harmonic measure, uniform annular transfer,
  survival `≤ C n^{−p/2+ε}`, and the endpoint estimate
  `K_n((0,B),(0,W)) = n^{−p−1+o(1)}` by two first-hit prefixes glued with an
  exact-time bridge.
- **Section 9:** monotonicity and the inverse; **Section 10:** `α` is
  irrational and `2 < α < 3` (`2 cos θ` has the conjugate
  `(−29−7√17)/2 < −2`), then positivity of `F''` and the rational local
  exponents of G-functions exclude D-finiteness.

Added by the write (5 October 2026), with proofs, marked `[write]`:

- **Remark 1.2 (`osr:rem:cone`):** the chain satisfies hypotheses (H1)–(H5)
  of Report 112's Theorem 2.1, printed as Theorem 24.1 in
  `a377922-corner-polyhedra-schnyder` (`cps:log:thm:cone`, see "Relation to
  the repository") at the phases `(c, W)`, `c ∈ {B, R, G}`, and
  `K_L((0,W),(0,W)) = 0` for `L ≥ 1`; so the exponent of Theorem 1.1 also
  follows from that general theorem.
- **Remark 9.1 (`osr:rem:lambert`):**
  `N(y) = −(α/g) W₋₁(−(g/α) y^{−1/α}) + o(log log y)`, `g = log Γ`, the
  instance `a = g`, `b = −α` of `p0:thm:lambert-core`; it adds no information
  at this precision.
- **Remark 10.1 (`osr:rem:criterion`):** the criterion in general: nonnegative
  integers with `a_n = μⁿ n^{−α+o(1)}`, `μ > 1`, `α` irrational, have a
  non-D-finite generating function. (After the independent check it also
  says why `R = 1/μ` is algebraic if the series is D-finite: by Pringsheim's
  theorem `R` is a singularity, hence a root of the leading coefficient of
  an annihilating operator over `ℚ[z]`.)
- **Note in Section 9:** `a(n+1) ≥ 2a(n)` for `n ≥ 1` (prepend a zero edge
  from `R` or from `G`), so the sequence is strictly increasing from `n = 1`.
- **Notes after Lemma 3.1 and in Section 4:** the condensed steps 1 and 2
  written out (the predictable quadratic variation as an additive functional
  of the colour chain; uniform matrix-power decay by Gelfand's formula and a
  finite cover, with `δ_t ∈ (0,1)` since the independent check, first
  `δ_t > 0`). Notes at steps 3 and 4 say what is missing.
- Section 1.1 (provenance, credits, relation to the repository, notation,
  collected non-claims), the shipped-layout note in Section 11.1, and
  Section 11.4.

**Independent check of the write (5 October 2026).** An adversarial check
made by the intake after the write (`0c2cdf435`) examined the seven items
the write supplied with proofs or relies on — Remarks 1.2, 9.1 and 10.1,
the note `a(n+1) ≥ 2a(n)`, the notes completing steps 1 and 2, and the
irrationality certificate of Section 10 — and found all seven valid, with
no counterexample and no gap in any proof chain. Changes: in the step-2
note, "there are `δ_t > 0`" now reads `δ_t ∈ (0,1)` (with `δ_t = 1`, the
bound `(1−δ)^{j/k−1}` would be `0` to a negative power for `j < k`;
cosmetic, marked there); Remark 10.1 now says why `R` is algebraic
(Pringsheim) and names Report 112's derivative order `m` (our `k`).
Separately, Part III of `a377922-corner-polyhedra-schnyder` has been
written since (`9b4001d29`): Remark 1.2, Remark 10.1 and Question 6 now
give its printed numbers (Theorem 24.1, Lemma 24.2, Section 27,
Remark 27.1, read from its built PDF), and Remark 1.2 records in a dated
note that Part III's Section 22.5 cites this report (it first said "written
concurrently" and "Neither report cites the other"). The check used
neither the delivered programs nor the write's. Its own programs (Python
3.14.4, sympy 1.14.0, mpmath 1.3.0, NumPy) rebuilt the step table from the
two weak inequalities and compared it cell by cell; ran an exact
big-integer transfer recursion to `n = 600`, reproducing `a(0..16)` (all
the OEIS has; its b-file is synthesized from the entry); and counted the
vincular avoiders by brute force for `n ≤ 9`, independently of the walk.
`a(n+1) ≥ 2a(n)` holds for every `1 ≤ n ≤ 599`, with equality at `n = 1`,
and fails at `n = 0`, so `n ≥ 1` is needed; `a(n) ≤ (3+√17)Γ^{n−1}` for
`1 ≤ n ≤ 600`; the observations of Question 1 are correct roundings. Exact
`ℚ(√17)` algebra confirmed (H1)–(H5): `A² > 0`, the characteristic
polynomial, `r`, `π`, `m`, `h`, `Σ` (unchanged when `h` is shifted by a
constant), `ρ`, `α = 2.9569294595087535…`; the Hessian of `log λ` (40-digit
finite differences) equals `Σ` to 12 digits; `K_L((0,W),(0,W)) = 0` for
`L ≥ 1`; the dual seed probability is `p*_WW(−v) = p_WW(v) = 1/Γ ≈ 0.1798`;
on a 401 × 401 torus grid the Fourier spectral radius is at most `0.9981`
for `|t| ≥ 0.1`, `0.954` for `|t| ≥ 0.5`, `0.823` for `|t| ≥ 1`. Whitt's
hypotheses follow from the deterministic jump bounds (largest
corrected-increment coordinate `1.5428 < 3`; `max ‖V(c)‖ = 0.557`) and the
ergodic theorem. The Lambert threshold is `L > α(1 − log(α/g)) ≈ 1.3477`;
`N(10^e) = 33, 74, 142, 278` against `X_0 = 32.86, 74.53, 142.74, 278.08`
(`e = 20, 50, 100, 200`), with `X_0` minus the two-term form drifting
towards `−(α/g) log g ≈ −0.9304`. The criterion uses the `o(1)` form only
through the Abelian comparison; no Tauberian step is needed. `2 cos θ` has
minimal polynomial `x² + 29x + 2` (an algebraic integer; conjugate
`≈ −28.93 < −2`). This was a careful reading with numerical tests (exact
rational, big-integer and `ℚ(√17)` arithmetic; floating-point grids not
interval-certified), not a formal verification or an external review; the
end of Section 11.4 of the article records it in full.

## What is not claimed

From the source, kept in the article (collected in Section 1.1):

- No multiplicative equivalent `a(n) ~ cΓⁿn^{−α}`, no positive amplitude, no
  correction series, no transseries; "a factor exp(o(log n)) need not
  converge".
- Non-D-finiteness excludes only a fixed-order polynomial-coefficient
  differential equation (equivalently recurrence); it does not rule out the
  exact multistate recurrence. No claim about arbitrary non-arithmetic
  D-finite functions.
- The inverse's constant `−(α/g) log g` "lies below the proved error scale"
  and is not claimed.
- Lemma 5.1 is not an endpoint limit theorem at the cone vertex; no survival
  equivalent or limiting constant; no killed-cone local limit theorem, no
  i.i.d. cone theorem, no random regeneration time.
- The finite checks do not prove the functional or local limit theorems, the
  harmonic measure, the annular transfer, bridge tightness, the logarithmic
  theorem, G-function regularity or the non-D-finiteness deduction;
  agreement with the 17 OEIS terms is not a proof of the source bijection;
  the annular example parameters (`q = 2`, `H = 8`, `b = 4`, `T = 1`,
  `δ = 1/8`) are illustrative.
- Bostan–Raschel–Salvy (JCTA 121 (2014), Thm 3) is cited for comparison
  only. The result "should be compared with subsequent specialist work
  before any publication or priority claim". The manifest "is an integrity
  record, not a digital signature". No third-party PDF is redistributed.

The write adds: the source's readings of the literature are not checked by
ProveIt; the intake's numerical observations are uncertified floating point.

## Further questions

Section 11.4 of the article ("Further questions and research",
`osr:sec:further`) states every unproved claim of the source as an open
question, with its sketch and what is missing (Vladimir's standing rule of
4 October 2026). The intake found **no false claim** in the source.

1. **The full equivalent** (`osr:q:equivalent`; source item 1): the
   amplitude part of the Asinowski–Cardinal–Felsner–Fusy conjecture. Pointer:
   **Report 125** of the same bundle (A279571,
   `A279571_Leading_Equivalent_and_Harmonic_Constant_Source.zip`; now Part I
   of `a279571-inversion-cone-walk`, with Report 123 as Part II) proves a leading equivalent `a_n ~ C_A 9ⁿ n^{−κ}` for an
   exact two-colour quadrant walk of the same kind, via killed harmonic
   functions, a deep-entrance argument and midpoint reversal; a natural
   model, not checked to transfer. *Observation, not a claim:*
   `a(n) Γ^{−n} n^α = 4.154, 4.418, 4.557, 4.604, 4.627, 4.641, 4.651` at
   `n = 50, 100, 200, 300, 400, 500, 599` (intake double-precision run of
   the recurrence), still increasing; consistent with the conjecture.
2. **Harmonic functions and the amplitude** (`osr:q:harmonic`; item 2).
3. **A quantitative error term** (`osr:q:error`; item 3).
4. **Corrections and further singular contributions** (`osr:q:corrections`;
   item 4).
5. **A bounded-term inverse** with rounding (`osr:q:inverse`; item 5).
6. **The condensed steps 3 and 4** (`osr:q:sketches`): the bridge limit and
   tightness of Lemma 5.1, and the uniformity arguments of Section 7.2.
7. **External inputs and priority** (`osr:q:external`).

## Checks made at intake

On copies (5 October 2026; Windows, Python 3.14.4, standard library only):

- At placement, in the delivered layout: `checks/CHECKSUMS.sha256` 9/9 OK;
  `integrity.py` PASS (22 files, strict inventory); `verify_report111.py`
  and `-O` PASS (394,716 guards); `mutation_campaign.py` PASS (54 mutations,
  108 rejected runs, about 4 minutes); `integrity_corruption_test.py` PASS
  (24 rejections). Every output equals the recorded one after removal of the
  carriage returns that Windows redirection adds.
- At the write, on a copy of the **shipped** files (route B below): the
  checker, normal and `-O`, byte-identical to `data/verification_normal.json`
  after CR removal (about 1 s each).
- Not run: `build.py` (TeX Live format build; it also rewrites the PDF),
  `replay.py` and `seal.py` (they need `report111_source_checks.zip`, which
  `seal.py` creates and the package does not ship).
- An independent intake script: the step table from the two weak
  inequalities, `a(0..16)`, `A` and its characteristic polynomial, `r`, `π`,
  `m`, `h`, `Σ` (also as a finite-difference Hessian of `log λ`), `ρ`, `α`,
  the quadratic `u² + 29u + 2`, and the float run to `n = 599` quoted above.
  All agree.
- The delivered text builds with MiKTeX pdfLaTeX in 18 pages, with one
  duplicate destination (`page.1`, title page) and one underfull line in the
  bibliography; both are removed in this build.

## Relation to the repository

**Formal status.** No statement of this report is formalized in Lean or
Rocq, and its place in the collection confers no formal status.

**Neighbouring reports:**

- `a377922-corner-polyhedra-schnyder` (same collection).
  - Part I's Lemma `cps:lem:nonD` derives non-D-finiteness from two-sided
    bounds `Θ(μⁿn^{−α})`; Section 10 here needs only `μⁿn^{−α+o(1)}`, and
    Remark 10.1 states the general criterion, of which `cps:lem:nonD` is the
    special case. The irrationality certificate differs from
    `cps:lem:irrational` (there `2 cos θ` is a rational non-integer; here it
    is an algebraic integer, and the certificate is its conjugate below −2).
  - **Part III** (Report 112 of the same bundle, file prefix `47-logcone-`,
    labels `cps:log:`; written by ProveIt in `9b4001d29`, after this report)
    proves the method of Sections 3–8 as a general cone theorem for
    finite-phase Markov-additive walks with exponential-tail jumps (its
    Theorem 2.1, printed there as Theorem 24.1, `cps:log:thm:cone`,
    hypotheses (H1)–(H5); Report 112's Section k is Section k + 22 there).
    Remark 1.2 checks that this walk satisfies (H1)–(H5), so the exponent of
    Theorem 1.1 also follows from that theorem; this report is the earlier
    (bundle index 08:51 against 09:26 UTC), model-specific proof with
    bounded steps. Its non-D-finiteness argument is that of Report 112's
    Section 5 (Section 27 there; the criterion in general is Remark 27.1,
    `cps:log:rem:criterion`). Neither source manuscript cites the other;
    ProveIt's write of Part III cites Remarks 1.2 and 10.1 here in its
    Section 22.5 (`cps:log:sec:siblings`). (Updated 5 October 2026 after
    Part III was written; this bullet first said "written concurrently with
    this report" and "Neither cites the other.")
- `Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/`
  (`p0:thm:lambert-core`): the inverse is an instance (Remark 9.1); no
  novelty is claimed for the inversion mechanics.
- `a113226-vincular-avoiders`: a different vincular pattern (12-34); no
  shared question.
- `a279571-inversion-cone-walk` (A279571; bundle Reports 125 and 123,
  batch 104). Its Part II (Report 123) proves the A279571 exponent by the
  same logarithmic-scale argument as this report, model by model, for a
  two-colour walk with unbounded steps; its Part I (Report 125) is the model
  named in Question 1, which as written needs `p > 2` and `4 < p < 5`
  (its Remark 26.4), while here `p ≈ 1.957`. A dated note in Question 1 of
  the article says so. *[5 October 2026; this bullet first read "Report 125
  (A279571, later batch): see Question 1."]*
- `a333497-historic-trees` (dated note, 7 October 2026, batch-103
  reciprocal note). Its Part III (bundle Report 115, batch 103) proves that
  the exponential generating functions of A333497 and A336009 are not
  D-finite, so that neither sequence is P-recursive (Theorem 30.1 there), by
  a different method: windings about the dominant singularity produce
  infinitely many linearly independent germs, which no linear ODE allows.
  Section 10 here argues from the growth exponent instead (Remark 10.1).
  Only the type of conclusion is shared; no theorem or lemma.

**Stale claims.** The manuscript makes no claim about the repository. Before
batch 103 no file mentioned A348351, one-sided or area-universal
rectangulations, or the Asinowski–Cardinal–Felsner–Fusy paper. Nothing to
correct.

## Notation

A table in Section 1.1 fixes the letters the manuscript reuses, with
tempting false readings: `J` (the arc `[θ/3, 2θ/3]` and the number of
crossings), `R` (radius scale, `R = Γ^{−1}`, the colour `R`), `T` (time
cutoff, Fourier matrix), `H` (seed height, `H(t) = F(Rt)`, `H_f`, a
horizon), `L` (`n − 1`, `log y`), `E`/`N` (steps; `N(y)`), `p`
(`π/θ`, `p_cd(v)`), `s` (`√17`, survival `s_n(c)`, an exponent), `c`/`C`
(colours, constants, the conjectured amplitude), `q` (annulus ratio, a
rational exponent), `A`, `a`/`b`/`B`, `F`/`G`, `u`, `β`. No symbol was
renamed. Neighbours: `a377922` Part I writes `μ` for the growth constant and
`p = π/θ = α − 1` (the same normalization); Report 112 writes `Γ` and
`ν = π/θ`.

## Labels

Every label carries the prefix `osr:` ("one-sided rectangulations"; no
`osr:` label existed in the repository). The manuscript's 55 labels (`eq:`
42, `sec:` 10, `lem:` 2, `thm:` 1) were prefixed before anything cited them,
and every reference was updated (37 `\eqref`, 5 `\ref`). The write added 12:
`osr:sec:provenance`, `osr:sec:further`, `osr:rem:cone`, `osr:rem:lambert`,
`osr:rem:criterion`, and the seven questions `osr:q:equivalent`,
`osr:q:harmonic`, `osr:q:error`, `osr:q:corrections`, `osr:q:inverse`,
`osr:q:sketches`, `osr:q:external`. The report has 67 labels; a build of the
delivered text and of this one give every delivered label the same number
(aux files compared). No statement, proof or number of the manuscript was
changed. After the write, the independent check of 5 October 2026 added an
unlabelled dated paragraph at the end of Section 11.4, made the range of
`δ_t` explicit in the step-2 note (marked there), clarified Remark 10.1,
and updated the references to Part III of `a377922-corner-polyhedra-schnyder`
in Remarks 1.2 and 10.1 and Question 6 (dated note in Remark 1.2); no label
was added or renumbered (aux files of the previous and the new build
compared).

## Files

```text
README.md                                     this guide (replaces the delivery README)
article.tex                                   the report (delivered report111.tex; labels prefixed, [write] additions)
article.pdf                                   compiled report, 25 pages
checks-README.md                              the checks README (delivered checks/README.md)
VALIDATION.md                                 validation summary (delivered checks/VALIDATION.md)
code/verify_report111.py                      exact finite checker (delivered checks/)
code/mutation_campaign.py                     54-mutation corruption campaign (delivered checks/)
code/build.py                                 deterministic two-build PDF check, TeX Live (delivered at the root)
code/integrity.py                             strict inventory and SHA-256 manifest check (delivered at the root)
code/integrity_corruption_test.py             manifest corruption test (delivered at the root)
code/replay.py                                fresh-archive replay (delivered at the root)
code/seal.py                                  writes the manifest archive (delivered at the root)
data/report111_fixture.json                   fixture: step table, exact constants, 17 OEIS terms (delivered checks/); OEIS part CC BY-SA 4.0
data/verification_normal.json                 recorded checker output (delivered checks/)
data/mutation_results.json                    recorded campaign output (delivered checks/)
data/validation-build_environment.json        build environment record (delivered validation/build_environment.json)
data/validation-integrity_corruption_results.json  corruption-test record (delivered validation/)
data/validation-quality_summary.json          quality summary (delivered validation/)
data/validation-sources.json                  source-location record (delivered validation/sources.json)
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to the delivery.

**Not shipped**, all recoverable from the arrival commit's archive (next
section): `report111.pdf`, the delivered 18-page PDF (383,004 bytes);
`manifest.json` (3,314 bytes) and `checks/CHECKSUMS.sha256` (789 bytes),
checksum manifests (repository policy ships none; both verified at
placement); `checks/verification_optimized.json` and
`checks/mutation_results_optimized.json`, byte copies of the shipped
`verification_normal.json` and `mutation_results.json`; and the delivery
`README.md` (2,746 bytes), staged at placement and replaced by this guide
(its content is kept under "From the delivery README" below).

**Delivered text that names the delivery layout or files not shipped.**
`checks-README.md` gives commands `python3 checks/verify_report111.py` and
`checks/mutation_campaign.py` from the report directory and names
`report111_fixture.json` beside the checker and `CHECKSUMS.sha256`;
`VALIDATION.md` names `CHECKSUMS.sha256`, `mutation_results_optimized.json`
and `verification_optimized.json` and records the SHA-256 of the delivered
`checks/README.md` (identical bytes to `checks-README.md`). Section 11.1 of
the article describes "the accompanying source-checks package". In the code,
`verify_report111.py` reads `report111_fixture.json` from its own directory
(`--fixture PATH` overrides); `mutation_campaign.py` hashes
`verify_report111.py`, `report111_fixture.json`, itself and `README.md` in
its own directory; `integrity.py`, `integrity_corruption_test.py`,
`replay.py` and `seal.py` take their own directory as the package root and
need `manifest.json`, `report111.tex`, `report111.pdf` and the `checks/` and
`validation/` layout; `build.py` builds `report111.tex` and rewrites
`report111.pdf`. **In the shipped layout nothing runs in place**; use the
routes below.

**Third-party data.** The 17 terms `a(0..16)` in
`data/report111_fixture.json` (and echoed in `data/verification_normal.json`)
are from The On-Line Encyclopedia of Integer Sequences
(https://oeis.org/A348351). OEIS content is published by The OEIS Foundation
Inc. under the Creative Commons Attribution-ShareAlike 4.0 licence
(CC BY-SA 4.0); these terms are third-party data under that licence, not
MIT-0 like the rest of the repository.

## Retrieving the delivered package

```sh
T=$(mktemp -d)
git -C /path/to/ProveIt show 60f54ea06:docs/incoming/A348351_Rectangulations_Exponent_and_Non_D_Finiteness_Source.zip > "$T/a.zip"
sha256sum "$T/a.zip"     # e3f191bd1fdd87e5275303ad2d7431134315761466ccfbe8020428dda098143b, 436,299 bytes
cd "$T" && unzip -q a.zip && cd report111
ls -l report111.pdf      # 383,004 bytes, 18 pages
```

## Rerun the checks (on a scratch copy)

Requirements: Python 3.9 or later, standard library only; no network. Never
run anything in the repository.

**Route A, delivered layout** (the integrity, corruption, replay and sealing
scripts need it):

```sh
cd "$T/report111"
python3 integrity.py                       # strict inventory and manifest
python3 checks/verify_report111.py > "$T/normal.json"
python3 -O checks/verify_report111.py > "$T/opt.json"
cmp "$T/normal.json" checks/verification_normal.json
python3 checks/mutation_campaign.py > "$T/mut.json"   # about 4 minutes
cmp "$T/mut.json" checks/mutation_results.json
python3 integrity_corruption_test.py > "$T/ict.json"
cmp "$T/ict.json" validation/integrity_corruption_results.json
```

`replay.py` needs `report111_source_checks.zip`, which `seal.py` writes into
the package directory (`python3 seal.py`, then
`python3 replay.py --out "$T/replay"`); the replay ends with a PDF rebuild
that requires the recorded TeX Live (see below). The intake did not run
these two.

**Route B, from the shipped files** (tested at the write):

```sh
R=/path/to/ProveIt/SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a348351-one-sided-rectangulations
T=$(mktemp -d); mkdir -p "$T/pkg" "$T/out"
cp "$R/code/verify_report111.py" "$R/code/mutation_campaign.py" "$R/data/report111_fixture.json" "$T/pkg/"
cp "$R/checks-README.md" "$T/pkg/README.md"      # the campaign hashes README.md
cd "$T/pkg"
python3 verify_report111.py > "$T/out/normal.json"
python3 -O verify_report111.py > "$T/out/opt.json"
cmp "$T/out/normal.json" "$R/data/verification_normal.json"
python3 mutation_campaign.py > "$T/out/mut.json"    # optional, about 4 minutes
cmp "$T/out/mut.json" "$R/data/mutation_results.json"
```

At the write both checker runs matched (about 1 s each); the campaign was
run at placement in route A, not again here.

**Windows notes.** Shell redirection of the JSON output writes CRLF line
endings, so compare after stripping CR (`tr -d '\r' < out.json | cmp -
recorded.json`); the content is identical. Use `py` where `python3` is not
on the path. `build.py` is not usable with MiKTeX (it builds a format with
`pdftex -ini … pdflatex.ini`).

## Build the PDF

pdfLaTeX (lmodern, microtype, amsmath, amssymb, amsthm, mathtools, booktabs,
array, geometry, enumitem, fancyhdr, hyperref, and longtable for the write's
notation table); the bibliography is embedded.

```sh
B=$(mktemp -d); cp article.tex "$B/"; cd "$B"
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built this way with MiKTeX on 5 October 2026
(rebuilt the same day after the independent check, with four pdfLaTeX
passes; every label keeps its number): 25 pages;
no errors or warnings, no undefined references or citations, no multiply
defined labels, no duplicate PDF destinations, no overfull or underfull
boxes. The delivered source built the same way gives 18 pages. The article
keeps the delivered preamble lines that suppress PDF dates and trailer
identifiers; the delivered `build.py` and its byte-identity check
(SHA-256 of the delivered PDF recorded in
`data/validation-quality_summary.json`) apply to the delivered
`report111.tex` under TeX Live 2025/dev, not to this build.

## From the delivery README

The delivery README (replaced by this guide) described the package as "the
article `report111.tex`, its final `report111.pdf`, source-location records,
and exact finite checks", stressed that "the programs are finite validation,
not proof assistants for the asymptotic probability arguments", listed the
three results above, and said: "The multiplicative equivalent, positive
amplitude, correction series, and transseries remain unproved here", and
non-D-finiteness "does not exclude the exact multistate recurrence included
in the article". Its instructions, translated to the shipped names:

- *Commands* (from the package root, Python 3.10 or newer):
  `python3 integrity.py`; `python3 checks/verify_report111.py` and with
  `-O`; `python3 checks/mutation_campaign.py`; `python3 build.py` (two clean
  builds, byte identity required); `python3 replay.py --archive … --out …`
  (here route A; the scripts are in `code/`, the recorded outputs in
  `data/`).
- *Environment:* standard library only; pdfTeX with the packages of the
  preamble; "Exact byte identity is required for the same TeX installation;
  a different TeX version or font package can legitimately produce a
  different binary PDF."
- *Sources:* "No network access or third-party source PDF is needed for the
  replay"; the primary references should be consulted for the source
  bijection and the two external theorems; URLs and locations in
  `validation/sources.json` (here `data/validation-sources.json`). "The
  manifest is an integrity record, not a digital signature or a mathematical
  correctness certificate."

## Provenance

- Sources cited by the manuscript: OEIS A348351 (terms through `n = 16`,
  checked 2 October 2026); Asinowski, Cardinal, Felsner and Fusy,
  Combinatorial Theory 5(1) (2025), art. 14 (DOI 10.5070/C65165025);
  Whitt, Probability Surveys 4 (2007) 268–302; Fischler and Rivoal,
  Comment. Math. Helv. 89 (2014) 313–341; Bostan, Raschel and Salvy, JCTA
  121 (2014) 45–63 (comparison only).
- Repository input: none; the package names no ProveIt commit or path.
- Batch 103 of `docs/incoming`, bundle Report 111; arrival `60f54ea06`,
  placement `9c995cefe`, written 5 October 2026. Single source, so the write
  made no merge choices. The delivered `report111.tex` is shipped as
  `article.tex`; the delivered checks, packaging scripts and records are in
  `code/` and `data/` as listed above.
