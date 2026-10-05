# Dyadic Scaling Rigidity and Log-Periodic Growth of 3AP-Free Permutations

**OEIS A003407: a continuous log-periodic growth profile, its exact fundamental period, real-scale rigidity, explicit 2:1 gluing losses and gains, the empirical and sampling laws (Part I); non-P-recursiveness of the counts and of every arithmetic section, and non-D-finiteness of both generating functions (Part II)**

This is a research report in two parts, built from two manuscripts. Part I
is dated 28 September 2026 and Part II 29 September 2026. Author line of
both: "Research article prepared for Vladimir Reshetnikov".

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | batch 40, manuscript 06 | `ProveIt_Dyadic_Scaling_Rigidity` (arrived in `017e6c0d8`; 20-page PDF) | `74f7f5bdb` | `afb2d1227` | Part I: Sections 1–14 and Appendix A, apart from text marked `[write]` (written in `d6078387e`) |
| 02 | batch 43, manuscript 06 | `ProveIt_3AP_Nonholonomicity` (*Non-holonomicity of 3AP-Free Permutation Counts: Finite-window rigidity, arithmetic sections, and stable obstructions to polynomial recurrences*; arrived in `acf39bd6d`; 21-page A4 PDF) | `8d936ee23` | `faef2ed2a` | Part II: its title block and abstract, Sections 16–27 and Appendices B–C, apart from text marked `[write]`; Section 15 and Subsection 11.4 are `[write]` |

Source 02 was written against Part I as committed (the report's
`article.tex` and `README.md` are the same blobs at its pin and at its
placement), and it continues Part I's explicit non-claim: Part I's research
item 8 (Section 12) ended "No non-D-finiteness or natural-boundary claim is
proved here". Part II answers the non-D-finiteness half; the natural-boundary
half stays open. Every result, proof, example, question and limitation of
both manuscripts is printed; Part I is unchanged apart from dated pointers
(listed under "Labels" below).

**Status.** AI-assisted and unrefereed. **Not formalized**: no theorem of
either part has a Lean or Rocq proof. Some inputs the two parts take from
the literature are proved in Lean in ProveIt (see "Formal status" below);
placement in the collection, near that Lean development, gives the report
itself no formal status.

```
article.tex                                    the report, standalone LaTeX with an internal bibliography (pdfLaTeX)
article.pdf                                    the compiled report, 51 pages (title page; contents pages 2-4;
                                               Part I, Sections 1-14, pages 5-26; Part II, Sections 15-27,
                                               pages 27-48; Appendices A-C pages 49-50; references pages 50-51)
README.md                                      this guide
SOURCE_AND_PROOF_AUDIT.md                      source 01's source and proof audit, as delivered
02-nonholonomicity-SOURCE_AND_PROOF_AUDIT.md   source 02's source, novelty and claim-status audit, as delivered
code/verify.py                                 source 01: exact integer checks and independent small counts (standard library)
code/plot_profile.py                           source 01: regenerates the figure (NumPy, Matplotlib)
code/build.sh                                  source 01: the delivered two-pass pdfLaTeX build (does not work from code/)
code/02-nonholonomicity-verify.py              source 02: exact verifier, counts n <= 32, Ho's separation, two determinants (standard library)
code/02-nonholonomicity-test_verify.py         source 02: nine unit tests of that verifier (unittest)
code/02-nonholonomicity-build.sh               source 02: the delivered three-pass pdfLaTeX build (does not work from code/)
data/counts.txt                                OEIS A003407 b-file values, n = 0..200 (201 rows, three comment lines)
data/verification.json                         source 01: the delivered record of `verify.py --max-n 32`
data/02-nonholonomicity-verification.json      source 02: the delivered record of its full verifier run (n <= 32, brute force n <= 8)
data/02-nonholonomicity-unit-tests.txt         source 02: the delivered unit-test transcript (9 tests, OK)
figures/profile_enclosure.pdf                  the figure included by the article (Part I)
figures/profile_enclosure.png                  the same figure as a PNG
```

Delivery names and shipped paths, source 01: `verify.py` ->
`code/verify.py`, `plot_profile.py` -> `code/plot_profile.py`, `build.sh`
-> `code/build.sh`, `verification.json` (package root) ->
`data/verification.json`; `data/counts.txt`, `figures/*` and
`SOURCE_AND_PROOF_AUDIT.md` keep their delivered paths. Source 02:
`code/verify.py` -> `code/02-nonholonomicity-verify.py`,
`code/test_verify.py` -> `code/02-nonholonomicity-test_verify.py`,
`build.sh` (package root) -> `code/02-nonholonomicity-build.sh`,
`data/verification.json` -> `data/02-nonholonomicity-verification.json`,
`data/unit-tests.txt` -> `data/02-nonholonomicity-unit-tests.txt`,
`SOURCE_AND_PROOF_AUDIT.md` -> `02-nonholonomicity-SOURCE_AND_PROOF_AUDIT.md`.
All of these are byte-identical to the deliveries. Not shipped: both
delivered `article.pdf` files (this directory's PDF is a build of the
written `article.tex`); source 01's delivered `README.md` (replaced by this
file; it is in the placement commit `afb2d1227`); source 02's delivered
`README.md` and `article.tex` (they survive only in its archive, committed
in `acf39bd6d` and retired from `docs/incoming` in `faef2ed2a`); and
source 01's checksum ledger `SHA256SUMS.txt` (11/11 verified at placement,
then retired by repository policy). Source 02 shipped no checksum ledger.

Delivered files whose text still uses delivery names:
- `SOURCE_AND_PROOF_AUDIT.md` names `verify.py` and `verification.json` at
  the package root and speaks of `python verify.py --max-n 32`;
  `code/plot_profile.py` says "Run after verify.py" and writes
  `figures/profile_enclosure.{pdf,png}` next to itself; `code/build.sh`
  builds `article.tex` in its own directory. Part I's delivered text
  (Section 10.1 and Appendix A) also uses the flat names; `[write]` notes
  there point to the shipped paths.
- `02-nonholonomicity-SOURCE_AND_PROOF_AUDIT.md` names `code/verify.py`,
  `code/test_verify.py`, `data/verification.json` and `data/unit-tests.txt`;
  `code/02-nonholonomicity-test_verify.py` does `from verify import ...`,
  so in place it imports Part I's `code/verify.py` (which has none of those
  names) and fails; `code/02-nonholonomicity-verify.py` writes by default
  to `<report>/data/verification.json`, which is **Part I's record**;
  `code/02-nonholonomicity-build.sh` changes to `code/` and finds no
  `article.tex`. Part II's delivered Section 24.4 gives the delivery
  commands; a `[write]` note there gives the shipped names.

## Labels

Every label in `article.tex` carries the prefix `dsr:`. Part I: the
manuscript's 71 labels were given the prefix when the report was written,
and seven `[write]` labels were added then (`dsr:sec:repo`,
`dsr:rem:stale-catalogue`, `dsr:sec:notation`, `dsr:rem:inputs-formal`,
`dsr:rem:ratio`, `dsr:sec:formal`, `dsr:sec:provenance`): 78. Part II uses
the sub-prefix `dsr:nh:`: source 02's 65 labels were prefixed (every `\ref`
and `\eqref` updated), and 14 labels were added: `dsr:nh:sec:provenance`,
`dsr:nh:sec:source`, `dsr:nh:sec:changes`, `dsr:nh:sec:notation`,
`dsr:nh:sec:relation`, `dsr:nh:sec:choices` (Section 15),
`dsr:nh:sec:formal` (Subsection 11.4), `dsr:nh:sec:conclusion`,
`dsr:nh:app:notation`, and `dsr:nh:q:boundary`, `dsr:nh:q:dalg`,
`dsr:nh:q:profile`, `dsr:nh:q:monotone`, `dsr:nh:q:certified` on five of
its questions. Total 157 (was 78); no label was renamed or removed, and no
section, theorem or equation number of Part I moved (checked against a
build of the previous text).

Part II was inserted after Part I's Section 14 and before Part I's
appendix. Changes to Part I, all dated `[write]` text: a line in the title;
a sentence in the collection note; a contents entry for each part; a
paragraph after Remark 9.2; the new Subsection 11.4; a pointer in research
item 8 of Section 12 and a paragraph after that list; a sentence at the
start of Section 14.1; Part II's macros and `example` environment in the
preamble; notes in the bibliography entries for Ho (journal DOI) and OEIS
(source 02's consultation date); four new bibliography entries used only by
Part II (Stanley; Garoufalidis 2009 and 2011; André).

A batch-85 reciprocal note (3 October 2026) added one bracketed paragraph,
marked "[Added 3 October 2026, batch 85]", after Corollary 19.6
(`dsr:nh:cor:jumps`) in Part II; it adds no label (still 157) and moves no
number. A batch-98 reciprocal note (5 October 2026) added a second bracketed
paragraph, marked "[Added 5 October 2026, batch 98]", after
Question 26.1 (`dsr:nh:q:boundary`); it adds no label and moves no number.

## What is claimed

Let theta(n) count permutations of [n] with no three-term arithmetic
progression as a subsequence (OEIS A003407), and a_n = log theta(n).

**Part I**
- **Profile** (Theorem 3.2; the equal-weight bounded-toll case of
  Hwang–Janson–Tsai, proved here with explicit constants): a unique
  continuous 1-periodic P with `log theta(n) = n P(log_2 n) - Q(n)`,
  `log 2 <= Q <= log 21`, so `e^{nP}/21 <= theta(n) <= e^{nP}/2`; an explicit
  modulus of continuity O(h log(1/h)) (Proposition 3.3).
- **Spectrum and finite-band enclosures** (Theorems 4.1, 4.2): the cluster
  set of theta(n)^{1/n} is [rho_-, rho_+], and published counts for
  100 <= n <= 200 give 2.20499 < rho_- < 2.23760 < 2.28484 < rho_+ < 2.32721.
- **Exact period** (Lemma 5.1, Theorem 5.2): the period group of P is exactly
  Z, certified by 32 strict integer inequalities on published counts
  (theta(128) and theta(n), 152 <= n <= 182) plus two containment inequalities.
- **Real-scale rigidity** (Theorem 6.2): `log theta(floor(cn)) - c log theta(n) = o(n)`
  iff c is an integral power of two; otherwise exponential gain and loss on
  sets of positive lower density. Integer arities: Corollary 6.3.
- **Explicit gluing** (Theorem 6.4): `theta(3n)/(theta(2n)theta(n))` is
  below (49/50)^n for n = 128·2^t and above (21/20)^n for n = 172·2^t, for
  every t >= 0; no subexponential universal gluing (Corollary 6.5).
- **Statistics and sampling** (Sections 7–8): the logarithmic empirical law,
  all ordinary cutoff laws nu_x, nonconvergence of both Cesàro means,
  fine sampling, and the rational/irrational geometric-sampling dichotomy.
- **Adjacent ratios** (Proposition 9.1): the binary-descent identity and
  `2n^{-gamma} <= theta(n+1)/theta(n) <= 2n^{gamma}`, gamma = log_2(21/2),
  with the deletion bound n+1 on the upper side.
- **Verification** (Section 10): the program checks 199 splitting
  inequalities on the table 2 <= n <= 200, the period and gluing
  certificates, two separation inequalities of Ho, exact extremizing-index
  selection and rational root enclosures in the bands [32,64], [64,128],
  [100,200], independent subset-state counts for n <= 32 and brute force for
  n <= 8.

**Part II**
- **Main theorem** (Theorem 16.2, proved in Section 20): for all integers
  q >= 1, r >= 0, the section theta(qn+r) is not P-recursive over C (no
  polynomial recurrence, of any order and degree, valid from any starting
  index); neither `F(z) = sum theta(n) z^n` nor `E(z) = sum theta(n) z^n/n!`
  is D-finite over C(z) (Section 22.1), and F is transcendental
  (Corollary 22.1).
- **Finite-window rigidity** (Lemma 19.3) and **local-growth rigidity**
  (Theorem 19.5): a nonzero leading Nilsson layer forces a fixed-length
  window to have a single exponential scale; hence an eventually positive,
  exponentially bounded, rational P-recursive sequence with exponentially
  growing common denominators and subexponential forward increases has an
  nth-root limit. Corollary 19.6: persistent exponential oscillation needs
  exponentially large upward jumps. Rational descent (Lemma 19.1) reduces
  complex coefficients to rational ones.
- **Route**: deletion bound `theta(n+j) <= (n+j)^j theta(n)` (Lemma 17.1),
  exponential bounds (Lemma 17.3), Ho's nonconvergence reproduced from the
  published theta(64), theta(75) by the exact comparison
  `(2 theta(64))^75 > (21 theta(75))^64` and a log gap > 1/2279
  (Section 18), and the section-limit Lemma 20.1.
- **Stable versions**: no eventually positive integer P-recursive v with
  `log v_n = d log theta(qn+r) + o(n)`, d > 0 (Theorem 16.3; rational v with
  exponentially bounded denominators too); rounded real powers
  (Corollary 21.1); positive polynomial observables of finitely many shifts
  (Theorem 16.4); no nonzero leading Nilsson layer (Corollary 21.2).
- **Profile obstruction** (Proposition 23.1): any positive integer sequence
  with `log u_n = n P(log_b n) + o(n)`, P continuous, nonconstant and
  1-periodic, is not P-recursive; a second route to the base theorem
  through Part I's profile (Section 23.2), and perturbed linear sampling
  (Corollary 23.2).
- **Verification** (Section 24): subset-state counts for n <= 32 (sound by
  Proposition 24.1), brute force for n <= 8, the splitting inequalities
  through 32, Ho's separation and two rational root brackets, and two
  nonzero exact determinants that exclude recurrences in the rectangles
  (order, degree, first row) = (5,3,0) and (4,3,8) only.
- Nine research questions (Section 26) and a formalization plan
  (Section 25.3).

## What is not claimed

Kept from source 01: no priority over the literature is certified (the
new statements "were not found in the sources inspected"); the periodic
profile method is Hwang–Janson–Tsai's and nonexistence of a growth constant
is Boon Suan Ho's (2026); Sharma's Theorem 2.8 is imported, not reproved;
counts beyond n = 32 are published OEIS data (Heinz; Correll–Ho through 90),
not recomputed, and arithmetic checks on them do not certify the enumeration;
finite recurrence checks do not prove the infinite recurrences; P is not
claimed optimal in modulus, differentiable, Lipschitz or nowhere
differentiable; P(0) is not shown to be a global maximum; the numeric bounds
are enclosures, not the extrema; the empirical laws have full support but no
density or absence of atoms is claimed; monotonicity of theta is not
decided; no natural-boundary claim (source 01 also made no
non-D-finiteness claim; answered by Part II on 29 September 2026, batch
43); a Python assertion is not a proof-assistant proof; the manuscript's
formalization route is a plan, not an executed formalization.

Kept from source 02: no novelty is claimed for Ho's nonconvergence theorem,
the G-function regularity theory (Garoufalidis; André, Chudnovsky-type
results; imported, deep, not proved here), the continuous periodic-profile
construction, the descent identity or the subset-state method; the novelty
search was targeted, not exhaustive. theta(64) and theta(75) are published
inputs, not recomputed (the verifier recomputes n <= 32 only). The two
determinants are finite diagnostics, not the proof, and supply no universal
finite certificate. The robust theorem needs integer values or exponentially
bounded common denominators and a pointwise o(n) error; approximants with
unrestricted real coefficients or uncontrolled denominators are not
excluded. Positive polynomial observables need nonnegative coefficients;
signed combinations are not covered. It is not claimed that arbitrary
non-P-recursive sequences have non-P-recursive sections. Not proved: a
natural boundary, differential transcendence (nonlinear differential
equations), infinitely many singularities of F, irrationality or
transcendence of its radius, monotonicity, sharper profile regularity. A
rounded real power with arbitrary d need not come with an effective
algorithm. Not refereed, not formalized.

## Formal status

ProveIt's Lean development of the three source papers is under
`Combinatorics/Ramsey/Lean/` (namespaces `LeanProofs.*`; paths below are
relative to that directory). The declarations named in Section 11 of the
article, checked at the current tree, which is unchanged in that directory
since both pins (`74f7f5bdb`, `8d936ee23`):

- `LeanProofs.Sharma2012.theorem_2_8_holds`
  (`Sharma2012/FinalConsequences.lean:23`; statement
  `Sharma2012/Statements.lean:272`): theta(n) <= 21 theta(ceil(n/2))
  theta(floor(n/2)) for n >= 3 — the theorem both manuscripts import
  (its case n = 2 is outside the Lean statement).
- `LeanProofs.DavisEntringerGrahamSimmons1977.even_count_recurrence_holds`
  and `odd_count_recurrence_holds`
  (`DavisEntringerGrahamSimmons1977/CountingRecurrences.lean:252, 485`): the
  parity lower recurrence that Part I's Lemma 2.2 and Part II's
  Proposition 17.2 reprove. Restated as
  `LeanProofs.Sharma2012.inequality_1_holds` / `inequality_2_holds` and
  `LeanProofs.LeSaulnierVijay2011.M_even_recurrence_holds` /
  `M_odd_recurrence_holds`.
- `LeanProofs.Sharma2012.theta_eq_davis_count`: Sharma's `theta` equals the
  Davis et al. `M` (the article's theta(n)).
- `LeanProofs.Sharma2012.theorem_1_1_holds` (2^(n-1) <= theta(n)), and
  `LeanProofs.DavisEntringerGrahamSimmons1977.table_1_holds` (theta(1..20),
  equal to the first twenty rows of `data/counts.txt`; resting on
  `native_decide` through an `implemented_by` native backend in
  `RamseyPaperCommon/CountCertificates.lean` and `ThreeFreeCounting.lean`, an
  explicit trust boundary).
- Bearing on the discussion: `insertion_count_upper_bound_holds`
  (`DavisEntringerGrahamSimmons1977/Proofs.lean:4824`; theta(n+1) <=
  floor((n+3)/2) theta(n) for n >= 1, stronger than the deletion bound
  theta(n+1) <= (n+1) theta(n) of Part I's Proposition 9.1 and Part II's
  Lemma 17.1: equal at n = 1, strictly smaller for n >= 2),
  `LeanProofs.LeSaulnierVijay2011.M_ratio_does_not_tend_to_two_holds`
  (the ratio does not tend to 2; Part I's Remark 9.2 derives, without
  formalization, that it has no limit at all), and Sharma's
  `open_problem_1` (monotonicity, open) and `open_problem_2` (convergence of
  theta(n)^(1/n); answered negatively by Ho, by Part I and again in Part II's
  Theorem 18.2, not formalized), which have no proof declarations by design.

**Part II** (article Subsection 11.4). It relies on the *statement* of
`theorem_2_8_holds` twice: through theta(n) <= 21^(n-1) (Lemma 17.3, the
exponential bound the G-function input needs) and through the factor 21 in
Ho's separation (the upper enclosure of l_75 in Lemma 18.1); the lower
bounds use the parity recurrences and `theorem_1_1_holds`. The manuscript
imports the published theorem and does not cite the Lean proof. The Lean
`insertion_count_upper_bound_holds` is stronger than Part II's deletion
bound, the one local estimate its main theorem uses. **theta(64) and
theta(75) are published counts that nothing in ProveIt certifies**: the
Lean count table `table_1_holds` stops at n = 20, the Python verifier
recomputes n <= 32, and their agreement with rows 64 and 75 of
`data/counts.txt` (checked when Part II was written) compares the same
published OEIS data. The Ramsey development states nothing about
P-recursiveness or D-finiteness, and ProveIt has no G-function theory.

No Lean build or axiom audit was run for either part. **Not formalized:**
every result of the article itself. Part I: the profile, modulus, spectrum
and band theorems, the exact period, real-scale rigidity, the gluing
certificates, the empirical and sampling laws, the binary-descent identity,
and soundness of the subset-state enumeration; its certificates use counts
100 <= n <= 200 that ProveIt does not certify. Part II: rational descent,
the imported G-function input, finite-window noncancellation, local-growth
rigidity, the section lemma, the main theorem and every extension, the
generating-function and transcendence corollaries, the profile obstruction,
perturbed sampling, and the two determinant certificates (Python only).

Source 01's audit and its Section 1.3 read only the Lean statement
catalogues and concluded that the recurrences must be taken from the
literature; that conclusion is stale (it was already stale at the pin). The
article corrects it in `[write]` Remark 1.1 and Section 11; the delivered
`SOURCE_AND_PROOF_AUDIT.md` is left as delivered. Source 02's audit
correctly treats the Lean names as statements it did not build.

## Setting and notation

Section 1.5 of the article has Part I's table. The ones to watch there:
theta(n) is the Lean `Sharma2012.theta n` and the Davis et al./LeSaulnier–Vijay
`M n`, but the article's `M(x)` in Theorem 7.3 is a limiting Cesàro mean,
not that count; `R(x)` (interpolated toll) is not the certificate ratios
`R_±`; `C`, `C_f`, `C(S)` are three different objects; `L`, `U`, `D` are the
constants log 2, log 21, log(21/2), not lim inf/lim sup of a_n/n (those are
p_±).

Section 15.3 has the table across the two parts. theta, a_n, L, U, D, gamma,
A(x), P, Q and C(S) agree. They differ as follows: Part II's toll is `tau_n`
(Part I's `r_n`), while Part II's `r` is the residue of a section
theta(qn+r); Part II's `T(x)` and `H(x)` are Part I's `R(x)` and `F(x)`,
and Part II's `F(z)`, `E(z)` are generating functions; Part II's `R` is a
Nilsson exponential scale; Part II's `Phi` is a polynomial, Part I's the
phase function; Part II's `b_n` has four local meanings (Part I's is
a_n/n); Part II's `Delta_n` is Part I's `d_n`, and its `d` is an order, an
exponent, a common difference or a degree. No symbol of either manuscript
was renamed.

## Neighbouring reports

No other report in the collections treats A003407 or 3AP-free
permutations (searched: A003407, 3AP, Sharma, LeSaulnier, Entringer across
the research-report and surreal collections and the research programmes).
Among the single-sequence reports of `oeis-sequence-asymptotics/`, the
closest contrast is `a158415-growth-constant`, where a growth constant is
proved to exist; here none exists and the periodic profile replaces it.
The formal neighbour is `Combinatorics/Ramsey/Lean/` (above).

`oeis-sequence-asymptotics/a182220-source-boundary` (batch 85) proves an
elementary counterpart in the other direction to Part II's Corollary 19.6
(`dsr:nh:cor:jumps`, upward exponential jumps are *necessary* for
oscillation in an integer P-recursive sequence): its Lemma 8.1
(`sbd:lem:jump`) shows that a jump after a plateau of every fixed length at
a lower exponential rate is *sufficient* to exclude P-recursiveness, without
integrality or an exponential bound. The source-boundary diagonals of
A182162 satisfy it; theta(n) does not, and this report's Example 22.2
(`dsr:nh:ex:parity`) shows why the plateau hypothesis is needed. Each report
carries a dated note pointing to the other (here after Corollary 19.6).
Since batch 98 (5 October 2026) that report's Part II proves natural boundaries for those diagonals through a general transfer lemma (its
Lemma 18.1, `sbd:edge:lem:transfer`: coherent dyadic blocks with a common
profile nonvanishing at the dyadic roots of unity). A second dated note
here, after Question 26.1 (`dsr:nh:q:boundary`), records that the lemma
bears on that question as a method only: no such block structure is known
for theta(n), and the question stays open.

## Building

In a scratch directory holding `article.tex` and
`figures/profile_enclosure.pdf` (Part II has no figures):

    latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex

The committed PDF was built this way with MiKTeX pdfLaTeX: 51 pages, 0
errors, 0 warnings, 0 overfull or underfull boxes, no undefined or
multiply-defined references and no duplicate destinations. Neither
`code/build.sh` nor `code/02-nonholonomicity-build.sh` works from `code/`
(each changes to its own directory and finds no `article.tex`); run
`pdflatex` from the report root (or a copy) instead.

## Rerunning the checks

Never run the scripts in place. `code/verify.py` resolves its data as
`<its own directory>/data/counts.txt` (so it fails in `code/`) and writes
`verification.json` next to itself; `plot_profile.py` overwrites
`figures/`; `code/02-nonholonomicity-verify.py` would overwrite Part I's
`data/verification.json`, and `code/02-nonholonomicity-test_verify.py`
would import Part I's `code/verify.py`. Restore each delivered layout on a
copy.

Part I:

    mkdir run && cd run
    cp <report>/code/verify.py <report>/code/plot_profile.py .
    mkdir data figures && cp <report>/data/counts.txt data/
    py verify.py --max-n 32 --output rerun.json     # Python >= 3.10, standard library; not with -O
    uv run --no-project --with numpy --with matplotlib python plot_profile.py

When Part I was written, both ran on such a copy: `verify.py` passed in
a few seconds and `rerun.json` equals `data/verification.json` apart from its
timing (`seconds`) fields; `plot_profile.py` regenerated the two figure
files. `--max-n` accepts 0 to 36; larger limits make the subset-state
enumeration much more expensive.

Part II:

    mkdir run2 && cd run2 && mkdir code data
    cp <report>/code/02-nonholonomicity-verify.py code/verify.py
    cp <report>/code/02-nonholonomicity-test_verify.py code/test_verify.py
    py code/verify.py --output rerun.json            # Python >= 3.10, standard library
    py -m unittest discover -s code -p "test_*.py" -v

When Part II was written this passed on such a copy: the verifier took
about 15 seconds, and `rerun.json` equals
`data/02-nonholonomicity-verification.json` apart from `runtime_seconds`;
the nine unit tests passed. Without `--output` the verifier writes
`data/verification.json` under the copy's root. `--max-n 12 --brute-n 7`
gives a quick run.

## Discrepancies

- Source 01's delivered audit and README say ProveIt's catalogue
  declarations were not established as proved; they were (see Formal
  status).
- The Lean namespace is `Sharma2012`; the article cites the paper as
  Electron. J. Combin. 16(1) (2009), R63, and the Lean file header calls it
  Sharma (2009). Same paper.
- `data/verification.json` was written by source 01's delivered run at the
  package root; its `seconds` fields are machine timings.
  `data/02-nonholonomicity-verification.json` records `runtime_seconds`
  10.56; source 02's text says "about eleven seconds".
- Source 02 cites the prior report (now Part I) as a bibliography entry;
  in the article these citations are printed as bracketed references to
  Part I, with that entry's caveat kept in Section 15.2. Its entries for
  works Part I also cites are merged into Part I's; Ho's journal DOI and
  its OEIS consultation date (29 September 2026, against Part I's 28
  September) are kept in those entries.
- Source 02 reproduces Ho's separation from theta(64) and theta(75); within
  this report Part I reaches the same nonconvergence from other published
  counts (theta(128), theta(152..182)). Neither route is certified in
  ProveIt.
- Source 02's Section 25.1 (its Section 10.1) gives the prior report's
  path; that is this directory, and the prior report is Part I.
