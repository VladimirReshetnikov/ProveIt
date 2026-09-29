# Dyadic Scaling Rigidity and Log-Periodic Growth of 3AP-Free Permutations

**OEIS A003407: a continuous log-periodic growth profile, its exact fundamental period, real-scale rigidity, explicit 2:1 gluing losses and gains, and the empirical and sampling laws**

This is a research report dated 28 September 2026, built from one
manuscript. Author line: "Research article prepared for Vladimir
Reshetnikov".

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 (only) | batch 40, manuscript 06 | `ProveIt_Dyadic_Scaling_Rigidity` (arrived in `017e6c0d8`; 20-page PDF) | `74f7f5bdb` | `afb2d1227` | the whole article, apart from text marked `[write]` |

**Status.** AI-assisted and unrefereed. **Not formalized**: none of the
report's own theorems has a Lean or Rocq proof. Two inputs it takes from
the literature are proved in Lean in ProveIt (see "Formal status" below);
placement in the collection, near that Lean development, gives the report
itself no formal status.

```
article.tex                     the report, standalone LaTeX with an internal bibliography (pdfLaTeX)
article.pdf                     the compiled report, 25 pages (title page, contents pages 2-3,
                                Sections 1-14 from page 4, appendix, references)
README.md                       this guide
SOURCE_AND_PROOF_AUDIT.md       the manuscript's source and proof audit, as delivered
code/verify.py                  exact integer checks and independent small counts (standard library only)
code/plot_profile.py            regenerates the figure (NumPy, Matplotlib)
code/build.sh                   the delivered two-pass pdfLaTeX build (see below: does not work from code/)
data/counts.txt                 OEIS A003407 b-file values, n = 0..200 (201 rows, three comment lines)
data/verification.json          the delivered record of `verify.py --max-n 32`
figures/profile_enclosure.pdf   the figure included by the article
figures/profile_enclosure.png   the same figure as a PNG
```

Delivery names and shipped paths: `verify.py` -> `code/verify.py`,
`plot_profile.py` -> `code/plot_profile.py`, `build.sh` -> `code/build.sh`,
`verification.json` (package root) -> `data/verification.json`;
`data/counts.txt`, `figures/*` and `SOURCE_AND_PROOF_AUDIT.md` keep their
delivered paths. All of these are byte-identical to the delivery. Not
shipped: the delivered `article.pdf` (this directory's PDF is a build of the
written `article.tex`), the delivered `README.md` (replaced by this file; it
is in the placement commit `afb2d1227`), and the checksum ledger
`SHA256SUMS.txt` (11/11 verified at placement, then retired by repository
policy).

Delivered files whose text still uses delivery names:
`SOURCE_AND_PROOF_AUDIT.md` names `verify.py` and `verification.json` at the
package root and speaks of `python verify.py --max-n 32`;
`code/plot_profile.py` says "Run after verify.py" and writes
`figures/profile_enclosure.{pdf,png}` next to itself; `code/build.sh`
builds `article.tex` in its own directory. The article's own delivered text
(Section 10.1 and the appendix) also uses the flat names; `[write]` notes
there point to the shipped paths.

## Labels

Every label in `article.tex` carries the prefix `dsr:`. The manuscript's 71
labels were given the prefix when the report was written (every `\ref` and
`\eqref` was updated with them); seven labels were added with the `[write]`
text (`dsr:sec:repo`, `dsr:rem:stale-catalogue`, `dsr:sec:notation`,
`dsr:rem:inputs-formal`, `dsr:rem:ratio`, `dsr:sec:formal`,
`dsr:sec:provenance`): 78 in total. No other label was renamed or removed.

## What is claimed

Let theta(n) count permutations of [n] with no three-term arithmetic
progression as a subsequence (OEIS A003407), and a_n = log theta(n).

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

## What is not claimed

Kept from the manuscript: no priority over the literature is certified (the
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
decided; no non-D-finiteness or natural-boundary claim; a Python assertion
is not a proof-assistant proof; the manuscript's formalization route is a
plan, not an executed formalization.

## Formal status

ProveIt's Lean development of the three source papers is under
`Combinatorics/Ramsey/Lean/` (namespaces `LeanProofs.*`; paths below are
relative to that directory). The declarations named in Section 11 of the
article, checked at the current tree, which is unchanged in that directory
since the pin `74f7f5bdb`:

- `LeanProofs.Sharma2012.theorem_2_8_holds`
  (`Sharma2012/FinalConsequences.lean:23`; statement
  `Sharma2012/Statements.lean:272`): theta(n) <= 21 theta(ceil(n/2))
  theta(floor(n/2)) for n >= 3 — the theorem the manuscript imports
  (its case n = 2 is outside the Lean statement).
- `LeanProofs.DavisEntringerGrahamSimmons1977.even_count_recurrence_holds`
  and `odd_count_recurrence_holds`
  (`DavisEntringerGrahamSimmons1977/CountingRecurrences.lean:252, 485`): the
  parity lower recurrence that the article's Lemma 2.2 reproves. Restated as
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
  (theta(n+1) <= floor((n+3)/2) theta(n), stronger than the article's
  deletion bound), `LeanProofs.LeSaulnierVijay2011.M_ratio_does_not_tend_to_two_holds`
  (the ratio does not tend to 2; the article's Remark 9.2 derives, without
  formalization, that it has no limit at all), and Sharma's
  `open_problem_1` (monotonicity, open) and `open_problem_2` (convergence of
  theta(n)^(1/n); answered negatively by Ho and by the article, not
  formalized), which have no proof declarations by design.

No Lean build or axiom audit was run for this report. **Not formalized:**
every result of the article itself — the profile, modulus, spectrum and
band theorems, the exact period, real-scale rigidity, the gluing
certificates, the empirical and sampling laws, the binary-descent identity,
and soundness of the subset-state enumeration. The certificates use counts
100 <= n <= 200 that ProveIt does not certify.

The manuscript's own audit and its Section 1.3 read only the Lean statement
catalogues and concluded that the recurrences must be taken from the
literature; that conclusion is stale (it was already stale at the pin). The
article corrects it in `[write]` Remark 1.1 and Section 11; the delivered
`SOURCE_AND_PROOF_AUDIT.md` is left as delivered.

## Setting and notation

Section 1.5 of the article has the table. The ones to watch: theta(n) is the
Lean `Sharma2012.theta n` and the Davis et al./LeSaulnier–Vijay `M n`, but
the article's `M(x)` in Theorem 7.3 is a limiting Cesàro mean, not that
count; `R(x)` (interpolated toll) is not the certificate ratios `R_±`; `C`,
`C_f`, `C(S)` are three different objects; `L`, `U`, `D` are the constants
log 2, log 21, log(21/2), not lim inf/lim sup of a_n/n (those are p_±). No
symbol of the manuscript was renamed.

## Neighbouring reports

No other report in the collections treats A003407 or 3AP-free
permutations (searched: A003407, 3AP, Sharma, LeSaulnier, Entringer across
the research-report and surreal collections and the research programmes).
Among the single-sequence reports of `oeis-sequence-asymptotics/`, the
closest contrast is `a158415-growth-constant`, where a growth constant is
proved to exist; here none exists and the periodic profile replaces it.
The formal neighbour is `Combinatorics/Ramsey/Lean/` (above).

## Building

In a scratch directory holding `article.tex` and
`figures/profile_enclosure.pdf`:

    latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex

The committed PDF was built this way with MiKTeX pdfLaTeX: 25 pages, 0
errors, 0 warnings, 0 overfull or underfull boxes, no undefined or
multiply-defined references and no duplicate destinations. `code/build.sh`
changes to its own directory and so finds no `article.tex` there; run its
two `pdflatex` commands from the report root (or a copy) instead.

## Rerunning the checks

Never run the scripts in place: `code/verify.py` resolves its data as
`<its own directory>/data/counts.txt` (so it fails in `code/`), and it would
write `verification.json` next to itself; `plot_profile.py` overwrites
`figures/`. Restore the delivered flat layout on a copy:

    mkdir run && cd run
    cp <report>/code/verify.py <report>/code/plot_profile.py .
    mkdir data figures && cp <report>/data/counts.txt data/
    py verify.py --max-n 32 --output rerun.json     # Python >= 3.10, standard library; not with -O
    uv run --no-project --with numpy --with matplotlib python plot_profile.py

When this report was written, both ran on such a copy: `verify.py` passed in
a few seconds and `rerun.json` equals `data/verification.json` apart from its
timing (`seconds`) fields; `plot_profile.py` regenerated the two figure
files. `--max-n` accepts 0 to 36; larger limits make the subset-state
enumeration much more expensive.

## Discrepancies

- The delivered audit and README say ProveIt's catalogue declarations were
  not established as proved; they were (see Formal status).
- The Lean namespace is `Sharma2012`; the article cites the paper as
  Electron. J. Combin. 16(1) (2009), R63, and the Lean file header calls it
  Sharma (2009). Same paper.
- `data/verification.json` was written by the delivered run at the package
  root; its `seconds` fields are machine timings.
