# Corner Polyhedra and Schnyder Labelings

**Polynomial exponents, non-D-finiteness and limiting amplitudes for OEIS
A377922, A377920 and A377921 (Fusy–Narmanli–Schaeffer Conjecture 25), and a
log-scale cone theorem for walks with a finite internal state**

A research report dated 2 October 2026, built from three manuscripts, each
printed in full; Part III was added on 5 October 2026. Part I's author line
is "Research note"; Part II's is "Research addendum" (its PDF metadata also
say "Research note"); Part III's is "Research report 112" (bundle Report
112). None names a tool or an author.

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 45 | batch 77, manuscript 45 | `oeis-bimodal-cone-research.zip`, arrival commit `096ee7b87` (wrapper `oeis-bimodal-cone-report/`, main file `article.tex`, 15-page PDF; PDF and `SHA256SUMS` not shipped) | none: no ProveIt commit is named; the only repository input was a GitHub code search, which returned nothing | `aa7345800` | Part I: Sections 1–10, Appendix A |
| 46 | batch 77, manuscript 46 | `oeis-bimodal-full-asymptotics.zip`, arrival commit `096ee7b87` (wrapper `oeis-bimodal-amplitude-report/`, main file `addendum.tex`, 14-page PDF; manuscript, PDF, README, `SHA256SUMS`, `build.sh`, `requirements.txt` and the embedded Foundation copy not shipped) | none: no ProveIt commit is named; the repository input is source 45's code search | `aa7345800` | Part II: Sections 11–21 |
| 47 | batch 103, cluster 103-A377922, manuscript 01; bundle Report 112 | `Geometric_OEIS_Sequences_Cone_Exponents_and_Inverses_Source.zip`, arrival commit `60f54ea06` (wrapper `report112/`, main file `report112.tex`, 19-page PDF; manuscript, PDF, README and `manifest.json` not shipped) | none: no ProveIt commit, path or search is named | `9c995cefe` | Part III: Sections 22–32 (Section 22 a guide written at the write) |

**Status:** AI-assisted? Not stated by either delivery. Unrefereed, not
formalized. Both parts are backed by exact symbolic checks and finite
enumeration (coefficients through `n = 30`); these check identities,
normalizations and indexing, not the limit theorems. The shipped mathematical
reviews are the deliveries' own, not external peer review.

Source 46 is an addendum to source 45: it embeds an unchanged copy of all 30
files of source 45's package (byte-identical at placement), cites it as "the
Foundation", and does not repeat its proofs. The copy is not shipped; source
45 is printed once, as Part I.

Source 47 (bundle Report 112, 2 October 2026) was written in a different
session about eight hours later and shows no knowledge of sources 45 and 46.
It proves the exponents again, on the logarithmic scale, as instances of a
general theorem; its statements about the three sequences are weaker than
Parts I–II and are printed as a second route, its new material in full.

## What it proves

`p_n` counts corner polyhedra with `n + 3` flats (polyhedral orientations
with `n` inner vertices, A377922), `s_n` counts 3-connected Schnyder
labelings with `n` inner faces (A377920), and `s̃_n` counts rigid orthogonal
surfaces (A377921), indexed as in Fusy–Narmanli–Schaeffer (Electron. J.
Combin. 30(2) (2023), P2.17). Put `μ_P = 9/2`, `μ_S = 16/3`,
`α_P = 1 + π/arccos(9/16) = 4.227476082…` and
`α_S = 1 + π/arccos(22/27) = 6.080304846…`.

**Part I (source 45)**
- `p_n = Θ(μ_P^n n^(-α_P))` and `s_n = Θ(μ_S^n n^(-α_S))` on the full
  integer sequence (Theorem 1.1). This proves the exponents of
  Fusy–Narmanli–Schaeffer's Conjecture 25. The method regenerates at
  returns to a parity state, uses a one-unit buffer for excursions within a
  cycle (Lemma 4.1), a random-clock transfer, a Fourier local limit and an
  interior gluing argument.
- Both exponents are irrational, and the ordinary generating functions of
  A377922, A377920 and A377921 are not D-finite (Corollary 9.4), by a
  positive-derivative criterion that works from `Θ` bounds.
- First-threshold inverses `N(Y) = (log Y + α log log Y)/log μ + O(1)`,
  without monotonicity (Lemma 9.5).

**Part II (source 46)**
- Finite positive constants `κ_P`, `κ_S` with
  `p_n ~ κ_P μ_P^n n^(-α_P)`, `s_n ~ κ_S μ_S^n n^(-α_S)` and
  `s̃_n ~ (16/19)^3 κ_S μ_S^n n^(-α_S)` (Theorem 11.1): the two
  positive-amplitude equivalents of Conjecture 25, and a coefficientwise
  equivalent for A377921 by a dominated signed convolution.
- On the way: a boundary-shift comparison of harmonic functions (Lemma
  14.1), harmonic and endpoint limits for valid cycles (Theorem 15.1), exact
  counted-time survival constants (Theorem 16.1), a uniform interior killed
  local limit (Lemma 17.1), fixed-endpoint bridge amplitudes (Theorem 18.1)
  with the universal Brownian factor evaluated (Section 18.1), and the
  amplitude formulas (19.1) and (19.3).
- A Lambert-`W_{-1}` inverse with a vanishing-width two-ceiling bracket
  (Theorem 20.1).

**Part III (source 47, bundle Report 112)**
- Theorem 24.1 (Report 112's Theorem 2.1): a cone theorem for a
  Markov-additive chain on `Z² × E` with a finite internal state (phase) set
  `E` and unbounded steps with a uniform exponential moment, killed on leaving
  the closed quadrant. Under hypotheses (H1)–(H5) (primitive phase matrix,
  exponential moment, zero drift and positive definite covariance, no
  secondary Fourier eigenvalue, legal seeds from both endpoint phases),
  `K_n((0,a),(0,b)) = n^(-1-π/θ+o(1))` at every integer time; under
  (H1)–(H4) the survival bound `P(τ > n) ≤ C_ε n^(-ν/2+ε)`. The method:
  martingale functional limit theorem, Fourier-matrix local limit theorem,
  an exact-time interior bridge (Lemma 24.2), Brownian wedge crossings over
  geometric annuli and two first-hit prefixes glued at the exact time. New to
  the report; Parts I–II disclaimed such a theorem.
- Proposition 29.1: an explicit six-face sleeve injection from Schnyder
  labelings of size `n` into those of size `n + 6` with non-isolated outer
  white vertices, hence `s_{n-6} ≤ s̃_n ≤ s_n` for `n ≥ 8`. New. With Part
  I's Theorem 1.1 it gives `s̃_n = Θ(μ_S^n n^(-α_S))` (Remark 29.3, proved at
  the write).
- Non-D-finiteness from the logarithmic law alone: nonnegative integer
  coefficients with `a_n = Γ^n n^(-α+o(1))`, `α` irrational, are not those
  of a D-finite series (Section 27; stated in general in Remark 27.1, at the
  write). Part I's Lemma 9.2 needs `Θ` bounds.
- The fixed-endpoint sandwich `e_{n-1} ≤ p_n ≤ e_{n+1}` (25.6), `e_L` the
  corner paths of length `L` from `(0,0)` to `(1,1)`; the exponential-moment
  certificate `189/13` for a whole Schnyder aggregate (26.7); the bounds
  `4 < α_P < 5`, `6 < α_S < 7`; three references not cited in Parts I–II
  (Denisov–Zhang 2025, Grama–Lauvergnat–Le Page 2020, Pham–Peigné–Son 2026).
- A second route, weaker than Parts I–II, to everything Report 112 says about
  the sequences: `p_n = μ_P^n n^(-α_P+o(1))`, the same for `s_n` and `s̃_n`,
  non-D-finiteness of the three generating functions, and first-threshold
  inverses with error `o(log log Y)` (Theorem 23.1). Table 2 maps every
  result of Report 112 to its counterpart in Parts I–II.
- *[Independent check, 5 October 2026.]* An adversarial check made by the
  intake after the write (`9b4001d29`) found all seven items it examined
  valid: the write's Remarks 22.1, 27.1, 29.3 and 29.4, and, as spot checks
  of Report 112, the sleeve Proposition 29.1, the moment certificates
  `189/13` and `524/405`, and the bounds `4 < α_P < 5`, `6 < α_S < 7`. It
  found no counterexample and no gap in any proof chain. Four refinements
  were adopted where they stand: Table 3's row `m, h` now says half-scale
  drift and corrector (only covariances are quarter-scale; the row `G, C`
  had the same slip and is corrected likewise); in Remark 27.1 the
  coefficient of `t^(n-m)` in `H^(m)` carries `R^n`, not `R^(n-m)` (dated
  note after the remark; the constant factor `R^m` changes nothing else);
  the remark now says that the irrationality of `α_P` and `α_S` is still
  used, proved at the start of Section 27; and it says why `R = 1/Γ` is
  algebraic (Pringsheim's theorem and the leading coefficient of the minimal
  operator). The Fischler–Rivoal locators ("Theorem 6", "Corollary 1",
  pp. 328–329) are right for the journal version that the bibliography
  names; in arXiv:1103.6022v2 the same results are Theorem 3 (§4.1) and
  Corollary 1 (§4.2), and the bibliography entry now gives both numberings.
  The tests, none of which used the delivered or the write's programs: exact
  SymPy recomputation of both kernel sets (Part III's `P(u, v)`, `G(u, v)`
  and Part I's `K_P`, `K_S`), reproducing every drift, corrector and
  covariance of Remark 22.1 and the factor 4 in both phases; a symbolic check
  of Remark 29.4 against Remark 20 of Fusy–Narmanli–Schaeffer
  (arXiv:2202.09172v3) and of the convolution `s_n = b_n + 3b_{n-1} +
  3b_{n-2} + b_{n-3}` on the OEIS terms for `n = 4..30`; the sleeve
  sandwich `s_{n-6} ≤ b_n ≤ s_n` on the OEIS terms for `n = 6..30` (no
  violation; smallest `b_n/s_{n-6}` is 14, at `n = 8`), with the sleeve's
  definitions compared with that paper's Section 2.1; `189/13` and
  `524/405` recomputed exactly; and the bounds on `α_P`, `α_S` verified by
  exact integer comparisons (mpmath: `α_P = 4.2274760821…`,
  `α_S = 6.0803048461…`). Its record is an unlabelled dated paragraph at
  the end of Section 31: a careful reading with exact computations and data
  checks, not a formal verification.

## What is not claimed

- **No numerical digits** of `κ_P` or `κ_S`, no rate of convergence and no
  correction term (Part II). The amplitudes are characterized by positive
  killed-harmonic and Brownian heat-kernel expressions; only the universal
  Brownian factor is evaluated.
- No unconditional rounding formula `N(Y) = ⌈r(Y)⌉` (Part II); Part I's
  inverse has `O(1)` error and no next additive constant.
- **A377923** (its OEIS entry was exported with the others) is a different
  sequence and is outside both theorems.
- No general cone theorem for Markov-modulated walks: the argument uses a
  fixed cycle buffer specific to these two tandem-walk models. Part II
  assumes no cone-killed local theorem for the two-state chain.
  *[5 October 2026]* True of Parts I–II only. Part III's Theorem 24.1 is a
  general cone theorem for walks with a finite internal state, at the
  logarithmic scale; the report still has no general amplitude or `Θ`
  theorem (Questions Q1–Q2 of Section 31.1).
- Part III keeps all of Report 112's non-claims: no amplitude, no full
  equivalent, no rate for the `o(1)` of Theorem 24.1, no claim at endpoint
  phases without seeds, no `O(1)` inverse of its own; its finite checks
  certify algebra and finite ranges, not the cone theorem, the limit
  theorems, the sleeve injection for all maps or any asymptotic.
- The counting bijections and conjectures are Fusy–Narmanli–Schaeffer's,
  the iid cone input (Theorems 2–3 of *Random walks in cones revisited*) is
  Denisov–Wachtel's, the non-D-finiteness step uses the
  André–Chudnovsky–Katz theorem in Fischler–Rivoal's form, and the
  Brownian cone kernel is Bañuelos–Smits'. **Neither source claims
  publication priority**; both literature checks are bounded snapshots
  (2 October 2026, 01:22–01:39 UTC) that do not establish novelty.
- Finite computations corroborate formulas and indexing; they do not prove
  the cycle lemma, the probabilistic estimates or any limit.

Part I's text (its abstract, Sections 1, 9 and 10) says that the amplitudes
are unresolved and that no coefficientwise estimate for A377921 follows.
Those sentences
describe source 45's own scope and are printed unchanged; dated `[write]`
notes point to Part II. Still open after the merge: the values of `κ_P` and
`κ_S`, rates, corrections, exact rounding, and other parity-dependent tandem
models with a fixed cycle buffer (Part I, Section 10). *[5 October 2026]*
For the last item, Part III's Theorem 24.1 gives the logarithmic-scale
exponent for every chain satisfying (H1)–(H5), with or without a buffer;
amplitudes and `Θ` bounds for such chains remain open.

Report 112 (Part III) likewise calls the logarithmic power "the advance
established here" and lists amplitudes, the limit of `s̃_n/s_n` and an
`O(1)` inverse as open. It did not know Parts I–II, which settle all three
(Theorem 11.1 and (11.4), giving the limit `(16/19)^3`; Lemma 9.5). Those
sentences are printed unchanged with dated notes; Section 31 records which
of Report 112's questions remain open, and Section 31.1 adds the write's
own (an amplitude and a `Θ` form of Theorem 24.1, endpoints without seeds,
steps not independently rechecked). No claim of Report 112 was found wrong.

**Inversion mechanics.** Lemma 9.5 and Theorem 20.1 are instances of the
transseries volume
`Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/transseries_and_inversion.tex`:
the model equation `λr − α log r = log(Y/γ)` is `p0:thm:lambert-core`
(`a = log μ`, `b = −α`, branch `W_{-1}`), its expansion is the first step
of `p0:thm:lambert-centered`, and the ceiling bracket is the separation
situation of `p0:thm:staircase`. No novelty is claimed for the inversion
mechanics; dated notes in Sections 9.2 and 20 say so. Part III's inverse
(23.4), with error `o(log log Y)`, is the same instance at logarithmic
precision (dated note in Section 28).

## Notation

Both manuscripts use the same normalizations (`μ`, `α`, `L`, `K_P`, `K_S`,
`q_n`, `Σ_P`, `Σ_S` per counted step, `θ`, `p = π/θ = α − 1`). No symbol was
renamed and no normalization changed. Several letters clash; Table 1 of the
guide lists them with the tempting false readings. The dangerous ones:

- Part II's `D` is the valid complete-cycle kernel; Part I's `D` is the
  denominator `(1 − 1/(3x²))(1 − y²/3)`, which Part II calls `D_P`.
- Part II's `T = (2Σ)^(-1/2)` is a whitening matrix; Part I's `T(z)` is the
  generating function of A377921, which Part II calls `S̃(z)`.
- Part II's `𝓗` is a harmonic function; Part I's `H` (Part II's `H_S`) is
  the denominator of the Schnyder kernel.
- Part I's `A(z)` is a generating function, Part II's `A(a)` a survival
  amplitude; Part I's `β = k − α`, Part II's `β` a survival constant.
- In both parts the roman `e` is the even parity state, not Euler's number.

Part III keeps Report 112's letters and has its own clash table (Table 3,
Section 22.4). The dangerous ones:

- Report 112 works in half-scale (quotient) coordinates, `x = 2U + c`, so
  its `Σ_P`, `Σ_S` and phase covariances `V^P_c`, `V^S_c` are **one quarter**
  of the matrices with the same names in Parts I–II (Remark 22.1, proved at
  the write, also converts drifts and correctors). Correlations, angles and
  exponents agree.
- Its `Γ_P`, `Γ_S` are `μ_P`, `μ_S`; its `ν = π/θ` is `p` (Part II's `ν` is a
  probability law); its phases `0`, `1` are the states `e`, `o`; its `e_L`
  is a path count, and its `e^t` is Euler's number.
- Its `A`, `F`, `J`, `W`, `T`, `D`, `G`, `C`, `H`, `κ`, `E`, `K_n` and
  `b_n` mean other things than the same letters in Parts I–II; Table 3 lists
  them.

## Relation to the repository

**Formal status.** No statement of this report, Part III included, is
formalized in Lean or Rocq, and its place in the collection gives it no
formal status. The only
related formal statement is the generic staircase lemma
`Fabius.staircase_separation` in
`Analysis/FabiusFunction/Lean/FabiusFunction/StaircaseInversion.lean`, which
concerns an arbitrary monotone interpolation, not these sequences.

**Neighbouring reports.** No other report mentions these sequences,
Schnyder labelings or corner polyhedra (repository search, 2 October 2026).
No other report cites Denisov–Wachtel's cone theorems. The closest in
subject is `a227578-ordered-rook-paths`, which counts lattice walks in a
Weyl chamber by exact coefficient identities and mentions, without using,
the Denisov–FitzGerald harmonic determinant; no theorem is shared. This
pointer is made here only.

*[5 October 2026]* Two bundle reports of the same day use Part III's method
model by model: Report 111, the report `a348351-one-sided-rectangulations`
in this directory (placed in `9c995cefe`), for one-sided rectangulations
(A348351), and Report 123, for the inversion-sequence class A279571
(arrival `60f54ea06`; Part II of `a279571-inversion-cone-walk`, placed in
`612787fb4` and written in batch 104, beside Report 125 as Part I; this
parenthesis first read "not yet placed"). The a348351 report's Remark 1.2
(`osr:rem:cone`) checks that its bounded-step four-colour walk satisfies
(H1)–(H5), so its exponent is an instance of Theorem 24.1
(`cps:log:thm:cone`); its Remark 10.1 (`osr:rem:criterion`) generalizes
Part I's Lemma 9.2 (`cps:lem:nonD`) to `μⁿn^(−α+o(1))`, as Part III's Remark
27.1 does; its irrationality certificate (a conjugate of `2cos θ` below
`−2`) differs from Lemma 9.1. Neither Report 111 nor Report 112 cites the
other; Section 22.5 and a dated note after Lemma 9.2 say so. The reports
share no text and stay separate.

*[5 October 2026, batch-104 reciprocal note]* `a279571-inversion-cone-walk`
checks Theorem 24.1's hypotheses for Report 123's walk (its Remark 26.1):
(H1)–(H4) hold, but (H5) fails at the origin endpoints (the stationary dual
has no seed there, and the kernel into the origin vanishes), so Report 123's
exponent is an instance of the theorem's proof, not of its statement. Its
Proposition 26.2 states the theorem at arbitrary fixed endpoint states, and
the independent check of that report (`1c7e526c7`) confirmed that it follows
from the proof of Theorem 24.1 unchanged. Its Part I (Report 125) proves, for
that one walk, the amplitude form asked by Question Q1 (`cps:log:q:amplitude`;
it uses `4 < ν < 5`), and the walk is an example for Question Q3
(`cps:log:q:seeds`). Dated notes in Section 22.5 and in Q1 and Q3 say so.

**Stale delivery statements.** Both literature receipts
(`45-cone-literature-status.md`, `46-amp-literature-status.md`) and
`data/45-cone-public-overlap-check.json` record that a GitHub code search of
ProveIt for A377920, A377921, A377922, "Schnyder" and "corner polyhedra"
returned nothing. That was true on 2 October 2026 before placement; the only
matches now are this report's files.

Report 112 (Part III) names no ProveIt path or search. Its claims that
amplitudes, the `s̃_n/s_n` limit and an `O(1)` inverse are open, and that no
theorem covers these kernels with a full equivalent, describe the
literature it checked; Parts I–II settle them for these two models (dated
notes in Sections 23, 30 and 31).

## Labels

Part I's labels carry the prefix `cps:` (source 45's 73 labels, prefixed
before anything cited them); Part II's carry `cps:amp:` (source 46's 78
labels). The merge added four: `cps:sec:guide`, `cps:tab:notation`,
`cps:part:exponents`, `cps:part:amplitudes`. Total 155 before Part III.
Part III added 86: `cps:part:logcone`, Report 112's 67 labels with the
prefix `cps:log:`, and 18 of the write (`cps:log:sec:guide`, `…:sec:new`,
`…:sec:provenance`, `…:sec:printing`, `…:sec:notation`, `…:sec:siblings`,
`…:tab:map`, `…:tab:notation`, `…:rem:scale`, `…:rem:criterion`,
`…:rem:theta`, `…:rem:rigid`, `…:sec:questions`, `…:q:amplitude`,
`…:q:theta`, `…:q:seeds`, `…:q:unchecked`, `…:q:rates`). Total 241; no
earlier label was renamed, lost or renumbered (checked against a build of
the previous text). Every label keeps its
source number: Part I's numbers are source 45's (checked against a build of
the delivered `article.tex`), and Part II's are source 46's with 10 added to
the section number (checked against a build of `addendum.tex`).

Apart from labels, the only changes to the manuscripts' text are: source
46's eight references to the Foundation (one citation, seven numbered
references), which became cross-references with the same numbers
("Foundation Lemma 2.1" is Lemma 2.1 here); its citation key `DW`, which
became source 45's `DWrevisited` (the same paper); and ten dated `[write]`
notes (five in Part I's body, one in Appendix A, four in Part II). The editorial guide before Part I is unnumbered. No statement,
proof, symbol or number of either manuscript was changed.

Part III prints Report 112 in full as Sections 23–32 (its Section `k` is
Section `k + 22`, its Theorem 2.1 is Theorem 24.1, its Proposition 7.1 is
Proposition 29.1); Section 22 is a guide written at the write, with the map
table (Table 2), the clash table (Table 3) and Remark 22.1. Apart from
labels, macro names (`\E`, `\R`, `\Z`, `\Q`, `\C` mapped to this
report's), the omitted title block, contents and running heads, and the
citation key `DW` (now `DWrevisited`), nothing of Report 112 was changed;
its equations are numbered within sections. The write added 29 notes dated
`[write, 2026-10-05]`: six in the guide before Part I (and a dated
paragraph in the abstract), four in Part I, one in Part II, eighteen in
Part III, and four remarks of its own in Part III (22.1, 27.1, 29.3,
29.4) and the further questions of Section 31.1. After the intake's
independent check of 5 October 2026: one formula of Remark 27.1 corrected,
with a dated note after the remark keeping its first wording; two rows of
Table 3 corrected and two sentences of Remark 27.1 clarified, each marked
"[corrected at the independent check]"; one sentence added to question Q4,
marked "[added at the independent check]"; a sentence in Section 22 pointing
to the record;
the Fischler–Rivoal bibliography entry extended with the arXiv numbering;
and an unlabelled dated paragraph, "Independent check of the write", at the
end of Section 31. No label was added, renamed or renumbered.

## Files

```text
README.md                                    this guide (replaces both delivery READMEs)
article.tex                                  the report (source 45 delivered as article.tex, source 46 as addendum.tex, source 47 as report112.tex)
article.pdf                                  compiled report, 66 pages
45-cone-literature-status.md                 source 45: bounded literature and overlap receipt (as delivered)
45-cone-mathematical-verification.md         source 45: the delivery's own mathematical review (as delivered)
46-amp-integrated-mathematical-review.md     source 46: the delivery's own review of the addendum with the Foundation
46-amp-literature-status.md                  source 46: literature snapshot (source 45's, with a preface)
47-logcone-checks-README.md                  source 47: what each exact check does and does not prove (delivered checks/README.md)
47-logcone-checks-VALIDATION_SUMMARY.md      source 47: reader validation summary (delivered checks/VALIDATION_SUMMARY.md)
code/45-cone-run_all.py                      Part I: runs the four checks below, writes results/verification-summary.json
code/45-cone-verify_symbols.py               Part I: exact kernels, correctors, covariances, cycle laws, angles (SymPy)
code/45-cone-independent_corner_checks.py    Part I: separate P algebra, 25,900 bounded cycle shapes, p_n to n = 15
code/45-cone-independent_schnyder_checks.py  Part I: separate S resolvent, moments, direct aggregate enumeration to n = 14
code/45-cone-enumerate_schnyder.py           Part I: weighted recurrence to n = 30, compared with sources/A377920.seq
code/45-cone-build.sh                        Part I: two-pass pdfLaTeX build of a delivery-layout article.tex
code/46-amp-run_all.py                       Part II: integrity check, new algebra, isolated Foundation replay
code/46-amp-verify_foundation.py             Part II: hashes the embedded Foundation copy (not shipped; see below)
code/46-amp-verify_addendum.py               Part II: exact Brownian/Gamma, determinant, multiplier and inverse checks
code/47-logcone-checks-validate.py           Part III: kernels, moments, Fourier witnesses, seeds, original-walk counts, sleeve (SymPy)
code/47-logcone-checks-verify_sleeve.py      Part III: finite sleeve graph, colours, labels and root recovery (imported by validate.py)
code/47-logcone-checks-run_validation.py     Part III: 57 named mutants in two modes and a fresh-directory replay
code/47-logcone-integrity.py                 Part III: checks the package against manifest.json (not shipped)
code/47-logcone-integrity_corruption_test.py Part III: corruption tests of integrity.py on temporary copies
code/47-logcone-build.py                     Part III: double clean pdfTeX build of report112.tex (not shipped), byte equality required
code/47-logcone-replay.py                    Part III: fresh replay from the original archive, PDF rebuild included
code/47-logcone-seal.py                      Part III: rebuilds a deterministic ZIP from manifest.json
data/45-cone-A377920.seq                     Part I: OEIS entry A377920 (s_n), oeisdata export da8d37c6 (CC BY-SA 4.0)
data/45-cone-A377921.seq                     Part I: OEIS entry A377921 (rigid surfaces), same export
data/45-cone-A377922.seq                     Part I: OEIS entry A377922 (p_n), same export
data/45-cone-A377923.seq                     Part I: OEIS entry A377923 (outside both theorems), same export
data/45-cone-provenance.json                 Part I: export commit, source URLs, sizes and SHA-256 of the four entries
data/45-cone-public-overlap-check.json       Part I: GitHub code-search receipts (ProveIt: 0 hits on 2 October 2026)
data/45-cone-requirements.txt                Part I: sympy>=1.12,<2
data/45-cone-symbolic-checks.json            Part I: recorded output of verify_symbols.py
data/45-cone-verify_symbols.stdout.txt       Part I: its stdout
data/45-cone-independent-corner-checks.json  Part I: recorded output of independent_corner_checks.py
data/45-cone-independent_corner_checks.stdout.txt
data/45-cone-independent-schnyder-checks.json  Part I: recorded output of independent_schnyder_checks.py
data/45-cone-independent_schnyder_checks.stdout.txt
data/45-cone-schnyder-enumeration.json       Part I: s'_n, s_n, s̃_n to n = 30
data/45-cone-enumerate_schnyder.stdout.txt   Part I: its stdout
data/45-cone-verification-summary.json       Part I: run_all.py summary (Python 3.12.14, SymPy 1.14.0)
data/45-cone-mathematical-verification.json  Part I: hash-bound receipt of the review
data/45-cone-visual-validation.json          Part I: layout check of the unshipped 15-page PDF
data/46-amp-addendum-symbolic-checks.json    Part II: recorded output of verify_addendum.py
data/46-amp-verify_addendum.stdout.txt       Part II: its stdout (byte-identical to the JSON)
data/46-amp-verify_foundation.stdout.txt     Part II: "PASS: 30 unchanged Foundation files …"
data/46-amp-foundation-replay.stdout.txt     Part II: stdout of the Foundation replay
data/46-amp-verification-summary.json        Part II: run_all.py summary (Python 3.12.14, SymPy 1.14.0)
data/46-amp-integrated-mathematical-review.json  Part II: hash-bound receipt of the review
data/46-amp-provenance.json                  Part II: Foundation hashes and source provenance
data/46-amp-visual-validation.json           Part II: layout check of the unshipped 14-page PDF
data/47-logcone-checks-fixtures.json         Part III: expected rationals, seeds, finite prefixes (OEIS terms, CC BY-SA 4.0), scope limits
data/47-logcone-checks-requirements.txt      Part III: sympy==1.14.0
data/47-logcone-checks-results-ordinary.json Part III: recorded output of validate.py --json
data/47-logcone-checks-results-ordinary.log  Part III: its stdout
data/47-logcone-checks-results-optimized.json  Part III: the same under python -O
data/47-logcone-checks-results-optimized.log Part III: its stdout
data/47-logcone-checks-results-validation_manifest.json  Part III: every mutant, diagnostic and hash of run_validation.py
data/47-logcone-checks-results-fresh_replay_manifest.json  Part III: the fresh-directory rerun
data/47-logcone-checks-results-fresh_replay.log  Part III: its summary
data/47-logcone-validation-integrity_campaign.json  Part III: recorded output of integrity_corruption_test.py (12 cases, 24 rejections)
data/47-logcone-validation-quality_summary.json  Part III: reader-facing scope (proved / not proved)
data/47-logcone-validation-sources.json      Part III: source ledger with locators
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to its delivery. The delivered files have LF line endings.

**Renames.** Placement prefixed every shipped name of source 45 except
`article.tex` and `README.md` (since replaced) with `45-cone-`, and every
shipped name of source 46 with `46-amp-`. Scripts went from `scripts/` (and
`build.sh` from the package root) to `code/`; `results/*`, `sources/*`,
`requirements.txt` and `audit/*.json` to `data/`; `audit/*.md` and source
46's `sources/literature-status.md` to the report root. Source 47's files
carry `47-logcone-` followed by their delivered path with `/` replaced by
`-` (so `checks/results/ordinary.json` is
`data/47-logcone-checks-results-ordinary.json`): programs in `code/`,
fixtures, requirements and records in `data/`, the two notes of `checks/`
at the report root.

**Not shipped** (all in the arrival commit): both delivered PDFs; both
`SHA256SUMS` ledgers (verified 29/29 and 49/49 at placement); source 46's
manuscript, README, `build.sh`, `requirements.txt` (identical to source
45's), its embedded 30-file Foundation copy, and
`results/foundation-integrity.json` (a SHA-256 ledger of that copy).
Source 47's `report112.tex`, `report112.pdf`, `README.md` and
`manifest.json` (a SHA-256 and size inventory of 25 files, verified 25/25
at placement), all in arrival commit `60f54ea06`. Its
`checks/requirements.txt` is a one-line pin that occurs many times in the
repository; it is shipped for this report as delivered.

**Delivered text that still uses delivery names.**
- The article's Appendix A and Section 10, and source 45's delivered README
  (replaced), name `scripts/run_all.py`, `build.sh`, `results/`, `sources/`
  and the package PDF; dated notes in Section 10 and Appendix A say so.
- `code/45-cone-*.py` resolve `scripts/`, `results/` and `sources/`
  relative to their parent directory; `code/45-cone-build.sh` builds
  `article.tex` beside itself.
- `code/46-amp-run_all.py` and `code/46-amp-verify_foundation.py` need
  `foundation/` with its `SHA256SUMS`, `article.pdf` and
  `audit/mathematical-verification.json`, none of which is shipped in that
  layout. Part II's Section 21 (dated note added) describes that package.
- The two review receipts, both review markdown files,
  `46-amp-provenance.json` and the two visual-validation records name and
  hash `article.tex`, `article.pdf`, `addendum.tex`, `addendum.pdf`,
  `foundation/…` and `results/foundation-integrity.json` at their delivery
  paths. The shipped `article.tex` is the merged report, not the reviewed
  source (SHA-256 `849e5150…`); the reviewed sources are in the arrival
  commit.
- `46-amp-literature-status.md` points to
  `foundation/sources/public-overlap-check.json`, shipped as
  `data/45-cone-public-overlap-check.json`.
- Source 47's two notes and its records name `checks/validate.py`,
  `checks/results/…`, `report112.tex`, `report112.pdf`, `manifest.json` and
  `report112_source_checks.zip` (the archive's build name; it was delivered
  as `Geometric_OEIS_Sequences_Cone_Exponents_and_Inverses_Source.zip`).
  `validate.py` imports `verify_sleeve` and reads `fixtures.json` beside
  itself; `integrity.py`, `integrity_corruption_test.py` and `seal.py` need
  `manifest.json`; `build.py` needs `report112.tex`; `replay.py` needs the
  archive. Part III's Sections 31–32 describe that package; a dated note in
  Section 32 says what is shipped.

## Rerunning the checks

Run on scratch copies, never in place: the scripts write `results/` beside
their parent directory, so running them from `code/` would create a
`results/` directory in the report and fail on the missing `sources/`.
On Windows the outputs have CRLF line endings; compare modulo CR
(`diff --strip-trailing-cr`).

**Part I** (from this directory, Git Bash):

```sh
R=$(mktemp -d) && mkdir "$R/scripts" "$R/sources"
for f in run_all verify_symbols independent_corner_checks independent_schnyder_checks enumerate_schnyder; do
  cp code/45-cone-$f.py "$R/scripts/$f.py"; done
for s in A377920 A377921 A377922 A377923; do cp data/45-cone-$s.seq "$R/sources/$s.seq"; done
(cd "$R" && uv run --no-project --with sympy==1.14.0 python scripts/run_all.py)
for f in "$R"/results/*; do diff -q --strip-trailing-cr "$f" "data/45-cone-$(basename "$f")"; done
```

On 2 October 2026 this took 49 s here and passed. All eight outputs equalled
the recorded ones modulo CR; `verification-summary.json` differed only in its
Python version (3.13.5 here, 3.12.14 recorded).

**Part II, new algebra only** (needs nothing else):

```sh
R=$(mktemp -d) && mkdir "$R/scripts" && cp code/46-amp-verify_addendum.py "$R/scripts/verify_addendum.py"
(cd "$R" && uv run --no-project --with sympy==1.14.0 python scripts/verify_addendum.py)
diff --strip-trailing-cr "$R/results/addendum-symbolic-checks.json" data/46-amp-addendum-symbolic-checks.json
```

This took 33 s and matched modulo CR.

**Part II, complete suite** (needs the Foundation copy, so run it from the
delivered archive):

```sh
R=$(mktemp -d) && git show 096ee7b87:docs/incoming/oeis-bimodal-full-asymptotics.zip > "$R/a.zip"
cd "$R" && unzip -q a.zip && cd oeis-bimodal-amplitude-report
uv run --no-project --with sympy==1.14.0 python scripts/run_all.py
```

On Windows this stops at `scripts/run_all.py` line 27 with
`AssertionError: symbolic-checks.json`. That line compares the replayed
Foundation outputs with the delivered ones byte for byte, and Windows text
mode writes CRLF. Every check before it passes (integrity of the 30
Foundation files, the new algebra, the four Foundation programs), and every
output equals the delivered one modulo CR (119 s here on 2 October 2026; the
placement run took 88 s). On a POSIX system it should pass as delivered. Do
not run the archive's `build.sh` scripts in the repository.

**Part III, exact checks** (from this directory, Git Bash; restores the
delivered `checks/` names):

```sh
R=$(mktemp -d) && mkdir "$R/checks"
cp code/47-logcone-checks-validate.py "$R/checks/validate.py"
cp code/47-logcone-checks-verify_sleeve.py "$R/checks/verify_sleeve.py"
cp data/47-logcone-checks-fixtures.json "$R/checks/fixtures.json"
cd "$R" && uv run --no-project --with sympy==1.14.0 python checks/validate.py > ordinary.log
uv run --no-project --with sympy==1.14.0 python checks/validate.py --json ordinary.json > /dev/null
cd - && diff --strip-trailing-cr "$R/ordinary.log" data/47-logcone-checks-results-ordinary.log
diff --strip-trailing-cr "$R/ordinary.json" data/47-logcone-checks-results-ordinary.json
```

On 5 October 2026 both runs took 8 s together here and matched the recorded
log and JSON modulo CR. Add `-O` after `python` for the optimized records.

**Part III, complete package** (integrity, mutation campaign, corruption
tests; run from the archive, preferably on a POSIX system):

```sh
R=$(mktemp -d) && git show 60f54ea06:docs/incoming/Geometric_OEIS_Sequences_Cone_Exponents_and_Inverses_Source.zip > "$R/a.zip"
cd "$R" && unzip -q a.zip && cd report112
python3 integrity.py && python3 checks/validate.py && python3 integrity_corruption_test.py
python3 checks/run_validation.py --output ../rv-out
```

At placement (on a copy, Windows) `integrity.py` passed 25/25,
`integrity_corruption_test.py` passed in both modes (12 cases, 24
rejections), and `run_validation.py` rejected all 57 mutants with their
expected diagnostics and reproduced the recorded baselines modulo CR; its
nested fresh-directory replay was cut by a 15-minute time box, so the
replay manifest was not regenerated. `build.py` and `replay.py` were not
run: they require pdfTeX from TeX Live 2025 for a byte-identical PDF, and
`replay.py` the archive under its build name (pass `--archive`). Never run
`run_validation.py` without `--output` in a directory whose
`checks/results/` should be kept: it rewrites them.

The archive of source 45 can be retrieved the same way:
`git show 096ee7b87:docs/incoming/oeis-bimodal-cone-research.zip`. No
delivered file was excluded as a heavy artifact (the largest is 46 KB), so
nothing needs reconstructing.

## Build the PDF

pdfLaTeX with Latin Modern, amsmath, amssymb, amsthm, mathtools, booktabs,
array, longtable, microtype, enumitem, xcolor and hyperref. From this
directory:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built in a scratch directory with MiKTeX on 5
October 2026 (rebuilt after the batch-104 reciprocal notes). It has 66 pages
(title and contents 1–4, guide 5–8, Part I 9–22, Part II 23–36, Part III
37–64, Appendix A 64–65, references 66), with
no errors, no undefined references or citations, no multiply defined
labels, no duplicate PDF destinations and no overfull boxes. Three
underfull lines remain in one `[write]` note of Section 20, as before Part
III; Part III adds none. The delivered manuscripts alone build without box
warnings.

## Provenance

- Source 45: batch 77 of `docs/incoming`, manuscript 45, archive
  `oeis-bimodal-cone-research.zip`; arrival `096ee7b87`, placement
  `aa7345800`, written in the batch-77 write phase (2 October 2026). No pin.
  Inputs: Fusy–Narmanli–Schaeffer (EJC 2023, arXiv:2202.09172v3),
  Denisov–Wachtel (AIHP 2024; Ann. Probab. 2015), Fischler–Rivoal (2014),
  Bostan–Raschel–Salvy (2014), the OEIS entries (oeisdata `da8d37c6`).
- Source 46: batch 77, manuscript 46, archive
  `oeis-bimodal-full-asymptotics.zip`; arrival `096ee7b87`, placement
  `aa7345800`, same write. No pin. Inputs: source 45 (embedded),
  Fusy–Narmanli–Schaeffer, Denisov–Wachtel, Bañuelos–Smits (PTRF 1997).
- Where the merge had to choose:
  - Source 45 is printed once; source 46's embedded copy is not shipped.
  - The guide is unnumbered, so Part I keeps source 45's numbers and the
    numbers in source 46's Foundation references stay correct.
  - Source 46's Section 2 (Section 12 here), a restatement of Part I's
    inputs in its own notation, is kept with a pointer note, because Part
    II cites its displays.
  - Appendix A (source 45's) is placed after Part II.
  - Letters are kept, with a clash table, rather than renamed.
  - One bibliography: source 45's entries, plus Bañuelos–Smits; source 46's
    entries for Fusy–Narmanli–Schaeffer and Denisov–Wachtel are the same
    papers; its `Foundation` entry is replaced by Part I; its uncited `OEIS`
    entry duplicates source 45's two OEIS entries and is omitted. Source 45's
    uncited entry for Denisov–Wachtel 2015 is kept, as delivered.
- Source 47: batch 103 (cluster 103-A377922, manuscript 01), bundle Report
  112, archive `Geometric_OEIS_Sequences_Cone_Exponents_and_Inverses_Source.zip`;
  arrival `60f54ea06`, placement `9c995cefe`, written in the batch-103 write
  phase (5 October 2026). No pin. Inputs: Fusy–Narmanli–Schaeffer,
  Whitt (2007), Fischler–Rivoal, Denisov–Wachtel (2024), Denisov–Zhang
  (2025), Grama–Lauvergnat–Le Page (2020), Pham–Peigné–Son (arXiv
  2603.26228, cited from its abstract), the OEIS entries (CC BY-SA 4.0
  prefixes in `data/47-logcone-checks-fixtures.json`). No "prepared for
  private review" text, sandbox path or personal data.
- Where the Part III write had to choose:
  - Report 112 is printed in full, not reduced to pointers: its statements
    about the sequences are where Theorem 24.1's hypotheses are checked, and
    the new sandwich and moment certificate sit inside them. Table 2 marks
    them as second routes.
  - Its guide is a numbered Section 22, so Report 112's numbers shift by 22.
  - Letters are kept, with a clash table and Remark 22.1 for the factor 4.
  - Its bibliography: Fusy–Narmanli–Schaeffer, Fischler–Rivoal and
    Denisov–Wachtel are the existing entries; Whitt, Denisov–Zhang,
    Grama–Lauvergnat–Le Page and Pham–Peigné–Son are added; its uncited
    OEIS entry is omitted.
