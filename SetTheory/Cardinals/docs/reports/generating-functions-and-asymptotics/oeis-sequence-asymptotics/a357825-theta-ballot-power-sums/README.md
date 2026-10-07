# Theta Asymptotics for High-Power Ballot Sums

**OEIS A357825, A357871 and the growing-power array A357824: exact oscillation envelopes, all-orders theta expansions, exponential multiset sectors and inverse asymptotics; Part II: a general lattice-peak transfer theorem for growing power sums**

This research report is dated 1 October 2026, with Part II added on
5 October 2026. It is built from two manuscripts. Part I is manuscript 59 of
batch 73 (cluster O1) of ProveIt's incoming-reports intake; its author line
is "Prepared with ChatGPT as a proposed contribution to the ProveIt research
corpus" (PDF author: "Research article prepared with ChatGPT"). Part II is
the late batch-98 arrival placed as batch 98D (the twelfth manuscript of
batch 98, local number 02); its author line is "Research report for the
ProveIt project", and it does not say whether an AI assistant was used.

| Source | Batch manuscript | Archive | Pin | Arrived | Placed | Printed as |
|---|---|---|---|---|---|---|
| Part I | 73O1, 59 | `OEIS_Theta_Ballot_Sums.zip` (*Theta Asymptotics for High-Power Ballot Sums*, main file `article.tex`, 25-page PDF as delivered) | `50f93367b` | `aa43cc555` | `9df4ba51a` | Part I: Sections 1–11 and Appendices A–B |
| Part II | 98D, 12 (local 02) | `ProveIt_OEIS_Lattice_Peak_Transfer_2026-10-05.zip` (*A Lattice-Peak Transfer Theorem for Growing Power Sums*, main file `ProveIt_OEIS_Lattice_Peak_Transfer.tex`, 641 lines, 14-page PDF) | none named ("checked against the ProveIt default branch on 5 October 2026"; it knows `67d54b7ac`) | `1ec443bc4` | `3b9458b31` | Part II: Sections 12–26 and Appendices C–D |

The pin `50f93367b2859b2727c34c68cf87684c101768cc` is the ProveIt commit the
manuscript inspected (its root README and `Combinatorics/README.md`). The
delivered `source_audit.md` calls it the "inspected tree commit"; it is a
commit. No other manuscript of batch 73 treats these sequences, so nothing
was merged. The delivered README, PDF and `SHA256SUMS` ledger (20/20
verified at placement) are not shipped and survive in `aa43cc555`.

Part II's package held only its article and PDF (no README, code, data or
checksum list), so nothing of it is staged; both survive in the arrival
commit (`git show 1ec443bc4:docs/incoming/ProveIt_OEIS_Lattice_Peak_Transfer_2026-10-05.zip`).
It answers question Q6 of Part I. It is the only manuscript of batch 98 on
these sequences or on the Mahonian power sums.

**Status: Part I AI-assisted, Part II AI provenance unstated; both
unrefereed, not formalized.** The intake reran Part I's verifier on a copy
and checked selected values and the expansion independently (see "Rerunning
the script"). It did not re-derive every Part I proof. Part II's main proofs
were checked by the batch-98 intake and by the write, which completed two of
them and corrected one identity (see "Part II" below).

## Files

```
README.md                         this guide
article.tex                       the report, Parts I and II (LaTeX, internal bibliography)
article.pdf                       the compiled report, 51 pages (unnumbered title page, then pages 1-50)
source_audit.md                   the manuscript's source and claim audit, as delivered
code/verify.py                    exact, symbolic and high-precision checks, tables and plots (SymPy, mpmath, Matplotlib)
code/build.sh                     the delivered build script (runs verify.py --all, then pdflatex three times; see below)
data/requirements.txt             mpmath==1.3.0, sympy==1.14.0, matplotlib==3.10.8
data/software_versions.json       Python 3.13.5 and the three package versions of the recorded run
data/verification_status.json     recorded run: exact-check counts and the numerical settings
data/coefficients.json            the polynomials A_1..A_5, D_1..D_6 and R_0..R_6
data/constants.json               liminf, limsup, mean, Turan liminf/limsup, first-sector constant (55 digits)
data/asymptotic_errors.csv        Table 1: relative errors of the truncations J = 0..6, n = 25..1200
data/exponential_sector.csv       the first exponential sector at n = 20, 30, 40, 60, 80, 100
data/square_transition.csv        the near-square logistic transition, s = 8, 16, 32, d = -2..2
data/inverse_errors.csv           the inverse-expansion errors of Section 9.3
data/plot_data.csv                the 601 points of Figures 1 and 2 (600 <= n <= 1200)
figures/phase_collapse.pdf        Figure 1, regenerated in the write (see below)
figures/oscillation.pdf           Figure 2, regenerated in the write
figures/phase_collapse.png        raster version, as delivered
figures/oscillation.png           raster version, as delivered
```

Every file except `article.tex`, `article.pdf`, `README.md` and the two
figure PDFs is byte-identical to Part I's delivery; every file belongs to
Part I, since Part II ships none. The five CSV files are CRLF
as delivered (kept by `-text` lines in `SetTheory/Cardinals/.gitattributes`);
`data/coefficients.json`, `data/constants.json` and
`data/verification_status.json` have no final newline, as delivered.

## Labels and edits

Every label carries the prefix `tbs:`. The manuscript's 104 labels are kept,
unchanged after the prefix; the write added one, `tbs:sec:collection`
(Section 1.4), so the report has 105. No theorem, section, equation or table
number of the manuscript changed.

The text is printed as delivered, apart from the label prefix and three
notes marked `[Write note, batch 73O1]`: one line on the title page,
Section 1.4 "Place in the ProveIt collection" (provenance, status, shipped
layout, neighbouring material), and a paragraph at the end of Section 9.4 on
the shipped paths of the requirements file and the build script. A fourth
note, `[Write note, batch 77P2, 2 October 2026]`, at the end of question Q6
(Section 10), points to the Mahonian report named below; it adds no label.
The title
page also gained a `\par` after its status box, so that the author line no
longer starts beside the box (a layout defect of the delivered PDF). No
symbol was renamed.

The batch-98D write (5 October 2026) added the Part headings (Part I is the
text above, unchanged), Part II (Sections 12–26, before the appendices, and
Appendices C–D, after Part I's), a table-of-contents line for the
appendices, four bibliography entries (`lptA380275`, `lptWang`, `lptCJZ`,
`lptMahonian`) and three notes dated 5 October 2026 in Part I: in Section
1.4 (a paragraph on Part II), after Theorem 6.2 (an instance of Part II's
theorem) and at the end of question Q6 (answered; the batch-77P2 note's
"this question stays open" is superseded). Part II's 90 labels carry the
prefix `tbs:lpt:`; the report now has **195 labels** (105 before). No
existing label was renamed or removed and no existing number changed (the
`.aux` files of builds before and after agree on all 105 old labels; only
page numbers moved). Section k of Part II's manuscript is Section k+12, its
Appendices A–B are C–D, and every numbered item and equation keeps the
manuscript's number within its section; the write's additions follow the
manuscript's items of their section.

## What is claimed

With B(n,h) the ballot triangle A008315, a_n = Σ_h B(n,h)^n (A357825),
b_n = Σ_h C(B(n,h)+n−1, n) (A357871) and S_{n,k} = Σ_h B(n,h)^k (A357824),
m = n+1, α_n = (√m − (m mod 2))/2 and Θ(α) = Σ_j exp(−4(j−α)^2):

- **Theorem 2.2** (all-orders diagonal expansion):
  a_n/𝒜_n = e^{−5/6}{Σ_{j≤J} m^{−j/2} F_j(α_n) + O_J(m^{−(J+1)/2})}, uniformly
  in the phase, with F_0 = Θ and F_j Gaussian-weighted sums of explicit
  polynomials R_j (R_1, R_2 printed; R_3, R_4 in Appendix A; R_0..R_6 in
  `data/coefficients.json`). 𝒜_n = 2^{n²+3n/2}/(π^{n/2} e^{n/2} n^n) is
  Kotesovec's normalization.
- **Theorem 4.2**: the exact liminf and limsup of a_n/𝒜_n are
  e^{−5/6}Θ(1/2) ≈ 0.31986675953099572613 and
  e^{−5/6}Θ(0) ≈ 0.45051819401966197435; the cluster set is the whole
  interval between them. Proposition 4.3 and Corollary 4.4 give the limiting
  phase law.
- **Theorem 5.1**: oscillatory adjacent-ratio and Turán asymptotics; a_n is
  eventually strictly log-convex. Proposition 5.2: a_n is not P-recursive.
- **Section 6** (the array A357824): fixed powers and the broad Gaussian regime k → ∞,
  k = o(n) (Proposition 6.1), the critical theta regime k ≍ n (Theorem 6.2), a uniform
  two-endpoint theorem for **all** supercritical powers (Theorem 6.3), and a
  logistic transition near square-index ties at k ≍ n^{3/2} (Corollary 6.4).
- **Section 7** (multisets): an exact rising-factorial bridge gives every
  fixed exponential sector (Theorem 7.1); the first one is
  n! b_n/a_n = 1 + √(πe)/(4√2) n³ 2^{−n}(1 + O(1/n)) with an explicit
  phase-dependent 1/n term (Theorem 7.2).
- **Section 8**: parity-sensitive inverse expansions (Proposition 8.1,
  Theorem 8.2) and their relation to integer thresholds.

Kotesovec's OEIS observations of November 2022 (a_n^{1/n} ~ K_n, and no limit
of a_n/𝒜_n; the same for b_n) are the starting point and are credited as
such, not claimed.

**Part II** (a general lattice-peak transfer theorem; it answers question Q6
in a sufficient-hypothesis form). For a positive array C_{n,x} on a moving
lattice with peak phase δ_n, power r_n and q_n = r_n d_n²/σ_n², with
ϑ(q,δ) = Σ_j exp(−(q/2)(j−δ)²) (Part I's Θ_τ is ϑ(8τ,·); the Mahonian
report's Z_δ(q) is ϑ(q,δ)):

- **Theorem 15.1**: under a local quadratic law (H1), a uniform Gaussian
  majorant (H2) and interior completeness (H3), S_n(r_n)/Ω_n^{r_n} =
  ϑ(q_n,δ_n) + o(1) uniformly for q_n in a compact K, with an explicit
  three-term bound; Corollary 15.2: the cluster set is ϑ(q, set of phase
  limits).
- **Theorem 15.4 and Proposition 15.5** (added by the write): (H2) may be
  weakened to an exponential majorant (H2e), which log-concavity of the row
  supplies.
- **Theorem 17.2**: every fixed order, with coefficients given by a Bell
  recurrence (the theta-side tail of its proof completed by the write);
  Section 17.1 and Remark 17.4 reduce them to phase derivatives of ϑ.
- **Theorem 18.1**: the multidimensional version with a quadratic-form theta
  function; **Theorem 19.1**: a first-order inverse (existence and
  localisation completed by the write), and Corollary 19.2.
- **Instances** (added by the write): the ballot array satisfies (H1)–(H3)
  (Proposition 20.1), so Theorem 6.2's leading term is an instance; the
  Mahonian array satisfies (H1), (H2e), (H3) (Proposition 21.1), so the
  critical window of `a380274-mahonian-growing-powers` is one too. The
  manuscript itself only predicted the Mahonian case.

Corrections made under Vladimir's standing rule (4 October 2026):

- **Refuted** (Remark 17.4): the manuscript's identity
  Σ u³e^{−qu²/2} = q^{−1}∂_δ(−2∂_qϑ) drops the term 2q^{−2}∂_δϑ. At q = 2.7,
  δ = 0.31 the sum is 0.018988…, the printed formula 0.022256…; the
  corrected formula agrees to 40 digits.
- **Overstated** (Remark 20.2): Part I's all-orders coefficients are
  "precisely" the T_s only at first order with the printed dictionary
  (T_2 ≈ 0.108 against F_2 ≈ 1.090 at n = 400…6400); with q = 8 and
  Ω_n^n = e^{−5/6}𝒜_n they agree at every order.
- **Unstated normalization**: the cluster set (20.4) is that of Kotesovec's
  a_n/𝒜_n (the batch-98 dossier called it "(8.5)"; the manuscript's number
  is (8.4)).
- **Moved to further questions** (Section 25, F1–F7, besides the
  manuscript's R1–R12): Gaussian (H2) for the Mahonian rows; the regimes
  outside the critical window; constrained and boundary variants; the
  heuristics of Sections 23.3 and 24; the inverse theorem for A357825 across
  parities (Remark 20.3 applies it per parity branch); the case M′ = 0 of
  Definition 17.1; the all-orders hypotheses for the ballot rows.
  Item F8 (added 5 October 2026 by a batch-100 reciprocal note, not a claim
  of the manuscript): the fibre hypotheses (H1), (H2e) that would make
  Theorem 22.1 of `a022629-distinct-partition-norms` an instance of
  Theorem 15.1.

## What is not claimed

The manuscript's non-claims are all kept in the text (title-page box, the
table of Section 1.2, Sections 9 and 10, Appendix B):

- Bala's conjecture a_{2p−1} ≡ 1 (mod p³) for primes p ≥ 5, recorded in
  A357825, is **not resolved** (question Q9).
- Log-convexity is proved only eventually, not at every index (Q2).
- The expansion is a Poincaré expansion: no convergence, optimal truncation
  or resurgence is claimed. It is an oscillatory expansion with periodic
  coefficients, "not an ordinary real logarithmic-exponential transseries"
  (remark after Theorem 2.2).
- No unrestricted exact inverse rounding theorem, no effective thresholds
  for the O-terms.
- The numerical tables are high-precision experiments, not interval
  certificates.
- No publication priority: the literature and OEIS search was limited.
- No Lean or other formal proof.

Part II's non-claims are kept in its Sections 13, 24 and Appendix D: the
hypotheses are sufficient, not necessary; general discrete Laplace theory
(Helton–Hughes–Schlosser, a fine-lattice regime) is not superseded; no new
proof of Part I's theorem; degenerate, boundary and multiple peaks are out
of scope; the all-orders theorem is Poincaré only (no convergence, optimal
truncation, Borel summability or resurgence); nothing arithmetic, in
particular not Bala's congruence; nothing formalized; no worldwide novelty
or priority claim; the standard ingredients are not claimed as new methods.

The OEIS data and attributions quoted in the article (terms n ≤ 14 embedded in
`code/verify.py`, the dates of Kotesovec's and Bala's comments) are as the
manuscript inspected them on 1 October 2026; the intake did not re-fetch
them.

## Relation to neighbouring material

- **No repository host.** No other report treats A357824, A357825, A357871
  or A008315. (When this report was written they occurred nowhere else in
  the repository outside its catalogue entries; since then they are also
  named in cross-references only: the README of
  `a215561-fixed-composition-excursions` (batch 75, a terminology warning)
  and the Mahonian report below (batch 77).)
- **Same mechanism, different objects** (cross-references only; no statement
  depends on them):
  [`Theta_Resolved_Optimal_Truncation_q_Multinomial`](../../../../../../../Analysis/Transseries/docs/series-and-transseries/Theta_Resolved_Optimal_Truncation_q_Multinomial/)
  (a continuous-to-lattice saddle with a theta law for q-multinomial
  remainders) and the chapter "Galois numbers and root-lattice theta
  sectors" of
  [`Combinatorial_Transseries_Inverses`](../../../../../../../Analysis/Transseries/docs/series-and-transseries/Combinatorial_Transseries_Inverses/),
  both in the series-and-transseries collection.
- [`a380274-mahonian-growing-powers`](../a380274-mahonian-growing-powers/)
  (batch 77, manuscript 55) proves the same theta phenomenon for growing
  powers of Mahonian numbers (OEIS A380274, A380275), with only the two
  lattice shifts δ ∈ {0, 1/2} instead of a varying phase. It is an instance
  for one more triangular array, not the general lattice-peak theorem of
  question Q6, which stays open (dated note in Q6). *[Update, batch 98D,
  5 October 2026: Q6 is now answered in a sufficient-hypothesis form by
  Part II, and the Mahonian critical window is proved there to be an
  instance (Proposition 21.1, with the exponential majorant (H2e) that
  log-concavity supplies; it reorganizes that report's own proof). Dated
  note at the end of Q6.]* Its theta functions are normalized differently:
  Z_δ(q) there is Θ_{q/8}(δ) here, and both are Part II's ϑ(q,δ); its
  Θ_δ(q) is e^{qδ²/2}ϑ(q,δ).
- **Inversion and staircases** (Part II): Theorem 19.1 is the first-order,
  real, bounded-perturbation analogue of the M = 1 term of
  `p0:thm:perturbed-inversion` in
  `Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/transseries_and_inversion.tex`
  (analytic, small parameter; neither contains the other). For question
  R11 the only related formal statement is the generic Lean lemma
  `Fabius.staircase_separation`
  (`Analysis/FabiusFunction/Lean/FabiusFunction/StaircaseInversion.lean`),
  about an arbitrary real number, not these sums.
- **Later arrivals.** The 177-archive arrival `60f54ea06` (not batch 98)
  contains `ProveIt_Critical_Theta_Power_Weighted_Distinct_Partitions.zip`
  and `A215570_Balanced_Ballot_Asymptotics.zip`, possibly further theta or
  ballot instances; they were not examined for this write.
  *[Update, batch 100, 5 October 2026: the first of these is now Section 22
  of [`a022629-distinct-partition-norms`](../a022629-distinct-partition-norms/)
  (a theta multiplier for ∏(1 + k^α q^k) with α growing like
  (2n)^{1/6}/log n). It is the lattice-peak mechanism in Fourier-dual form
  but not an instance of Theorem 15.1 as proved: (H1) for its row
  l ↦ P(S = n, R_{≥2} = l) is a fibre local limit theorem that neither report
  proves, and (H2e) would need log-concavity in l (new item F8). Dated note
  at the end of Section 21.1 (the two-instance statement).]*
  *[Update, batch-101 reciprocal note, dated 7 October 2026: the second,
  `A215570_Balanced_Ballot_Asymptotics.zip` (bundle Report 86), has been
  examined and written (batch 101, placement `f7c612c72`) into Part VI of
  [`a215561-fixed-composition-excursions`](../a215561-fixed-composition-excursions/)
  as source 101-86, together with bundle Report 90 (source 101-90). It is
  **not** an instance of Part II's lattice-peak transfer theorem
  (Theorem 15.1, `tbs:lpt:thm:transfer`; Theorem 18.1): it has no power sum
  and no growing exponent (one coefficient, r_n ≡ 1). Its "lattice factor 4"
  counts the dominant points of a mark torus, i.e. the index of the
  sublattice that carries (length, #(±2), #(+2) − #(−2)), the classical
  periodicity factor of a lattice local limit theorem; read as a lattice sum
  it sits in the fine-lattice limit q ≍ 1/n → 0, where Proposition 16.1 gives
  the phase-independent √(2π/q) and Remark 18.2 says to parametrize the
  sublattice first. The factor also depends on the coordinates: source
  101-90's coordinates give 2h = ν(r − 1) dominant pairs (r − 1 mark points,
  each with ν time phases), those of that report's Section 6 give ν (one
  mark point), and for the zero-free walk with the steps −2, −1 marked there
  is one dominant point; only the count divided by the square root of the
  Gaussian determinant is the same in all of them (its Remark 36.4).
  Remark 38.1 there gives the argument; the same holds for source 101-90.
  README only; the article is unchanged.]*
- [`ballot-polynomial-hankel-determinants`](../../../hankel-determinants/catalan-and-ballot/ballot-polynomial-hankel-determinants/)
  studies Hankel determinants of ballot moments, not growing powers; there
  is no overlap.
- **Lean.** Placement in this collection confers no formal status. No Lean
  or Rocq declaration of the repository concerns these sums, and none of the
  statements of this report is formalized. Question Q10 sketches a staged
  formalization plan, and Part II's R12 one for the transfer theorem.

## Building

From a scratch copy of this directory, run

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The build needs `figures/phase_collapse.pdf` and `figures/oscillation.pdf`
beside `article.tex`. pdfLaTeX (MiKTeX 26.2) produced the shipped
`article.pdf`: 51 pages (50 before the batch-100 reciprocal note of
5 October 2026), with no errors, no warnings, no undefined
references or citations, no multiply defined labels, no duplicate
destinations, no overfull boxes, and one underfull line in the bibliography
(also present in a build of the delivered text). It contains no Type 3 font
(`pdffonts`: 17 Type 1, 6 CID TrueType). Copy back only `article.pdf`.

The shipped `code/build.sh` does not work from `code/`: it changes into its
own directory and then calls `code/verify.py`, and it expects `article.tex`
beside itself. In the delivered layout, with `build.sh` at the root, it ran
`code/verify.py --all` (which rewrites `data/` and `figures/`) and then
`pdflatex` three times, copying the result over `article.pdf`. Do not run it
in this directory.

## Rerunning the script

`code/verify.py` finds `data/` and `figures/` relative to its own parent
directory and **overwrites** them: run it on a copy, never in place.

```sh
R=SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a357825-theta-ballot-power-sums
W=$(mktemp -d)
cp -r "$R/code" "$R/data" "$R/figures" "$W/"
cd "$W"
uv run --no-project --with mpmath==1.3.0 --with sympy==1.14.0 --with matplotlib==3.10.8 python code/verify.py --all
```

Without flags the script runs only the exact and symbolic checks (and
rewrites `data/coefficients.json` and `data/verification_status.json`);
`--plots` adds the figures, `--all` also the numerical tables. The intake ran
`--all` on a copy (exit code 0, about two minutes): the eight data files it
writes equal the shipped ones, five CSV files byte for byte and the three
JSON files up to line endings (on Windows, `Path.write_text` writes CRLF; the
delivered JSON is LF). The figures it writes differ in bytes from the
shipped ones (Matplotlib metadata, and Type 3 fonts unless set as below).

Independently of the delivered code, the intake recomputed a_0..a_6 and
b_0..b_6 from the definitions, both envelope constants to 20 digits, and the
expansion through F_2 against exact sums at n = 100, 200, 400, 800 (relative
errors 1.2e−5, −6.4e−5, 7.9e−7, −1.4e−5 after F_2, consistent with
O(m^{−3/2})), and the first exponential sector at n = 100, 200, 400.

## Checking Part II

Part II ships no program, and none was added. Its rebuild needs only
`article.tex`; it was also rebuilt on a copy from the arrival commit (14
pages, no errors). The intake and the write checked it with mpmath 1.3.0 and
SymPy 1.14.0 at 40 digits, on scratch copies outside the repository:

- Section 17.1: the first two identities hold to 40 digits at q = 2.7,
  δ = 0.31; the third, as printed, gives 0.0222562 against the true
  0.0189884, and the corrected form, the recurrence (17.11) and the closed
  form of Σ_3 agree with the direct sum to 40 digits.
- The dictionary (12.1) at three (q, δ) points (18 digits), and
  e^{−5/6}ϑ(8,½), e^{−5/6}ϑ(8,0) against Part I's C_∓ (21 digits).
- The ballot dictionary on exact sums: S_{n,k}/Ω_n^k against ϑ(8τ, α_n) for
  τ = 0.5, 1, 2 at n = 400, 1600, 6400 (relative errors falling like 1/m,
  from 8.9e−3 to 4.0e−6); Remark 20.2's polynomials P_2, Q_2 by series
  expansion from Part I's A_1..A_4 (`data/coefficients.json`), and both
  order-2 truncations against exact a_n.
- The Mahonian rows (exact integers, n = 40, 41, 80, 82): log-concavity, the
  bound (15.5) with the constants of Proposition 15.5 (largest ratio 0.106),
  and the window errors η_n(3); and S_n(ρσ_n²)/C_n^r against
  Θ^mgp_δ(ρ) for ρ = 0.5, 1, 3 (relative errors about 1/n).

These are numerical checks of formulas and conventions, not of the
asymptotic statements, which rest on the proofs.

## Disclosures and discrepancies

- **Not shipped:** the delivered `README.md` (replaced by this guide), the
  delivered `article.pdf` (replaced by a build of this text) and the
  `SHA256SUMS` ledger. Of Part II, the article and its PDF (printed as
  Part II; they survive in `1ec443bc4`).
- **Part II edits.** Symbols colliding with Part I or the Mahonian report
  are renamed (Table 2 of the article): Θ(q,δ) → ϑ(q,δ), A_n → Ω_n,
  ε_n → t_n, Λ_n = a_n + d_nℤ → L_n = ξ_n + d_nℤ, m_n → ν_n, Q_n → **Q**_n,
  D → 𝒟, B, c → B_*, c_*, M_n(j), q, V_n (Mahonian) → I_n(j), z, σ_n²,
  among others; no normalization changed. Part II's bibliography entry for
  this report is dropped (it is this report); its A357825 and A357824
  entries are cited as Part I's, and its A380275 entry with the entry's
  name. Its two paraphrased OEIS titles are recorded, with the names fetched
  on 5 October 2026, in Appendix D (OEIS text CC BY-SA 4.0). Wang's preprint and the Helton–Hughes–Schlosser
  paper were not re-fetched.
- **Renamed paths:** `requirements.txt` → `data/requirements.txt`;
  `build.sh` → `code/build.sh`. Every other file keeps its delivered path.
  Section 9.4 of the article (a verbatim delivered passage, followed by a
  write note), `source_audit.md` and the delivered README name
  `requirements.txt` and `build.sh` at the root, and the article's
  "From the extracted archive" refers to the delivered layout.
- **Regenerated figures.** The delivered `phase_collapse.pdf` and
  `oscillation.pdf` embedded their DejaVu Sans and STIX fonts as Type 3. In
  the write both were regenerated from the shipped, unmodified
  `code/verify.py`, on a copy, by calling its `plots()` function only:
  - Matplotlib 3.10.8, the version that made the delivered files, with
    `rcParams['pdf.fonttype'] = 42` set before the script was loaded, mpmath
    1.3.0 and SymPy 1.14.0;
  - `SOURCE_DATE_EPOCH=1790886019`, the delivered files' creation date
    (1 October 2026, 20:20:19 UTC);
  - the run rewrote `data/plot_data.csv` byte-identical to the shipped file,
    so the plotted data are the delivered ones;
  - two runs gave byte-identical PDFs; page size (576 × 266.4 pt) and the
    rendered images match the delivered figures, apart from glyph
    anti-aliasing; the fonts are now CID TrueType;
  - the PNG previews are kept as delivered.

  To reproduce, on a copy as above, run
  `import runpy, matplotlib; matplotlib.rcParams['pdf.fonttype'] = 42; runpy.run_path('code/verify.py', run_name='m')['plots']()`
  with that environment variable, under the `uv run` line above.
- **"Inspected tree commit"** in `source_audit.md` is the commit
  `50f93367b`.
- **Delivered README wording.** Its "Verification actually performed" list
  ("First 15 terms of each target sequence against OEIS") rests on the
  values embedded in `code/verify.py`, which the intake did not compare with
  the live OEIS entries.
