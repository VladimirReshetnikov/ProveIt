# Noisy Parity on Finite and Infinite Cubes

**Exact coloring, inspection budgets, asymptotic laws, and measurable
choice: the exact optimum of a noisy two-input labeling game, its expected
inspection frontier, a spectral simulation of every measurable rule by random
parities, and where choice and measurability decide attainment on the
countable cube**

A research article dated 5 October 2026, built from one manuscript. Its title
page reads "Prepared for Vladimir Reshetnikov / AI-assisted mathematical
development and exposition", and its PDF author field "OpenAI ChatGPT; prepared
for Vladimir Reshetnikov" (authorship; no author line is added here). The
package carries no "prepared for private review" line, no e-mail address and
no personal data.

| Source | Batch | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | batch 114 (non-bundle arrival; no bundle report number) | `Noisy_Parity_Finite_and_Infinite_Cubes.zip` (474,728 bytes, SHA-256 `c58216c1976adb1f36f0cd7eacbd3bcfa4465ff09d618d8b6d4a7aa61e7f5b90`; wrapper directory `noisy_parity/`, 13 files, 639,515 bytes unpacked), arrival commit `2399df2bd` ("New research reports", 5 October 2026); main file `noisy_parity.tex` (2,298 lines, 97 labels, 32-page A4 PDF) | `b71545625` (`b71545625fedc631edc2ead542abbfba72eb6063`, "Write batch 98B: …", 5 October 2026; title page, Appendix B, bibliography entries `repocube` and `repobox`; an ancestor of the current tree) | `99053b5d1` (batch 114) | the whole report |

**Status:** AI-assisted, unrefereed, **not formalized**: no Lean or Rocq
declaration states any theorem of this report, and its place in the collection
confers no formal status. Every theorem has a written proof. The finite checks
were executed (by the package, by the intake dossier and again at the write);
the infinite and asymptotic theorems rest on the written proofs only.
**Historical priority is not established** (the source says so). Nothing in
the source was found to be wrong.

## Trust boundaries

- **Classical inputs, quoted.** Walsh expansion, spectral samples, noise
  operators and the influence identity (O'Donnell, *Analysis of Boolean
  Functions*); infinite parity functions and their choice behaviour
  (Geschke–Lubarsky–Rahn 2015; Serafin, arXiv:2311.07886); the measurable
  chromatic obstruction on the cube graph (Conley–Miller); the Hurwitz-zeta
  expansion (DLMF 25.11.43). The write read Geschke–Lubarsky–Rahn and Serafin
  and confirmed the two literature statements of Section 8 (below); it did not
  read the other three.
- **Proved in the article.** All results listed under "What it proves",
  including the parts the source calls classical (Propositions 8.1 and 8.2 are
  proved there too).
- **Computation.** `code/verify_parity.py` checks the finite theory
  exhaustively in dimensions 1–4 in exact rational arithmetic;
  `code/check_asymptotics.py` evaluates the Zipf expansions in 65-digit
  `Decimal` arithmetic (not interval certificates); `code/create_figures.py`
  checks the examples exactly and encloses the infinite product of Remark 8.7
  with rational partial products and a tail bound. No infinite statement rests
  on a computation; the plots illustrate proved formulas.

## What it proves

The game: `X` uniform on `{0,1}^I`, `I = [n]` or `N`; a challenge index `J`
with ordered weights `p_1 ≥ p_2 ≥ …` (all positive, summing to 1); i.i.d.
Bernoulli(`η`) noise `B`; `Y = X ⊕ e_J ⊕ B`. One measurable label `f` (with
one shared seed if randomized) scores `Win(f) = P(f(X) ≠ f(Y))` —
**disagreement** is success. Put `a = 1 − 2η`, `P_k = p_1 + … + p_k`,
`F_k = a^k(2P_k − 1)`, `w_k = (1 + F_k)/2`. Statement numbers are the
delivered ones (section counter).

- **Theorem 2.2** (`np:thm:main`), for `0 < η < 1/2`: the optimum is
  `max_k w_k = max_k [1 + (1−2η)^k (2P_k − 1)]/2`, attained by the prefix
  parity `χ_[K]` (`K` the smallest maximizing index), also on the countably
  infinite cube, where `K` is finite; the maximizing degrees are `K` alone or
  `K, K+1`. The exact expected-inspection frontier `G(c)` joins the points
  `(k, w_k)`, `k ≤ K`, and is constant from `K` on; a shared mixture of the two
  adjacent prefix parities attains every intermediate budget, and no exact
  adaptive shared-randomized procedure with expected cost at most `c` does
  better.
- **Section 3, the spectral simulation**: every XOR-noise response of a
  measurable Boolean rule is reproduced by the random parity `χ_S` with
  `P(S = T) = f̂(T)²` (Theorem 3.1), whose mean query cost is the total
  influence `Σ|S|f̂(S)²`, at most the expected cost of any exact adaptive tree
  computing `f` (Lemma 3.2, Corollary 3.3); equality of cost and influence
  holds exactly for signed parities (Proposition 3.4); the budget problem for
  an arbitrary perturbation law is a linear program (display (4)).
- **Proposition 4.1**: `F_k` is unimodal with at most one adjacent tie; the
  first sign change of `d_k = 2a p_{k+1} − (1−a)(2P_k − 1)` certifies the
  optimum. Example 4.2: `p_i = 2^−i`, `η = 1/10` gives `w = (0, 1/2, 33/50,
  173/250, 849/1250, …)`, optimum `173/250` at three bits; `G(5/2) = 169/250`.
  Proposition 5.1: the boundary rates `η = 0` and `η = 1/2`.
- **Section 6**: every optimum depends on finitely many coordinates (the
  optimal family `𝓜` is finite), and under strictly decreasing weights the
  optima are `±χ_[K]` (and `±χ_[K+1]` at a tie) (Theorem 6.1); a nonlinear
  optimum under tied weights, score `6029/10000` (Example 6.2); quantitative
  stability with a positive gap `γ` (Theorem 6.3).
- **Section 7**: at zero noise on `N` the measurable supremum is 1 and is not
  attained (Theorem 7.1); every near-perfect sequence tends weakly to 0 and has
  no Boolean limit in measure (Theorem 7.2); finite truncations converge with
  error at most `1 − P_n` (Proposition 7.3).
- **Section 8, choice and summable noise**: a total parity label exists under
  AC, and over ZF exactly under a restricted choice of `E_ev`-classes
  (Proposition 8.1, classical); no proper measurable or Baire-measurable
  countable colouring of the cube graph (Proposition 8.2, classical); a total
  parity label is measurable for a biased product measure `ν_q` iff
  `Σ min(q_i, 1−q_i) < ∞` (Proposition 8.3), so homogeneous noise excludes
  total parity labels even from the class of labels with measurable success
  events (Corollary 8.4); for summable heterogeneous noise the optimization over
  **all** subsets of `N` is compact, its value is the measurable supremum,
  measurable attainment holds iff some finite subset maximizes, and in ZFC a
  label with a measurable success event attains it (Theorem 8.5); full infinite
  parity is optimal iff `η_i ≤ p_i` for every `i` (Theorem 8.6); Remark 8.7:
  `η_i = p_i²/2` has no measurable optimizer, value
  `(1 + Π(1 − 4^−i))/2 ≈ 0.84426876856017` for `p_i = 2^−i`.
- **Section 9, small-noise laws**: uniform weights (Proposition 9.1) and the
  saturation transition at `ηn = 1`, with one-sided second derivatives `4e^−2`
  and `5e^−2` (Theorem 9.2); geometric weights, degree `⌊x_η⌋` and a
  logarithmically periodic second term `Φ_r` (Theorem 9.3); regularly varying
  weights, `L(η) ~ α/(α−1) · η k_η` (Theorem 9.4) and the degree-regret
  profile (Proposition 9.5); exact Zipf weights, an implicit envelope and the
  second-order laws, `2√(Cη) − (3C + 1/2)η` at `α = 2` (Theorem 9.6,
  Corollary 9.7), and a Bernoulli-`B_2` lattice term (Theorem 9.8).
- **Section 10**: the compact optimization for any almost surely finite
  random perturbation (Theorem 10.1), and one total parity function serves
  every law (Corollary 10.2).
- Sections 11–13 and Appendices A–B: the exact computations, a proposed
  formalization path, twelve research directions, a claim ledger and the
  package audit.

Added by the write (5 October 2026), with proofs, marked `[write]`:

- **Remark 5.2 (`np:rem:deterministic`)**: under strictly decreasing weights
  and a non-integer budget `0 < c < K`, no *deterministic* exact procedure with
  `E Q ≤ c` attains `G(c)` (equality in the chain simulation–Jensen–influence
  would force Fourier support `{[m], [m+1]}`, impossible for a Boolean
  function); on a finite cube the deterministic optimum is therefore strictly
  below `G(c)`. This sharpens the source's refusal to identify the two
  optimizations; the rest is Question 13.
- **Remark 6.4 (`np:rem:gap-shrinks`)**: on the countable cube the stability
  gap satisfies `0 < γ(η) < 2p_{K_η}` and tends to 0 as `η ↓ 0` (the set
  `[K−1] ∪ {j}` with `p_j < p_K`, and `K_η → ∞`). This proves the source's
  "it can shrink as η ↓ 0".
- Section 1.4 (provenance, the repository claims checked, second routes,
  see-also, the external sources as read, a reading-conventions table, the
  collected non-claims); a status note before the contents; notes at
  Sections 1.2, 3.2, 11, 12 and Appendix B; Section 13.1; two bibliography
  entries.

## What is not claimed

From the source, kept in the article (collected at the end of Section 1.4):
the machinery is classical (O'Donnell; Geschke–Lubarsky–Rahn, Serafin;
Conley–Miller); the puzzle is designed, priority is not established, it is not
a named open problem, not refereed, not a Lean/Rocq formalization, and implies
no endorsement or involvement of Elliot Glazer; the spectral simulation does
not compute `f` and does not preserve correlations of three or more inputs;
the expected-budget optimum is not identified with the deterministic-tree
average-cost optimum; the restricted parity principle is not equated with AC
or choice for arbitrary pairs, ultrafilter and `E_0`-transversal constructions
are sufficient, not necessary, and no new choice equivalence is inferred; the
stability gap may shrink as `η → 0`; there is no countably infinite uniform
model; the Zipf formula does not resolve terms below its remainder; the
`Decimal` checks are not interval certificates and the plots are not evidence;
the formalization table proposes modules; the requested LinkedIn page gave no
usable content (Glazer's interests are taken from his Epoch AI biography); no
repository change or outside communication was part of the deliverable.

## Further questions

Section 13 of the article lists the source's twelve proposals Q1–Q12
(`np:q:biased`, `np:q:multi`, `np:q:ties`, `np:q:costs`, `np:q:correlated`,
`np:q:nonsummable`, `np:q:tauberian`, `np:q:secondorder`, `np:q:joint`,
`np:q:effective`, `np:q:choice`, `np:q:certificates`): biased configurations
and adaptivity; three or more inputs; Boolean functions in tied eigenspaces;
coordinate costs; algorithms for correlated perturbations; nonsummable
heterogeneous noise; a Tauberian converse; second-order tail perturbations;
joint truncation and small-noise limits; effective values versus optimizers;
the ZF+DC strength of almost-sure optimality (the converse of Corollary 10.2);
certificates and formalization. Section 13.1 ("Further questions and
research", `np:sec:further`, Vladimir's standing rule of 4 October 2026)
records for each what the report proves toward it and what is missing, and
adds three:

13. **Deterministic trees under an average cost constraint**
    (`np:q:dettrees`; from the paragraph after the proof of Theorem 2.2):
    Remark 5.2 rules out attainment of `G(c)`; the deterministic optimum
    itself, the tied case and the countable supremum are open.
14. **Stability uniformly in small noise** (`np:q:smallnoise`): `γ(η) → 0`
    (Remark 6.4); a quantitative statement on the natural scale is missing
    (Proposition 9.5's paragraph gives one form for power-law weights).
15. **External inputs and priority** (`np:q:external`).

No claim of the source was found to be wrong, and no research question of
another report is answered.

## Checks made at intake

- Placement (batch-114 dossier `dossier114_PUZ`, 5 October 2026): the
  manuscript read in full; checked by hand the eigenvalue `(1−2p(S))a^|S|`,
  the `d_k` recursion and cutoff, the example values and `G(5/2)`, the
  Boolean-ness of Example 6.2, the deletion and inclusion identities of
  Theorem 8.6, the derivatives of Theorem 9.2, the `α = 2` Zipf coefficient,
  the regular-variation inversion, the summable-noise upper bound for
  nonmeasurable labels and the Fubini argument of Corollary 8.4. Independent
  spot checks (all PASS): uniform-weight degree, value and tie rule against
  brute force (`n ≤ 24`, 59 rational `η`); geometric degree `⌊x_η⌋`; the
  table rows `23/40` and `929079903231/10^12` (degree 6); the deletion
  identity; `Π(1 − 4^−i) = 0.6885375371203397…`; `A''(1±)`.
- Suites on copies (dossier, and again at the write; Python 3.14.4):
  `verify_parity.py` passes for all 65,812 truth tables × 8 parameter cases
  (526,496 pairs) in about 2–3 s, and its JSON equals
  `data/verification.json` except `python_version` (3.12.14 in the delivery)
  and `elapsed_seconds`; `check_asymptotics.py` prints
  `data/asymptotics_check.txt` exactly; `create_figures.py` (NumPy and
  Matplotlib via `uv`) prints "Exact examples and nonlinear optimizer: PASS"
  and the enclosure `0.84426876856016985772825717864675` …
  `0.84426876856016985772825727357091`, and writes a JSON file equal to
  `data/examples.json` (as JSON; bytes differ in newlines on Windows) and three
  figure PDFs that differ in bytes from the shipped ones (another Matplotlib
  version). The shipped figures embed TrueType fonts only (no Type 3).
- At the write: all 12 staged files byte-identical to the archive of
  `2399df2bd`; the two literature statements of Section 8 checked against
  Geschke–Lubarsky–Rahn (manuscript of 13 March 2015: Lemma 5, Corollary 9(b),
  Question 12) and Serafin (arXiv v2: Theorem 1, "Assuming the consistency of
  the existence of an inaccessible cardinal", with "model of set theory"
  meaning ZF + DC in his Section 2, presented as the answer to that question).

## Relation to the repository

**Formal status.** Nothing of this report is formalized, and it shares no
declaration with any formal file. The source cites
`Analysis/FabiusFunction/Lean/FabiusFunction/ThueMorseBooleanCube.lean`
(97 lines, namespace `Fabius`, blob `3527bee8` at the pin and now); its
description is correct. That module proves four finite algebraic identities:
`prod_one_add_eq_sum_powerset`, `prod_one_add_mul_pow`
(`∏_{j<m}(1 + u z^{2^j}) = Σ_{n<2^m} u^{w(n)} z^n` over any commutative
semiring), `prod_one_sub_pow_eq_sum_thueMorseSign` (the signed finite
Thue–Morse product over any commutative ring) and
`sum_pow_binaryWeight_eq_one_add_pow` (`Σ_{n<2^m} u^{w(n)} = (1+u)^m`), with
`thueMorseSign n = (−1)^{binaryWeight n}` (`FabiusFunction/Arithmetic.lean`).
Over ℚ or ℝ the last one, at `u = −η/(1−η)` and multiplied by `(1−η)^k`, is
`E χ_S(B) = (1−2η)^|S|`, the noise factor of the report's eigenvalue
(display (5)): an observation of the write, not used by the source. The
neighbouring `ThueMorseWalsh.lean` (353 lines, blob `63a333d6`, unchanged
since before the pin; not cited by the source) proves the vanishing of
nontrivial Walsh character sums on the dyadic block
(`sum_neg_one_pow_binaryWeight_land`), a masked character sum
(`sum_pow_binaryWeight_mul_pow_binaryWeight_land`) and the one-point Walsh
spectrum of the full parity (`sum_thueMorseSign_mul_walsh`). These are
ingredients of the first layer of the source's proposed formalization plan
(Section 12); no Lean or Rocq file proves Walsh inversion or Parseval for
arbitrary functions on a binary cube, or treats influences, decision trees or
noise channels (the Walsh-basis lemma under
`Combinatorics/Ramsey/Lean/GowersSzemeredi/` is Gowers' Lemma 15.1 over
`ℤ/N`, unrelated). The source's statement that its modules are "proposed
proof modules, not files already present" therefore still holds.

**Neighbouring reports** (paths under `SetTheory/Cardinals/docs/reports/`):

- `ordinals-and-order-types/measurable-box-games` (cited by the source as
  context; its README blob `04ce7e69` is unchanged since the pin and calls the
  report "AI-assisted, unrefereed, not formalized", as the source says). Two
  standard lemmas re-proved here are in its **Part IV**, credited there as
  classical: Lemma 3.2 here (total influence at most the expected number of
  inspections, and its per-coordinate form used in Proposition 3.4) is the
  second display of its Lemma 64.1, `mbg:insp:var-covariance` (source 04 of
  that Part); the depth-`d` degree bound after Corollary 3.3 is its Lemma 49.1,
  `mbg:qry:lem:degree` (source 06). Both are printed here as **second
  routes** with notes at both places. Conventions differ (`±1` hats and
  `χ_A = Π x_j` there; bits and `χ_S = (−1)^{Σ x_i}` here); for `±1`-valued
  `g`, its `E(∂_j g)²` is the flip influence used here. The write found there
  no counterpart of the spectral simulation or of the other results here.
- `ordinals-and-order-types/robust-neutral-choice` (**see also**; batch 114,
  same placement commit, independent source): overlaps only in side
  sections — choice-built labels invariant under finite changes on `2^N`, their
  non-measurability and failure of the Baire property, and a biased-product
  threshold there (`Σ(p_i − 1/2)² = ∞` for its neutral rules) beside
  Proposition 8.3 here (`Σ min(q_i, 1−q_i) < ∞` for total parity labels).
  Different symmetries; neither is an instance of the other; neither source
  cites the other. Its `η` is an unrelated tolerance.

**Stale claims.** None. The source's three repository statements (the Lean
module's content, the box-games report's subject and status, the
formalization modules being proposals) are correct at the current tree; the
write adds the neighbouring Walsh module the source did not cite.

## Notation

A table in Section 1.4 fixes the letters the source reuses, with tempting
false readings: `a`, `a_i`, `a(S)`; `A`, `B` (a constant, Fourier
coefficients, an independent set, the events `A_n`, `B_n`, the Bernoulli
polynomial `B_2`); `b_k` versus the modal sequence `b`; `C` (Zipf constant,
tree cost, cylinder, `E_0`-class); `D`, `d_k`, `d`; `ε` (stability deficit,
Zipf scale) and `ϵ(f)`; `α`; `F_k = F([k])`; `G`, `G_0`; `h`; `K` (the
*smallest* maximizing degree) versus `k_η`; `L` versus the label classes
`𝓛_μ ⊆ 𝓛_evt` and smooth losses; `M`, `𝓜`; `q`; `R` (seed, Zipf scale,
noise tail); `s`; `T`, `t_k`; `u`; the many `V`s; `η`; `Inf_i`. "Success"
means disagreement. No symbol was renamed.

## Labels

Every label carries the prefix `np:`, as delivered (none existed in the
repository; the source also uses sub-prefixes `np:found:` and `np:asym:`).
The source has 97 labels; the write added 19: `np:sec:provenance`,
`np:rem:deterministic`, `np:rem:gap-shrinks`, `np:sec:further`, the labels
`np:q:biased` … `np:q:certificates` on the source's Q1–Q12 (with a
`ref=Q\arabic*` key on their list, output unchanged), and `np:q:dettrees`,
`np:q:smallnoise`, `np:q:external`. The report has 116 labels. Builds of the
delivered text and of this one give all 97 delivered labels the same numbers
(aux files compared): the two added remarks are the last numbered statements
of their sections, and the added subsections come last in theirs.

## Files

```text
README.md                          this guide (replaces the delivered README.txt)
article.tex                        the report (delivered noisy_parity.tex; [write] additions)
article.pdf                        compiled report, 39 pages
code/build.sh                      delivered build script (delivered at the package root; fails from code/, see below)
code/verify_parity.py              exhaustive exact finite verification, dimensions 1-4
code/check_asymptotics.py          65-digit Decimal diagnostics of the Zipf expansions
code/create_figures.py             figures and exact example checks (needs NumPy, Matplotlib)
data/verification.json             recorded output of verify_parity.py
data/asymptotics_check.txt         recorded output of check_asymptotics.py
data/examples.json                 recorded examples and the rational product enclosure
figures/inspection_frontier.pdf    Figure 1 (included by the article)
figures/uniform_transition.pdf     Figure 2
figures/geometric_correction.pdf   Figure 3
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to the delivery (checked again at the write).

**Not shipped**, recoverable from the arrival commit (next section): the
delivered PDF `noisy_parity.pdf` (366,411 bytes, 32 pages) and the delivered
`README.txt` (6,130 bytes; staged at placement as `README.md` and replaced by
this guide; summarized under "From the delivery README"). The package has no
checksum manifest.

**Delivered text that names the delivery layout.** Appendix B of the
article and the delivered README name `noisy_parity.tex`, `noisy_parity.pdf`,
`README.txt` and `build.sh` at the package root, and give commands to run
from the package directory (a dated note in Appendix B says so).
`code/build.sh` changes to its own directory and runs `latexmk` on
`noisy_parity.tex`, so **it fails from `code/`**. `code/create_figures.py`
writes `figures/*.pdf` and `data/examples.json` two levels above itself
(`ROOT = parents[1]`), so **run in place it would overwrite shipped files**.
`code/verify_parity.py` writes `verification.json` in the working directory
unless `--output` is given. Use the routes below.

## Retrieving the delivered package

```sh
T=$(mktemp -d)
git -C /path/to/ProveIt show 2399df2bd:docs/incoming/Noisy_Parity_Finite_and_Infinite_Cubes.zip > "$T/np.zip"
sha256sum "$T/np.zip"   # c58216c1976adb1f36f0cd7eacbd3bcfa4465ff09d618d8b6d4a7aa61e7f5b90, 474,728 bytes
cd "$T" && unzip -q np.zip     # creates noisy_parity/
```

## Rerun the checks (on a scratch copy)

Python 3.10 or later. `verify_parity.py` and `check_asymptotics.py` use the
standard library only; `create_figures.py` also needs NumPy and Matplotlib.
Never run the programs inside the repository.

**Route A, delivered layout**: in the extraction above,

```sh
cd "$T/noisy_parity"
python3 code/verify_parity.py --output verification_rerun.json
python3 code/check_asymptotics.py > asymptotics_rerun.txt
diff asymptotics_rerun.txt data/asymptotics_check.txt
python3 code/create_figures.py      # rewrites figures/ and data/examples.json of the extraction
bash build.sh                       # latexmk on noisy_parity.tex
```

**Route B, from the shipped files** (tested at the write):

```sh
R=/path/to/ProveIt/SetTheory/Cardinals/docs/reports/ordinals-and-order-types/noisy-parity-cubes
T=$(mktemp -d); cp -r "$R/code" "$R/data" "$R/figures" "$T/"; cd "$T"
python3 -I -B code/verify_parity.py --output "$T/verification_rerun.json"   # about 3 s
python3 -I -B code/check_asymptotics.py | diff - "$R/data/asymptotics_check.txt"
uv run --no-project --with numpy --with matplotlib python -I -B code/create_figures.py   # writes into "$T" only
```

Compare `verification_rerun.json` with `$R/data/verification.json` as JSON,
ignoring `python_version` and `elapsed_seconds` (the only fields that differ),
and `$T/data/examples.json` with the shipped file as JSON. Regenerated figure
PDFs differ in bytes with another Matplotlib version; the article uses the
shipped ones. On Windows use `py` for `python3`; text output then has CRLF
line ends (compare ignoring them).

## Build the PDF

pdfLaTeX (mathpazo, amsmath, amssymb, amsthm, mathtools, geometry,
microtype, booktabs, longtable, array, enumitem, graphicx, xcolor, fancyhdr,
xurl, needspace, placeins, hyperref); the bibliography is embedded and the
three figures are read from `figures/`.

```sh
B=$(mktemp -d); cp article.tex "$B/"; cp -r figures "$B/"; cd "$B"
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built this way with MiKTeX on 5 October 2026: 39 pages;
no errors or warnings, no undefined references or citations, no multiply
defined labels, no duplicate PDF destinations, no overfull or underfull boxes.
The delivered source built the same way gives 32 pages, equally clean.

## From the delivery README

The delivery `README.txt` (replaced by this guide) gave the problem and main
results in the terms used above; said that the article "is an AI-assisted
mathematical development with full written proofs and independent internal
audits", that its foundations "are classical and cited", that "Historical
priority for the designed problem and its extensions has NOT been
established", and that it is "not a refereed publication, a certified solution
of a named open problem, or a Lean/Rocq formalization", without endorsement by
Elliot Glazer; recorded the pin and that no repository changes were made;
listed the 13 delivered files; gave the build commands (`bash build.sh` or
`latexmk` on `noisy_parity.tex`, from the package directory) and the package
list; and described the three programs as above (526,496 rule/parameter
pairs; a fixed grid `α ∈ {1.3, 1.5, 2, 2.5, 3, 5}`, `η ∈ {10^−5, 10^−8,
10^−11}`; intervals "rounded outward"; plots "not independent numerical
evidence").

## Rights

Repository contents are MIT-0. The package contains no OEIS data and quotes no
OEIS sequence; nothing was submitted anywhere.

## Provenance

- Sources cited by the manuscript: O'Donnell, *Analysis of Boolean
  Functions* (2014; arXiv:2105.10386); O'Donnell–Saks–Schramm–Servedio (FOCS
  2005); Geschke–Lubarsky–Rahn, *Choice and the Hat Game* (manuscript,
  13 March 2015); Serafin, arXiv:2311.07886v2; Conley–Miller (manuscript,
  2011); Glazer, arXiv:2211.10474; the Epoch AI article with Glazer's
  biography; DLMF §25.11; the ProveIt files above at the pin. Added by the
  write: the box-games article (Part IV) and `ThueMorseWalsh.lean`.
- Batch 114 of `docs/incoming` (non-bundle arrivals); arrival `2399df2bd`,
  placement `99053b5d1`, written 5 October 2026. Single source, so no merge
  choices. The delivered `noisy_parity.tex` is shipped as `article.tex`, the
  delivered programs, data and figures as listed above.
