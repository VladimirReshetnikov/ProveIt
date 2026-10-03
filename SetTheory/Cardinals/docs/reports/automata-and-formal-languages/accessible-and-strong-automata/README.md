# Accessible and Strongly Connected Deterministic Automata

**Every fixed order, inverses and automorphism sectors**

This is a research report dated 2 October 2026, built from two manuscripts
of batch 77. Author line of source 09: "Research article and reproducibility
supplement"; source 64 has an empty author line. Source 09's source notes
state that its article and computational supplement "were prepared with
OpenAI model assistance"; source 64 names no tool.

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 09 | batch 77, manuscript 09 | `accessible-automata-reproducibility.zip` (*All orders asymptotics for fixed alphabet accessible automata*, main file `accessible-automata.tex`, 16-page PDF) | none (no ProveIt commit named; a bounded read-only audit of the public repository, 2 October 2026) | `d0e6008d9` | Part I (Sections 1–12) and Appendix A; base of the merge |
| 64 | batch 77, manuscript 64 | `strong-automata-reproducibility.zip` (*Strongly connected automata: fixed order asymptotics, inverses, and exact automorphism sectors*, main file `strong-automata.tex` with the fragment `cyclic-lift-proof.tex`, 21-page PDF) | none (does not mention ProveIt) | `d0e6008d9` | Part II (Sections 13–24) and Appendix B |

Both archives arrived in commit `096ee7b87` and can be retrieved with
`git show 096ee7b87:docs/incoming/<archive>`. Every result, proof, table,
remark, limitation and further question of both manuscripts is printed.
Where source 64 repeats source 09 up to the change of normalization (the
suffix count and its three forms, the three-range kernel estimates, the
Fuss–Catalan mass and moments, the contraction), the statement is printed
once, in Part I, and Part II says exactly what changes in a `[merge]` note.
The report is AI-assisted and unrefereed. **Independent proof review and
formalization are pending; nothing here is formalized.**

```
article.tex                                the report (standalone LaTeX, internal bibliography)
article.pdf                                the compiled report, 38 pages (title, abstracts and [write]
                                           notes 1–3, contents 3–4, Part I 5–18, Part II 19–34,
                                           appendices 35–37, references 37–38)
README.md                                  this guide
09-accessible-SOURCES.md                   source 09's bibliography, attribution and literature limits, as delivered
09-accessible-VERIFICATION.md              source 09's verification scope and recorded results, as delivered
64-strong-SOURCES.md                       source 64's sources, OEIS conventions and nearby literature, as delivered
64-strong-REPLAY.md                        source 64's recorded fresh replay, as delivered
64-strong-independent_checks-README.md     source 64's guide to its independent checks, as delivered
code/09-accessible-generate_coefficients.py              finite two-boundary coefficient algorithm (Part I)
code/09-accessible-validate_generated_coefficients.py    exact-count residual and precision-stability tests
code/09-accessible-verify_numerical_precision_regressions.py  exact phases, k = 500 regression
code/09-accessible-verify_identities.py                  355 exact identity checks
code/09-accessible-derive_coefficients.py                symbolic c1, c2
code/09-accessible-check_expansion.py                    exact-count comparisons through n = 200
code/09-accessible-compare_independent.py                comparison of separate coefficient derivations
code/09-accessible-inversion_demo.py                     Lambert/Newton model inversion at exact counts
code/09-accessible-checks-verify_exact_counts.py         exact recurrence, exhaustive and large-n checks
code/09-accessible-checks-check_third_order.py           separate cumulant-based c3
code/09-accessible-verify_manifest.py                    checksum verifier (needs the unshipped manifest)
code/09-accessible-make_archive.py                       archive builder (delivery tool)
code/09-accessible-replay.sh                             source 09's full replay (delivered layout; see below)
code/09-accessible-build.sh                              source 09's PDF build (builds accessible-automata.tex)
data/09-accessible-coefficients_k2_order5.json           coefficients through order 5, k = 2, 60 digits
data/09-accessible-coefficients_k3_order5.json           the same, k = 3
data/09-accessible-coefficients_k4_order5.json           the same, k = 4
data/09-accessible-coefficients_k2_order5_90digits.json  the k = 2 replay at 90 digits
data/09-accessible-coefficients_k500_order1.json         k = 500, first order
data/09-accessible-coefficients_k500_order1_60digits.json  the same at 60 digits
data/09-accessible-coefficient_symbolics.txt             symbolic c1/c2 output
data/09-accessible-generator_validation.json             successive-order error validation
data/09-accessible-identity_verification.json            the 355 identity checks
data/09-accessible-independent_comparison.json           c0..c3, tau1, tau2 cross-comparison
data/09-accessible-inversion_demo.json                   model-inversion results
data/09-accessible-numerical_precision_regressions.json  518 phase tests and the k = 500 test
data/09-accessible-numerics.json                         exact-count diagnostics
data/09-accessible-checks-verification.json              exact-count check record (input of check_third_order.py)
data/09-accessible-checks-third_order.json               separate c3 record
data/09-accessible-requirements.txt                      mpmath==1.3.0, sympy==1.14.0
code/64-strong-generate_coefficients.py                  finite saddle, strict renewal and logarithmic transfer (Part II)
code/64-strong-verify_precision.py                       70/100-digit comparisons, exact phases, k = 500
code/64-strong-verify_exact_sectors.py                   strict checkpoints, exact recurrences, sectors, primes, k = 1
code/64-strong-verify_cyclic_lifts.py                    exhaustive connected-lift counts
code/64-strong-verify_inverses.py                        B/R/U smooth inverses
code/64-strong-verify_all_model_inverses.py              all four inverse models, including L
code/64-strong-independent_checks-derive_low_orders.py   separate low-order derivation
code/64-strong-independent_checks-check_small_models.py  exhaustive enumeration of small models
code/64-strong-independent_checks-verify_exact_counts.py exact integer recurrences through n = 600
code/64-strong-verify_replay.py                          replay comparator
code/64-strong-verify_manifest.py                        checksum verifier (needs the unshipped manifest)
code/64-strong-make_archive.py                           archive builder (delivery tool)
code/64-strong-replay.sh                                 source 64's full replay (delivered layout; see below)
code/64-strong-build.sh                                  source 64's PDF build (builds strong-automata.tex)
data/64-strong-coefficients_k2.json                      coefficients through degree 5, k = 2, 70 digits
data/64-strong-coefficients_k3.json                      the same, k = 3
data/64-strong-coefficients_k4.json                      the same, k = 4
data/64-strong-precision_validation.json                 precision record
data/64-strong-exact_sector_validation.json              exact-sector record
data/64-strong-cyclic_lift_validation.json               cyclic-lift record
data/64-strong-inverse_validation.json                   36 smooth-inverse evaluations
data/64-strong-all_model_inverse_validation.json         48 all-model inverse checks
data/64-strong-independent_checks-low_orders.json        separate low-order coefficients
data/64-strong-independent_checks-small_models.json      small-model enumeration
data/64-strong-independent_checks-exact_k2.json          exact n <= 600 ratio samples and residuals, k = 2
data/64-strong-independent_checks-exact_k3.json          the same, k = 3
data/64-strong-independent_checks-exact_k4.json          the same, k = 4
data/64-strong-requirements.txt                          mpmath, sympy (unpinned)
```

(`code/` holds 28 files and `data/` 30.) Every file except `article.tex`, `article.pdf` and this README is
byte-identical to the delivery.

## Labels and numbering

Every label in `article.tex` carries the prefix `asa:acc:` (Part I, source
09) or `asa:str:` (Part II and Appendix B, source 64): **147 labels**, of
which 65 are source 09's, 72 are source 64's (71 in its main file, 1 in the
cyclic-lift fragment), each unchanged after the prefix, and 10 were added
by the write (`asa:acc:sec:objects`, `asa:acc:sec:three-region`,
`asa:acc:sec:mass`, `asa:acc:sec:inverse`, `asa:acc:sec:further`,
`asa:acc:app:left`, `asa:str:sec:objects`, `asa:str:sec:attribution`,
`asa:str:sec:further`, `asa:str:app:cyclic`). Source 09's Section *n* is
Section *n* here (*n* = 1, …, 12), so its theorem numbers are unchanged;
source 64's Section *n* is Section *n* + 12 (*n* = 1, …, 12), so its Theorem
2.1 is Theorem 14.1 here. Equations are numbered within sections (source
09 numbered them consecutively). Source 09's appendix is Appendix A; source
64's `cyclic-lift-proof.tex`, which it inputs inside its Section 10, is
Appendix B, *Liskovets's unrooted formula (a proof of the existing
identity)*. Write-step text is marked `[write]`; merge pointers `[merge]`.

## Notation

Both Parts share `k`, `d = k − 1`, the saddle constants
`t = k(1 − e^{−t})`, `v = t/k`, `ρ = e^{−t}`, `c = 1 − kρ`, `q = ρv^d`,
`β = e^{−d}/q`, the suffix count `R_h(r)`, the weights `w_r`, the mass
`θ = (1 − c)/c` and the endpoint moments. Everything else is local to its
Part; the table in the opening `[write]` note lists every clash. The
important ones:

| Here | Source | Meaning; tempting false reading |
|---|---|---|
| `T_n` (Part I) | 09 `T_n` | `S(kn+1, n)`. Not Part II's diagonal; Lebensztayn's normalization is `nS(kn, n)`, and `S(kn+1,n)/(nS(kn,n)) → 1/v`. |
| `T°_n` (Part II) | 64 `T_n` | `S(kn, n)`. **Renamed** (no normalization change) so that the two Stirling diagonals cannot be confused. |
| `K(n,h)`, `W_j(r)` | both | Each Part's own renewal kernel and endpoint series: `W_1(r) = −r/2` in Part I, `+r/2` in Part II. |
| `c_j`; `p_j`, `b_j` | 09; 64 | Coefficients of `a_n/T_n`; of `P_n/T°_n`, `B_n/T°_n`. For `k ≥ 3`, `c_1 = kρv/(2c)` but `b_1 = −kρv/(2c)`: the opposite signs in the two tables are not a misprint. |
| `t_j`, `τ_j` | 09; 64 | Saddle coefficients of the two diagonals; `t_1 ≠ τ_1`. |
| `L_n` | both | `(n−1)! a_n` (accessible, root 1) in Part I; labelled strongly connected structures in Part II. |
| `B_n`, `B_m(x)`, `B_{2a}` | both | Strong symmetry-weighted count (II); Bernoulli polynomials (I); Bernoulli numbers (II). |
| `A`, `C`, `α_j`, `a`, `s`, `J` | both | Part-local (see the table in the article). |
| `t, q, d, r, h, T, H` in Appendix B | 64 fragment | Local letters of the cyclic-lift proof (orbit length, additive order, product of primes, number of non-tree arcs, spanning tree, subgroup), listed at its start. |

The first small-state correction is at order `k = d + 1` in Part I and at
order `d` in Part II (strict checkpoint `Y_{kh} ≥ h+1` against
`Y_{kh+1} ≥ h+1`), as source 64 itself notes.

## What the report claims

Theorem numbers are those of the built `article.pdf`. All statements fix
`k ≥ 2` and the expansion order.

### Part I (source 09): rooted accessible structures, OEIS A006689 (`k = 2`), A006690 (`k = 3`)

- **Theorem 1.1.** `a_n / S(kn+1, n) = Σ_{j≤J} c_j n^{−j} + O(n^{−J−1})`
  for every fixed `J`, with effectively computable `c_j`, `c_0 = c`,
  `c_1 = kρv/(2c)`; only `h` with `dh + 1 ≤ j` affect `c_j`; the small-state
  boundary first affects `c_k` (for `k = 2` it contributes `−cv²` to `c_2`).
- The exact first-failure identity `T_n = a_n + Σ a_h R_h(n−h)` (Section 2);
  the saddle expansion of `S(kn+1,n)` (Lemma 3.1); three region bounds
  (Proposition 4.1); the uniform-sum identity and the strict contraction
  `θ < 1` (Section 5); a finite coefficient algorithm (Section 6); the
  patched-trial remainder proof (Section 7); `c_1, c_2, c_3` with a table for
  `k = 2, 3, 4` (Section 8); the carrier `a_n = C_a β^n n^{dn+1/2}(…)`,
  a Lambert seed with two corrections, existential integer-threshold
  brackets (Theorem 9.1) and finite Newton inversion (Section 9); an
  association-free left-tail bound (Appendix A).

### Part II (source 64): strongly connected structures, OEIS A027834/A027835, A006691/A006692, A304312/A304313

- **Theorem 14.1.** Every fixed order for `P_n/S(kn,n)`, `B_n/S(kn,n)`,
  the saddle expansion of `S(kn,n)`, and `B_n = Cβ^n n^{dn−1/2}(…)`; the
  same expansion for `U_n` and, multiplied by `n` and `n!`, for `R_n` and
  `L_n`; `p_1`, `b_1` explicit, with a binary small-state term at first
  order.
- The positive strict checkpoint model `P'_n = P_n` and its renewal
  identity (Section 15); three ranges (Lemma 16.1); the finite Gaussian rule
  and coefficient recursion (Section 17); the remainder theorem (Section
  18); the transfer through the formal logarithm with the factorial
  convolution Lemma 19.1 (Section 19); `p_1..p_3`, `b_1..b_3` and a table
  (Section 20); smooth inverses for four models and existential threshold
  brackets (Proposition 21.1); exact cyclic automorphism sectors, fixed
  divisor expansions, the uniform divisor-tail Theorem 22.1, even and prime
  state counts, the one-letter check and marked-state corollaries (Section
  22); a self-contained proof of Liskovets's exact unrooted formula
  (Appendix B).

## What it does not claim

From the two manuscripts (articles and delivery READMEs), kept here:

- No uniformity in `k`; `k = 1` is excluded (Part II uses it only as a check
  of normalization). No convergence of the correction series, no Borel
  summability, optimal truncation or beyond-all-orders description of the
  identity count `B_n`; the growth of `c_j`, `p_j`, `b_j` in `j` is not
  controlled.
- The leading equivalents (Korshunov; Bassino–Nicaud; Lebensztayn), the
  auxiliary recurrence and logarithm (Liskovets, Robinson) and Liskovets's
  unrooted formula are classical; Appendix B is a proof of the existing
  identity, not a new formula. Publication priority of the higher-order
  refinement is **unresolved**: Korshunov's 1978 survey was not obtained in
  full text and his 1986 strong-automata paper was not exhaustively
  inspected; an absent OEIS formula does not establish novelty.
- Inverse brackets have existential constants and cutoffs; no unqualified
  ceiling rule. Numerical coefficients are high-precision evaluations, not
  interval certificates. Finite checks support the implementations, not the
  asymptotic remainders.
- Fixed-divisor expansions need `n/ℓ → ∞`; small automorphism sectors are
  resolved only with larger sectors kept exact; a finite algebraic truncation
  of `B_n` cannot resolve the `ℓ = 2` sector. No terminal-state subset is
  included in the main counts.
- **Inverse sections.** The smooth inverses of both Parts are instances of
  the transseries-and-inversion volume
  (`Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/`):
  the seeds are its factorial core `p0:prop:factorial-core` (the log-linear
  companion of `p0:thm:lambert-core`), the corrections its reversion
  (`p0:thm:core-reversion`, `p0:thm:lambert-centered`), and the
  two-ceiling rule the separation condition of `p0:thm:staircase`;
  `t2:thm:balanced-inverse` of *Combinatorial Transseries Inverses* is cited
  for gamma-quotient phases. No novelty is claimed there; the `[write]`
  notes at the ends of Sections 9 and 21 give the dictionary.
- No publication, repository change or OEIS submission is implied (source
  09).

## Relation to the repository

- **No formal status.** Placement in the collection confers none. No
  statement of this report is formalized in Lean or Rocq. The only related
  declarations are the generic staircase lemmas `Fabius.staircase_ceil` and
  `Fabius.staircase_separation` in
  `Analysis/FabiusFunction/Lean/FabiusFunction/StaircaseInversion.lean`,
  which concern an arbitrary monotone function and give no formal status to
  Theorem 9.1 or Proposition 21.1.
- **Neighbouring reports.** In this category, `dfao-reversal-coloring-obstruction`
  uses "accessible" for the reachability property of one automaton; it
  counts nothing. Minimal DFAs of finite languages (A331120 and its `k`-ary
  analogues), compared with relaxed trees, are in
  `generating-functions-and-asymptotics/oeis-sequence-asymptotics/a082161-airy-amplitudes`
  (with batch 77's archive 29, `larger-alphabet-automata-report.zip`,
  handed there from this cluster); those objects are not the transition
  structures counted here, and no theorem is shared.
- **Repository searches.** Source 09's own audit of the repository was
  bounded (its tree listing was truncated). The intake's untruncated content
  search (2 October 2026) for the eight OEIS numbers above and for
  accessible or strongly connected automata, Korshunov and Liskovets found
  only the DFAO report named above; so no earlier repository text treats
  these sequences, and no repository claim is affected.

## Build

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

pdfLaTeX, standard packages only. The committed PDF was built with MiKTeX
in a scratch directory: 38 pages, no errors, no undefined references or
citations, no multiply-defined labels or duplicate destinations, no
overfull or underfull boxes. The delivered `code/*-build.sh` scripts build
the delivered main files, not this article.

## Rerunning the suites

The delivered scripts assume the delivered layout (for example
`code/verify_identities.py` and `checks/` in source 09; root-level
`coefficients_k2.json` and `independent_checks/` in source 64), so run them
from a fresh extraction of the archives, never inside this directory:

```sh
S=<a scratch directory outside the repository>
git show 096ee7b87:docs/incoming/accessible-automata-reproducibility.zip > "$S/09.zip"
git show 096ee7b87:docs/incoming/strong-automata-reproducibility.zip > "$S/64.zip"
cd "$S" && unzip -q 09.zip -d x09 && unzip -q 64.zip -d x64
uv venv "$S/venv" && uv pip install --python "$S/venv" mpmath==1.3.0 sympy==1.14.0
(cd x09/accessible-automata && PYTHON="$S/venv/Scripts/python.exe" bash replay.sh)
(cd x64/strong-automata-report && PYTHON="$S/venv/Scripts/python.exe" bash replay.sh)
```

(`venv/bin/python` outside Windows.) The staged files are the same bytes
under the names in the listing above.

- Source 09's `replay.sh` **rewrites its reference outputs in place**
  (`data/*.json`, `checks/*.json`) in the extracted copy; compare them with
  the shipped `data/09-accessible-*` files afterwards. It takes several
  minutes (five to six on this machine, mostly the three coefficient runs).
- Source 64's `replay.sh` works in `.replay/work`, compares with the
  delivered data itself and does not overwrite it (about two and a half
  minutes here). Its individual scripts, run by hand, do replace their
  named JSON outputs.
- On Windows, Python writes CRLF line endings, so compare modulo `\r`.
- `verify_manifest.py` (both) needs `MANIFEST.sha256`, present in the
  extracted archives but not shipped here; `make_archive.py` and `build.sh`
  are delivery tools.

Intake replay (2 October 2026, on copies, pinned SymPy 1.14.0 and mpmath
1.3.0): source 09's thirteen steps all passed (run in pieces under a
three-minute cap); six regenerated outputs equal the delivered ones modulo
CRLF and thirty are byte-identical. Source 64's replay passed: "All 13 JSON
outputs match, ignoring only run time fields", exact `n ≤ 600` checks
included. No PDF was rebuilt with the delivered build scripts.

No delivered file was excluded as a heavy regenerable artifact (the
largest shipped data file is 12 KB), so there is nothing to reconstruct.

## Delivered files that use delivery names

These files are byte-identical to the delivery, so their text still uses the
delivered names; this table maps them.

| Delivered name | Shipped as |
|---|---|
| 09 `accessible-automata.tex` / `.pdf` | `article.tex` (merged and edited) / not shipped |
| 09 `README.md`, `MANIFEST.sha256` | not shipped (this README; manifest verified 35/35 at intake and retired) |
| 09 `SOURCES.md`, `VERIFICATION.md` | `09-accessible-SOURCES.md`, `09-accessible-VERIFICATION.md` |
| 09 `code/<name>.py`, `build.sh`, `replay.sh` | `code/09-accessible-<name>.py`, `code/09-accessible-build.sh`, `code/09-accessible-replay.sh` |
| 09 `checks/<name>.py` / `checks/<name>.json` | `code/09-accessible-checks-<name>.py` / `data/09-accessible-checks-<name>.json` |
| 09 `data/<name>`, `requirements.txt` | `data/09-accessible-<name>`, `data/09-accessible-requirements.txt` |
| 64 `strong-automata.tex`, `cyclic-lift-proof.tex` / `.pdf` | Part II and Appendix B of `article.tex` / not shipped |
| 64 `README.md`, `MANIFEST.sha256` | not shipped (manifest verified 35/35 at intake and retired) |
| 64 `REPLAY.md`, `SOURCES.md`, `independent_checks/README.md` | `64-strong-REPLAY.md`, `64-strong-SOURCES.md`, `64-strong-independent_checks-README.md` |
| 64 `<name>.py`, `build.sh`, `replay.sh` | `code/64-strong-<name>.py`, `code/64-strong-build.sh`, `code/64-strong-replay.sh` |
| 64 `<name>.json`, `requirements.txt` | `data/64-strong-<name>.json`, `data/64-strong-requirements.txt` |
| 64 `independent_checks/<name>.py` / `.json` | `code/64-strong-independent_checks-<name>.py` / `data/64-strong-independent_checks-<name>.json` |

Other discrepancies, disclosed rather than fixed:

- `09-accessible-VERIFICATION.md` records SHA-256 hashes of the delivered
  TeX source and PDF (neither is shipped as such; `article.tex` is the
  merged text) and of the coefficient generator (which matches
  `code/09-accessible-generate_coefficients.py`); it describes manifest
  checks and a 16-page byte-identical PDF rebuild of the delivery.
- `64-strong-REPLAY.md` describes the delivered 21-page PDF and manifest;
  `64-strong-SOURCES.md` says "Section 1 of the article derives the
  identification" (Section 13 here); `64-strong-independent_checks-README.md`
  gives commands with the delivered paths.
- `code/09-accessible-checks-check_third_order.py` reads
  `verification.json` next to itself (the shipped
  `data/09-accessible-checks-verification.json`); source 09's article and
  delivered README speak of "SHA-256 manifests" and a `README.md`; source
  64's article of "a checksum manifest". `[write]` notes in Sections 10 and
  23 say what is shipped.
- `data/64-strong-requirements.txt` is unpinned; the intake used the pins
  of `data/09-accessible-requirements.txt`.
- `data/09-accessible-coefficient_symbolics.txt` and
  `data/09-accessible-numerics.json` have no final newline, as delivered.
