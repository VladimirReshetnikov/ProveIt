# Integration into the ProveIt polylogarithm manuscript

This note accompanies **Polylogarithms: Global Euler Extremizers, Polynomial Zero Thresholds, and Mixed Gaussian Identities**. It describes reviewable integration changes. No manuscript, incoming archive, or repository file was modified during this delivery.

## 1. Immutable source and scope

The inspected repository is [VladimirReshetnikov/ProveIt](https://github.com/VladimirReshetnikov/ProveIt), at commit:

`4c173c06cc32c9cea554b39be1837ad2ae897fc1`

The canonical entry point is `Analysis/Polylogarithms/docs/manuscript/polylogarithms.tex`. The incoming directory is `docs/incoming`.

`provenance/source_snapshot.json` records the actual Git commit and tree, SHA-256 hashes of all six incoming ZIP files, hashes and Git blob identities for 22 relevant canonical/directory files, and hashes of 29 selected archive members. The materialized source matched the pinned Git blobs and its working tree was clean at capture. These hashes establish source identity; they do not certify the mathematics.

The research screened the canonical and incoming text for the relevant dependencies, conjectures, status changes, and duplicate work. It does not claim a line-by-line certification of every manuscript page, inventory entry, or archived implementation. Claims of advancement are relative to this snapshot and the inspected incoming files, not an exhaustive assertion of priority over the literature.

### Exact incoming archive map

The similarly named archives are different sources. Preserve their exact filenames and root directories when recording provenance.

| Filename in `docs/incoming` | Top-level directory in the ZIP | Article bibliography key | Relevant role |
|---|---|---|---|
| `ProveIt_Sharp_Universal_Euler_2026-10-10.zip` | `ProveIt_Sharp_Universal_Euler` | `IncomingSharp` | Kernel-maxima conjectures; negative-order moment identities |
| `ProveIt_Polylogarithms_Research_2026-10-10.zip` | `polylogarithms_uniform_bounds_20261010` | `IncomingBounds` | Optimal averaged constant, axis lower asymptotic, `conj:euler-rate` |
| `proveit_polylogarithms_research_2026-10-10 (1).zip` | `polylogarithms_uniform_continuation` | `IncomingUniform` | Effective Lerch theorem, polynomial mesh question, prior S10/S12 candidates |
| `proveit-polylogarithms-research-2026-10-10.zip` | `proveit-polylogarithms-research-2026-10-10` | `IncomingMixed` | Overlapping Euler, golden-ladder, Cayley and radial material |
| `ProveIt_Polylogarithms_Radial_Bifurcation_2026-10-10.zip` | `ProveIt_Radial_Bifurcation` | `IncomingRadial` | Existing radial continuation retained |
| `ProveIt_AllDepth_Oscillation.zip` | `ProveIt_AllDepth_Oscillation` | `IncomingDepth` | Existing all-depth continuation retained |

The SHA-256 hashes, byte sizes, and selected member hashes are supplied in the JSON provenance rather than inferred from these names.

## 2. Exact status changes

| Earlier location and label | Current result | Integration action and remaining scope |
|---|---|---|
| `IncomingSharp/sections/08-questions.tex`, `conj:limit` | `ker:thm:limit` | Mark the global kernel-limit conjecture proved; retain the earlier compact scaling lemma as a prerequisite or historical statement. |
| Same source, `conj:maxima` | `ker:thm:N2` and `ker:thm:analytic` | Record uniqueness at N=2 and eventual uniqueness, decrease, and a convergent expansion. Keep the assertion for every finite N open. |
| `IncomingBounds/sections/research.tex`, `conj:euler-rate` | `ord:thm:leading`, with `ord:thm:axis-reduction` | Mark the matching global asymptotic proved. Include axis reduction before the rate argument: the previous axis lower bound alone did not establish global optimality. |
| `IncomingBounds/sections/euler.tex`, late-order discussion | `ord:thm:second`, `ord:prop:order-profile`, `ord:cor:near-maximizers` | Add the threshold correction and exact excess-scale localization criterion. These strengthen the earlier leading candidate. |
| `IncomingUniform/sections/04_lerch.tex`, `efflerch:prop:mesh`; polynomial question in `sections/08_research_agenda.tex` | `mesh:thm:polynomial` | Record the bound `mesh(Q_n) >= 1/(10 n^2)` for n>=2. Retain the earlier exponential bound, which may still be stronger at a small degree. |
| `IncomingUniform/sections/04_lerch.tex`, `efflerch:thm:explicit`, `efflerch:cor:growing` | `mesh:thm:saturation`, `mesh:thm:transfer`, `mesh:cor:growing` | Add the polynomial sufficient threshold and stronger growing-index range. Do not claim an optimal saturation threshold or uniform constant offsets. |
| `IncomingSharp/sections/06-identities.tex`, `cor:negativeorder` and the negative-order question in Section 8 | `neg:thm:transitions` | Retain negativity for every real outer order at least -1. Add the unique simple b-transition separately at outer orders -2 and -3. The general lower-order classification remains open. |
| Canonical `chapters/04-depth.tex`, `egen:prop:euler-full-generator` | `mix:thm:shift`, `mix:thm:rational`, `mix:thm:integer`, `mix:cor:resummation` | Add exact sampling, parameter jets, finite parts, and cross-weight identities. Do not describe these as proofs of individual unresolved fixed-weight reductions. |
| Incoming S10/S12 coefficient vectors | `mix:conj:S14`, `mix:prop:proximity` | Append the frozen weight-fifteen candidate. The exact rational result is a residual enclosure; equality remains conjectural. |

### Status that must be preserved

- S2 and S4 are already proved. In `chapters/04-S4-proof.tex`, the labels `s4proof:thm:s4`, `gaussian:thm:S4`, and the compatibility alias `gaussian:conj:S4` belong to the same proved result. The old label name does not make S4 an open conjecture.
- `cycloquot:conj:S6` in `chapters/04-cyclotomic-quotients.tex` and `s8new:conj:S8` in `chapters/04-S8-candidate.tex` remain conjectural.
- The S10 and S12 vectors in `polylogarithms_uniform_continuation/sections/05_shuffle_and_identities.tex` remain conjectural.
- The new S14 vector has total weight fifteen. Its normalized residual satisfies the exact inequality `|R_14| < 10^(-775)`, and the delivered interval contains zero. No equality theorem follows from that interval.
- The all-index sharp universal constant C_* is an existing theorem. Its value and attaining first-truncation boundary are separate from both sequences M_N and C_N studied here.
- No theorem-level error was established in the inherited inputs used here. Most proposed edits are status updates and scope qualifications, not retractions.

`integration/proposed_status_updates.tex` is a concise TeX insertion for review once the proof sections and their labels have been integrated. It is not a patch and does not apply itself to the repository.

## 3. Suggested chapter placement

The following filenames are suggestions for the integrator, not files already written into the manuscript.

| Delivered proof section | Suggested manuscript placement | Dependencies to keep visible |
|---|---|---|
| `sections/02_kernel_extrema.tex` | Chapter 5, after `05-universal-euler.tex`; for example `05-kernel-extrema.tex` | Residual kernel, positive two-measure identity, distinction between M_N and averaged errors |
| `sections/03_order_extrema.tex` | Immediately after the new kernel section; for example `05-optimal-euler-orders.tex` | `rw:thm:euler` on a>=1; gamma moment conventions; kernel definitions from the preceding section |
| `sections/04_lerch_zeros.tex` | Chapter 9, after the Appell/Laplace and effective zero framework; for example `09-polynomial-zero-thresholds.tex` | Definition of Q_n, real-rootedness framework, positive-transform zero bound |
| `sections/05_negative_orders.tex` | Chapter 5, following the continuation and order-extrema material; for example `05-negative-order-transitions.tex` | Principal continuation of F_(a,b), operator D=z d/dz, `ker:eq:continuation` |
| `sections/06_mixed_gaussian.tex` | Chapter 4, near the full-generator and S4/S6/S8 discussion; for example `04-mixed-generator-and-S14.tex` | Decreasing-index polylogarithm convention; existing generator continuation; later exact-evaluation cross-references |

The companion article is already coherent as a standalone research subtree. An alternative is to retain the entire package under a new research directory and add only status links to the canonical manuscript before merging individual sections.

When merging individual sections, copy the associated `figures/`, `code/`, and `data/` files together. The scripts resolve paths relative to their own package directory; changing the code/data directory relationship requires reviewing those paths. The exact S14 certificate depends on its frozen vector and shared `mixed_gaussian_common.py`, not on rerunning the discovery search.

### Labels and bibliography

Preserve the new prefixes `ker:`, `ord:`, `mesh:`, `neg:`, and `mix:`. The delivered source also has a few section-level identifiers beginning `sec:`; search them against the target manuscript before merging. Do not blindly rename old conjecture labels as theorem labels or introduce a second definition of an existing compatibility alias.

Merge the relevant bibliography entries from `references.tex` into the existing bibliography, retaining classical attribution and source-archive identities. Do not paste a second `thebibliography` environment inside the first. In particular, the old and new uses of gamma asymptotics, real-rooted differential operators, and the polylogarithm definitions should retain their cited primary sources.

## 4. Conventions and preamble compatibility

The canonical preamble at the pinned commit already supplies `\Li`, `\Ima`, `\Rea`, `\E`, `\R`, `\C`, `\Q`, `\D`, `\dd`, `\eps`, `\Res`, `\sgn`, the theorem environments, and the standard mathematics/table/graphics packages. It calls the imaginary unit `\iu`; the delivered article uses `\ii`.

A minimal guarded compatibility addition, after checking for local definitions, is:

```tex
\providecommand{\ii}{\iu}
\providecommand{\mesh}{\operatorname{mesh}}
\providecommand{\supp}{\operatorname{supp}}
\providecommand{\FP}{\operatorname{FP}}
```

Keep the manuscript's book class, chapter numbering, page geometry, and theorem counters. Only the standalone companion article should use its delivered document preamble unchanged. The proof sections use ordinary cross-references; their placement should preserve those labels and the displayed function definitions from the introduction.

| Symbol or convention | Required meaning |
|---|---|
| `Li_(a,b)(z,w)` | Sum over n>m>=1 of z^n w^m/(n^a m^b), then the stated continuation |
| `F_(a,b)(z)` and `g_(a,b)` | F=Li_(a,b)(z,1), g=Im F(i), on the principal slit plane |
| `D` in the negative-order section | z d/dz; the derivative identity defines negative integer outer orders without using a divergent boundary series |
| `f_N(v)` | Residual kernel (1-v)^N/(1+v), not the harmonic coefficient sequence f(n) |
| `K_N(p,y)` and `M_N` | Pointwise residual kernel and its maximum over the full square |
| `R_N(a,b)` and `C_N` | Scaled Euler error and its supremum over the specified gamma order family |
| `C_*` | Existing sharp constant uniform in both orders and all truncation indices; it is not M_infinity or lim C_N |
| Gamma variables | Independent, rate one; shape zero is represented by a point mass at zero |
| `Q_n` | Reciprocal-gamma Appell polynomial, with roots ordered as stated in the zero section |
| rho=1 | Endpoint of the derivative family with k>=1; not a convergence claim for the undifferentiated Lerch sum |
| `S_p` | Sum of (-1)^n H_n/(2n+1)^p; its total weight is p+1 |
| `mathcal O(t)` | Odd function of t whose coefficients are the even-index values S_(2m); this differs from the existing even function generated by odd-index values |
| Finite part | Constant Laurent coefficient in the explicit local coordinate t-t_0 |

The lower-order example and the higher-degree rational kernels have different numbers of sign changes; do not extend the one-crossing proof to every negative outer order by analogy. Likewise, bounds for M_N do not automatically establish the corresponding optimal averaged constant C_N.

## 5. Quantifiers to preserve in theorem statements

- Kernel uniqueness, kernel decrease, axis reduction, axis uniqueness and averaged-constant decrease are eventual statements, except for the separately proved exact N=2 kernel theorem. No numerical starting index is asserted.
- The C_N leading and second-scale asymptotics are global over the positive order family only because the axis-reduction theorem is included.
- The second correction has scale N^(-kappa)/sqrt(log N). Its large first inverse-log coefficient makes moderate-N accuracy a separate problem. A later Taylor moment is an upper bound, not that second asymptotic term.
- The near-maximizer criterion uses an error o(N^(-p))=o(C_N-1). A weaker o(1) approximation permits other moving-order regimes.
- The mesh theorem holds at every n>=2. The explicit Lerch threshold is sufficient, not claimed minimal; the joint-growth result controls relative locations and total zero count, not uniform constant offsets.
- The negative-order transition theorem covers m=2 and m=3, for every real b>0. It does not classify all m.
- The sampling and finite-part identities are analytic equalities. The frozen S14 relation is a conjectured equality accompanied by a proved proximity statement.
- Restricted formal relation-space obstructions do not prove independence of complex periods or global nonreducibility.

## 6. Replay and typesetting

From the package root, the exact replay is:

```sh
python code/verify_all.py
```

Optional independent numerical/symbolic diagnostics are requested explicitly:

```sh
python code/verify_all.py --diagnostics
```

The default replay includes the exact kernel, exponent, mesh and S14 certificates. It does not run PSLQ discovery. `verification/replay_report.json` records commands, return codes, full child-process output and timings for an actual replay. The actual environment versions are in `provenance/runtime.json`; installed optional libraries are not mathematical premises of the analytic proofs.

The standalone article can be typeset using:

```sh
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

After merging into the book, rebuild the manuscript and review cross-references, bibliography keys, table widths, figures and page breaks in that new context. The delivered PDF review concerns the standalone article, not a later manuscript layout.

## 7. Proof status and further work

The article supplies ordinary mathematical proofs plus finite exact rational certificates where stated. It does not supply Lean or other proof-assistant formalizations. Numerical diagnostics remain separate from exact arithmetic, and exact arithmetic remains relative to the analytic tail theorems proved in the article.

The principal remaining targets are a finite-index classification of the two maximizing problems, useful explicit starting indices, sharper Appell mesh bounds, full negative-order sign classification, and an exact functional relation proving the unresolved mixed Gaussian reductions. The source archives should remain immutable historical records; record supersession in the manuscript and editorial ledger rather than silently replacing their mathematical claims inside the old ZIP files.
