# Archive of historical document versions

Each entry preserves a `.tex`/`.pdf` document under `Analysis/FabiusFunction`
exactly as it stood in the commit that first introduced it to the repository
(history reachable from `main`, 2026-08-26); the one deliberate exception is
marked as a special entry in its description.  Later edits are not archived,
and a rename or move of an existing document did not create a new entry
(`git log --diff-filter=A -M`).  A `.tex` and `.pdf` sharing one directory
and base name are one document and share one entry; unrelated documents with
clashing names carry a numerical suffix, assigned chronologically and matched
case-insensitively (Windows checkouts cannot separate such names).  Entries
whose `.tex` — or, for PDF-only entries, whose PDFs — were byte-identical to
files elsewhere in the current HEAD were pruned as redundant (2026-08-26):
the live tree already preserves those versions exactly.

Entries are grouped by content and purpose into the subdirectories below.
These are frozen historical artifacts: the Libertinus font and PDF-rebuild
policies for living documents do not apply here, and nothing in this tree
should be edited or rebuilt.

## `early-notes/`

Short informal notes from before the documentation campaign (from the old `Papers/` directory).

- **`Fabius Asymptotic/`** — Short informal note: an exact identity on a dyadic logarithmic scale, the large-argument determination of the expansion coefficients, and the 1-periodic remainder of the endpoint asymptotic.
  Files: `Fabius Asymptotic.pdf`, `Fabius Asymptotic.tex`.  Source commit: `8b8d25fa7` (2026-08-23).  Original location: `Analysis/FabiusFunction/Papers/Fabius Asymptotic/`.

- **`K-fold summation over the signed Thue-Morse sequence/`** — Short informal note on iterated summation of the signed Thue--Morse sequence: self-similarity and the Fabius equation, the zero runs, a compact formula for the k-fold sums, and the Lambert-W small-argument asymptotic.
  Files: `K-fold summation over the signed Thue-Morse sequence.pdf`, `K-fold summation over the signed Thue-Morse sequence.tex`.  Source commit: `8b8d25fa7` (2026-08-23).  Original location: `Analysis/FabiusFunction/Papers/K-fold summation over the signed Thue-Morse sequence/`.

## `standalone-studies/`

Self-contained formalization-backed articles on single questions.

- **`Non_Elementarity_of_the_Fabius_Function/`** — First version of the still-living paper: no elementary function agrees with F on any nonempty open subset of [0,1], proved via density of the analytic locus of elementary functions, with the Lean development described.
  Files: `Non_Elementarity_of_the_Fabius_Function.pdf`, `Non_Elementarity_of_the_Fabius_Function.tex`.  Source commit: `92d08dc56` (2026-08-25); `95d4723dd` (2026-08-25).  Original location: `Analysis/FabiusFunction/docs/Non_Elementarity_of_the_Fabius_Function/`.

- **`Small_Argument_Asymptotics/`** — The exponentially small small-argument expansion in the lower-Lambert phase: closed-form saddle jets, a general formula for every coefficient, the leading-derivative and amplitude laws, and numerical verification.
  Files: `Small_Argument_Asymptotics.pdf`, `Small_Argument_Asymptotics.tex`.  Source commit: `b001c6c38` (2026-08-24).  Original location: `Analysis/FabiusFunction/docs/Small_Argument_Asymptotics/`.

- **`fabius-inverse-dyadic-closed-form/`** — Derives a finite, fully non-recursive composition-sum formula for F(2^-n) from the triangular recurrence, with an increasing-chains multiple sum, a nilpotent-matrix interpretation, and a Lean formalization section.
  Files: `fabius-inverse-dyadic-closed-form.pdf`, `fabius-inverse-dyadic-closed-form.tex`.  Source commit: `1d94f7fd0` (2026-08-24).  Original location: `Analysis/FabiusFunction/Article/`.

## `primary-exposition/`

First-generation parallel drafts and selected versions of the synthesis paper *The Fabius Function and Rvachev's Up-Function*.

- **`Fabius_Function_and_Rvachev_Up/`** — One of the parallel first-generation drafts: self-similarity, probability, exact dyadic arithmetic, and the corrected small-argument asymptotic.
  Files: `Fabius_Function_and_Rvachev_Up.pdf`, `Fabius_Function_and_Rvachev_Up.tex`.  Source commit: `e42dcd3a9` (2026-08-24).  Original location: `Analysis/FabiusFunction/docs/drafts/Fabius_Function_and_Rvachev_Up/`.

- **`Fabius_Function_and_Rvachev_Up-2/`** — The draft that won: moved verbatim (pure rename) to docs/Fabius_Function_and_Rvachev_Up/ and thus the direct ancestor of the living primary exposition.
  Files: `Fabius_Function_and_Rvachev_Up.pdf`, `Fabius_Function_and_Rvachev_Up.tex`.  Source commit: `fb7d8070c` (2026-08-24).  Original location: `Analysis/FabiusFunction/docs/drafts/Fabius_Function_and_Rvachev_Up-2/`.

- **`Fabius_Function_and_Rvachev_Up-3/`** — Special entry, not a first version: the longest revision the primary exposition ever reached at its canonical path (620,640 bytes, 13,105 lines, commit ff2b86f24 ‘Polish the Poisson support specialization’, PDF rebuilt in the same commit), before later restructuring moved material into the walkthrough and frontier documents.
  Files: `Fabius_Function_and_Rvachev_Up.pdf`, `Fabius_Function_and_Rvachev_Up.tex`.  Source commit: `ff2b86f24` (2026-08-25).  Original location: `Analysis/FabiusFunction/docs/Fabius_Function_and_Rvachev_Up/`.

- **`Fabius_and_Rvachev_Up-2/`** — Parallel first-generation draft organized around ‘three functions, not one’, ending in the Legendre expansion and best polynomial approximation.
  Files: `Fabius_and_Rvachev_Up.pdf`, `Fabius_and_Rvachev_Up.tex`.  Source commit: `fb7d8070c` (2026-08-24).  Original location: `Analysis/FabiusFunction/docs/drafts/Fabius_and_Rvachev_Up/`.

- **`Fabius_and_Rvachev_up/`** — Parallel first-generation draft emphasizing the fast bit-recursive exact evaluator, denominator arithmetic, and the corrected full endpoint expansion.
  Files: `Fabius_and_Rvachev_up.pdf`, `Fabius_and_Rvachev_up.tex`.  Source commit: `e42dcd3a9` (2026-08-24).  Original location: `Analysis/FabiusFunction/docs/drafts/Fabius_and_Rvachev_up_article/`.

- **`Fabius_function_and_up_function/`** — The most compact of the parallel drafts: probability, Fourier analysis, dyadic arithmetic, 2-adic valuations, and the Fourier--Legendre expansion.
  Files: `Fabius_function_and_up_function.pdf`, `Fabius_function_and_up_function.tex`.  Source commit: `fa27ce2b8` (2026-08-24).  Original location: `Analysis/FabiusFunction/docs/drafts/Fabius_function_and_up_function/`.

## `primary-supplements/`

Companion documents extending and auditing the primary exposition.

- **`Fabius_Function_Missing_Parts/`** — Supplement on the totalized inverse and the hidden machinery of the all-orders endpoint expansion: periodic saddle jets, the centered exponent, formal exponential/Gaussian contraction/logarithm.
  Files: `Fabius_Function_Missing_Parts.pdf`, `Fabius_Function_Missing_Parts.tex`.  Source commit: `0d4da526c` (2026-08-25).  Original location: `Analysis/FabiusFunction/docs/Fabius_Function_and_Rvachev_Up/drafts/Fabius_Function_Missing_Parts/`.

- **`Fabius_Function_Missing_Parts-2/`** — Second, broader supplement: total inversion, strong non-elementarity, measure-theoretic probability--Laplace bridges, endpoint/tilted Laplace moments, and the algebra behind the saddle expansion.
  Files: `Fabius_Function_Missing_Parts.pdf`, `Fabius_Function_Missing_Parts.tex`.  Source commit: `700594ac6` (2026-08-25).  Original location: `Analysis/FabiusFunction/docs/Fabius_Function_and_Rvachev_Up/drafts/Fabius_Function_Missing_Parts-2/`.

## `q-calculus/`

Article drafts on the base-1/2 q-calculus behind the dyadic formulas.

- **`Fabius_q_Special_Functions/`** — Rewritten dyadic q-calculus article (base q=1/2): the geometric coefficient-extraction theorem, exact values at inverse powers of two, translation invariance, and arbitrary dyadic arguments.
  Files: `Fabius_q_Special_Functions.pdf`, `Fabius_q_Special_Functions.tex`.  Source commit: `b14c6e375` (2026-08-24).  Original location: `Analysis/FabiusFunction/docs/drafts/Fabius_q_Special_Functions_article/`.

- **`fabius-q-special-functions/`** — Draft arguing the q-special functions are structural: q-Pochhammer symbols, Gaussian binomials, Thue--Morse blocks and Prouhet cancellation, the matching refinement products, and the global q-series.
  Files: `fabius-q-special-functions.pdf`, `fabius-q-special-functions.tex`.  Source commit: `4f132ee8f` (2026-08-24).  Original location: `Analysis/FabiusFunction/docs/drafts/fabius-q-special-functions-article/`.

## `lean-walkthrough/`

Versions of the guided walkthrough of the Lean development.

- **`Fabius_Function_Lean_Walkthrough/`** — Parallel walkthrough draft organized around the curated root facade, the four kinds of source module, and the naming conventions that encode intent.
  Files: `Fabius_Function_Lean_Walkthrough.pdf`, `Fabius_Function_Lean_Walkthrough.tex`.  Source commit: `768357067` (2026-08-24).  Original location: `Analysis/FabiusFunction/docs/fabius_lean_walkthrough/drafts/`.

- **`fabius_lean_walkthrough/`** — First version of the living walkthrough: repository and toolchain orientation, what the umbrella module exposes, an exploration workflow, and a layered view of the development.
  Files: `fabius_lean_walkthrough.pdf`, `fabius_lean_walkthrough.tex`.  Source commit: `dd7d5474a` (2026-08-24).  Original location: `Analysis/FabiusFunction/docs/fabius_lean_walkthrough/`.

## `glossary/`

Versions of the mathematical glossary for the development.

- **`FabiusFunction_Mathematical_Glossary/`** — First version of the glossary: 423 alphabetized headwords covering the Lean development and its documents.
  Files: `FabiusFunction_Mathematical_Glossary.pdf`, `FabiusFunction_Mathematical_Glossary.tex`.  Source commit: `eb1ce0122` (2026-08-25).  Original location: `Analysis/FabiusFunction/docs/FabiusFunction_Mathematical_Glossary/`.

- **`FabiusFunction_Mathematical_Glossary-2/`** — Parallel glossary draft with purpose/notation front matter and a subject guide preceding the alphabetical entries.
  Files: `FabiusFunction_Mathematical_Glossary.pdf`, `FabiusFunction_Mathematical_Glossary.tex`.  Source commit: `0c3d90018` (2026-08-25).  Original location: `Analysis/FabiusFunction/docs/FabiusFunction_Mathematical_Glossary/drafts/`.

## `research-frontiers/`

Per-topic research dossiers of non-formalized mathematics, their quarantine register, and the first consolidated volume that superseded them.

- **`Fabius_Dyadic_Asymptotic_Bridge/`** — Bridge from exact dyadic arithmetic to endpoint asymptotics: coefficient extraction, q-binomial collapse, phase locking, vertical coefficient extraction, and an exact Bromwich-to-coefficient collapse.
  Files: `Fabius_Dyadic_Asymptotic_Bridge.pdf`, `Fabius_Dyadic_Asymptotic_Bridge.tex`.  Source commit: `35bdb53ef` (2026-08-25).  Original location: `Analysis/FabiusFunction/docs/non-formalized-research-frontiers/Fabius_Dyadic_Asymptotic_Bridge/`.

- **`Fabius_Dyadic_Formulae_and_Alternative_Representations/`** — ‘The dyadic web’: moment corrections, half-base q-interpolation, binary telescopes, and discrete extrapolation, unified into one dyadic identity with a compact identity sheet.
  Files: `Fabius_Dyadic_Formulae_and_Alternative_Representations.pdf`, `Fabius_Dyadic_Formulae_and_Alternative_Representations.tex`.  Source commit: `a33c8e02a` (2026-08-25).  Original location: `Analysis/FabiusFunction/docs/non-formalized-research-frontiers/Fabius_Dyadic_Formulae_and_Alternative_Representations/`.

- **`Fabius_Dyadic_Formulae_to_Asymptotics/`** — Second bridge dossier: q-binomial decompression, the endpoint--Laplace transfer, and two sharp routes to the lower-Lambert expansion (moment comparison and a coefficient saddle).
  Files: `Fabius_Dyadic_Formulae_to_Asymptotics.pdf`, `Fabius_Dyadic_Formulae_to_Asymptotics.tex`.  Source commit: `0e6c0f7d4` (2026-08-25).  Original location: `Analysis/FabiusFunction/docs/non-formalized-research-frontiers/Fabius_Dyadic_Formulae_to_Asymptotics/`.

- **`Fabius_Dyadic_q_Connections/`** — Dyadic calculus connecting exact values, Appell blocks, Thue--Morse differences, Gaussian interpolation, and discrete limits. No PDF of this dossier was ever committed historically; the accompanying PDF was generated from the archived TeX on 2026-08-26 (21 pages, Libertinus prose, no unresolved references). It faithfully renders the never-built draft, including the draft's own layout defects: one long inline path overruns the right margin, and a few long module names collide with the second column of the appendix table. The TeX itself remains frozen.
  Files: `Fabius_Dyadic_q_Connections.tex` (first-committed), `Fabius_Dyadic_q_Connections.pdf` (generated 2026-08-26).  Source commit: `6d2a6f522` (2026-08-25).  Original location: `Analysis/FabiusFunction/docs/non-formalized-research-frontiers/Fabius_Dyadic_q_Connections/`.

- **`Fabius_Thue_Morse_Convergence_Rate/`** — Sharp n*2^-n convergence law for iterated Thue--Morse prefix-sum approximants of F, with exact centering and faster recentered approximations.
  Files: `Fabius_Thue_Morse_Convergence_Rate.pdf`, `Fabius_Thue_Morse_Convergence_Rate.tex`.  Source commit: `f79f6280d` (2026-08-25).  Original location: `Analysis/FabiusFunction/docs/non-formalized-research-frontiers/Fabius_Thue_Morse_Convergence_Rate/`.

- **`Fabius_Thue_Morse_Convergence_Rates/`** — Companion dossier on the same hierarchy: lattice deconvolution, exact grid drift, the first-order quantization error, an exact midpoint identity, and bias-removed accelerated reconstructions.
  Files: `Fabius_Thue_Morse_Convergence_Rates.pdf`, `Fabius_Thue_Morse_Convergence_Rates.tex`.  Source commit: `faea4d140` (2026-08-25).  Original location: `Analysis/FabiusFunction/docs/non-formalized-research-frontiers/Fabius_Thue_Morse_Convergence_Rate-2/`.

- **`Primary_Exposition_Gap_Register/`** — Quarantine register of claims removed from the primary exposition during its proof-correspondence audit, each awaiting an exact Lean counterpart, with explicit promotion rules.
  Files: `Primary_Exposition_Gap_Register.pdf`, `Primary_Exposition_Gap_Register.tex`.  Source commit: `150bdcd01` (2026-08-25).  Original location: `Analysis/FabiusFunction/docs/non-formalized-research-frontiers/Primary_Exposition_Gap_Register/`.

- **`Repeated_Integration_and_Rvachev_Up/`** — The 2012 Mathematics Stack Exchange repeated-integration construction: the finite stages are box splines, exact n-th stage formulas, a positive Peano kernel, and the sharp convergence rate.
  Files: `Repeated_Integration_and_Rvachev_Up.pdf`, `Repeated_Integration_and_Rvachev_Up.tex`.  Source commit: `52b136ec9` (2026-08-25).  Original location: `Analysis/FabiusFunction/docs/non-formalized-research-frontiers/Repeated_Integration_and_Rvachev_Up/`.

- **`Rvachev_Up_from_Repeated_Integration/`** — Second treatment of the same construction: the integration operator as a probability operator, exact error decomposition by tail replacement, derivative geometry, and numerical use.
  Files: `Rvachev_Up_from_Repeated_Integration.pdf`, `Rvachev_Up_from_Repeated_Integration.tex`.  Source commit: `35bdb53ef` (2026-08-25).  Original location: `Analysis/FabiusFunction/docs/non-formalized-research-frontiers/Rvachev_Up_from_Repeated_Integration-2/`.

- **`non-formalized-research-frontiers/`** — The first consolidated frontiers volume (19,667 lines): merges all former per-topic dossiers into one document with a consolidation map and a Lean-object crosswalk.
  Files: `non-formalized-research-frontiers.pdf`, `non-formalized-research-frontiers.tex`.  Source commit: `421bb071a` (2026-08-25); `afc63887b` (2026-08-25).  Original location: `Analysis/FabiusFunction/docs/non-formalized-research-frontiers/`.

