# Surreal Scalars in Theoretical Physics

**Black-Hole Singularities, Asymptotic Structure, and the Limits of Replacing
the Scalar Field**

A merged research report, 79 pages. Everything in this directory other than
`article.tex` and `article.pdf` is preserved source material.

```
article.tex   the merged report, standalone LaTeX with an internal bibliography
article.pdf   the compiled 79-page report
README.md     this guide
sources/      the three source manuscripts, unmodified, with their READMEs and audit
code/         the three source verification programs, unmodified
data/         the three recorded verification records, unmodified
```

---

## Read this first: the conclusion is negative

Surreal and surcomplex numbers make the hierarchy of quantities near a
gravitational singularity **exactly representable**. They do **not** make the
spacetime regular.

**The sentence this report exists to refuse, in any form, is that surreal
numbers resolve the black-hole singularity.** Four independent facts, each
re-derived from the metric for this merge rather than copied from a source:

* The Kretschmann scalar of Schwarzschild is exactly `K = 48 M²/r⁶`.
* Under a formal radial change `r = s^q·w(s)` with `w(0) ≠ 0` the pole order
  becomes exactly `6q` with leading coefficient `48 M²` **unchanged** —
  checked for `q = 1, 2, 3`. *No radial reparametrization removes the
  blow-up.*
* The proper time from rest at `R` to `r = 0` is `(π/2)·√(R³/2M)`, finite for
  finite `R, M`; and for **infinitesimal** `R` it is *infinitesimal*, hence
  still finite (`v(τ) = (3/2)·v(R) > 0`). **The infall terminates either way.**
* The tidal component `R^r_trt = 2M(2M − r)/r⁴` diverges as `r → 0` and is
  unlimited at infinitesimal `r`.

And the exact identity `r⁶K = 48m²` has **no** field-valued solution at `r = 0`
in *any* characteristic-zero field, not merely in `R`. Evaluating at a nonzero
infinitesimal radius names another point of a punctured domain. It supplies no
missing endpoint, no continuation law and no observable rule.

What *is* true, and is worth a 79-page report: the surreal/Hahn language
records the power **and** the coefficient of every divergence exactly, keeps
competing scales separate, and detects when an expansion has been used outside
its regime. That is a real gain in representation and nothing more.

---

## The claim-status firewall

This is the only report in this collection whose subject is not mathematics,
and its entire value is the firewall between what is proved and what is
proposed. Three classes of statement are kept **separately and visibly
labelled throughout the article** — in every theorem header and at the head of
every substantive paragraph. The same ledger is Table 1 of the article
(Section 2), so the contract is stated before anyone opens it, and again here
so it is stated before anyone opens the article.

| Tag | Tier | What it means |
|---|---|---|
| **[E]** | exact symbolic identity | A finite algebraic or differential identity in ordinary real/complex symbols, checked **exactly** — never to a tolerance — by at least one of the three programs, or derived from such by finite algebra. **This is the entire content of what the programs establish.** |
| **[C]** | conditional theorem | An ordinary mathematical proof in the text, under hypotheses stated in full. The hypotheses are strong and **are established for no physical model**. Nothing in this tier is machine-checked. |
| **[A]** | assessment | An argument, not a result: a judgement, a declared modelling choice, a power-counting estimate, a proposal, or a negative claim scoped as a *missing implication* rather than an impossibility theorem. |
| **[I]** | imported | A published result used with its own hypotheses intact, neither reproved nor strengthened. A **provenance marker**, not a fourth claim tier. |

Tag counts in the article: 53 `[E]`, 51 `[C]`, 140 `[A]`, 34 `[I]`.

### What lands in which tier

**[E] — exact symbolic identities.** The general static-spherical `K[f]`,
`Scal` and `G^t_t`; Schwarzschild `K = 48m²/r⁶`, `K(2m) = 3/(4m⁴)`, vacuum
`Ric = 0`; the Eddington–Finkelstein determinants `−1` and `−r⁴sin²θ`; the
`E = 1` infall law `r³ = (9/2)mu²` and `K = 64/(27u⁴)`; the tidal coefficients
`4/(9u²)`, `−2/(9u²)` and the Jacobi exponents `4/3, −1/3, 2/3, 1/3`; the
closed-form proper time `(π/2)√(R³/2M)`; the nonradial `2/5` balance and the
**exact crossover integrand factor**; the Kasner coefficient `64/27` and all
three flat exceptional cases; the Hayward central limits `K(0) = 24/ℓ⁴`,
`ρ(0) = 3/(8πℓ²)`, `r_c = (2mℓ²)^(1/3)`; the outer/inner/transition rational
rewrites and eight exact geometric remainders; the boundary-layer `b″(0) = −2`;
the finite-part shifts (`FP` non-multiplicative, `a ↦ a − c`); the Gaussian
regulator integrals; the Borel pole residue; factorial-ODE residuals for
`N = 1..8`; the double-null `R_uu` normalization and areal-radius gradient
norm; and `r_Q = 48^(1/6)(m·l_P²)^(1/3)` **as algebra**.

**[C] — conditional theorems, hypotheses established for no physical model.**
The formal Einstein reduction over `C^∞(U,R)[[h]]`; the coefficientwise
standard-part reduction over a Hahn coefficient algebra, with its shadow
corollary; pole persistence under ramification (valuation route) and
unlimitedness of a leading pole in any ordered extension (order route — a
*different* theorem, both kept); the algebraic endpoint obstruction; the
set-sized collapse of the full fine topology; the inner/outer strong-
summability criteria, sharp at `α = 2/3`; the finite Hermitian spectral
theorem; the finite quantum-shadow theorem with its conditioning boundary;
standard part and the two elementary obstructions; bounded-frame valuation
invariance; the dominant-balance lemma; the `Exp_EK` phase/derivation
incompatibility, `Exp_EK(iωt) = 1`, and the infinite-period proposition.

**[A] — assessments.** The reading of `r_Q` as a threshold; the whole
loss-of-control argument; the conservative architecture (ordinary spacetime +
controlled Hahn/transseries coefficients + explicit real-shadow map), called
the most defensible *starting point* and not a derived necessity; standard part
as an apparatus readout rule; the framework comparison; the Nieto critique; the
five-stage program, four benchmarks, four projects and proposed module names;
and the final assessment.

**Flattening these tiers would manufacture exactly the overclaim all three
manuscripts were written to refuse** — most obviously by presenting the
Einstein reduction as a theorem about general relativity rather than about
formal coefficient equations under stated conditions, or by letting
"Schwarzschild at an infinitesimal radius" read as a physical regime.

### One placement decision, made deliberately

Section 8 computes Schwarzschild at an infinitesimal radius. **Section 9 —
"The classical theory loses control before a literal infinitesimal scale" —
follows it immediately**, not a dozen sections later. Source 14 makes that
argument a headline, source 12 buries it inside its effective-field-theory
section and source 13 defers it. The buried version invites precisely the
misreading the report exists to prevent, so the merge follows 14 on placement:
a positive *real* high-curvature scale `r_Q` is encountered first, a literal
infinitesimal lies below **every** positive real cutoff ratio, and the
computation of Section 8 is therefore a mathematical extension of a classical
formula and not a physical regime.

---

## Where it came from

Three source archives, all pinned to `VladimirReshetnikov/Surreal` at commit
`39f2be6667ade51bca2b45daa47e289d69c09764`.

| id | manuscript | files in `sources/` |
|---|---|---|
| 12 | scalar-extension assessment (34 pp., 25 refs) — the base | `12-scalar-extension-assessment.tex`, `-README.md`, `-source-audit.md` |
| 13 | no-go obstructions (29 pp., 18 refs) | `13-no-go-obstructions.tex`, `-README.md` |
| 14 | black-hole singularity limits (31 pp., 23 refs) | `14-black-hole-singularity-limits.tex`, `-README.md` |

Duplication between them is very high — on the order of two thirds. All three
independently rebuild the static-spherical connection and the full Riemann
tensor in SymPy and re-derive the same Schwarzschild quantities from the metric
alone; 12 and 14 print the *same* formula `r_Q = 48^(1/6)(m·l_P²)^(1/3)` with
the same "power counting, not a derived threshold" disclaimer. The shared spine
— what a singularity is; Schwarzschild at infinitesimal radius with infall and
tides; a conditional reduction of the Einstein equations; a regular-core
comparison; finite-dimensional surcomplex quantum algebra; quantum fields,
regulators and transseries; a framework comparison; a staged program; a claim
ledger and a curvature appendix — **is printed once**.

### What each contributed uniquely

* **12 — scalar-extension assessment (base).** Pole persistence under formal
  ramification `r = s^q·w(s)` (the valuation route); the boundary-layer family
  `b_δ = δ⁴/(δ² + x²)` with `b″(0) = −2`, showing uniform smallness of a
  perturbation does not bound curvature; the **exact inner and outer Hahn
  support criteria for the Hayward core, summable iff `α < 2/3` / `α > 2/3` and
  neither at `α = 2/3`**, with the exact transition form and exact finite
  remainders; the formal Einstein reduction over `C^∞(U,R)[[h]]` with `π₀`; the
  derivation of `Exp_EK` with kernel `2πi·Oz` and `Sin_EK(b) = sin(b_fin)`,
  **plus its proved incompatibility with any derivation killing `R` with
  `Dω = 1`**, and the real-time corollary `Exp_EK(iωt) = 1`; the
  refutation-by-counterexample of the published surreal-singularity proposal;
  the units-and-falsifiability material; the two-parameter valuation power
  counting `l_P⁴K = 48ε^(4β−6α)`; the Gaussian regulator integrals; the
  audit, notation and claim-status appendices.
* **13 — no-go obstructions.** The three-way taxonomy of replacement proposals
  (algebraic scalar extension / non-Archimedean coefficients on ordinary
  spacetime / a genuinely surreal-valued spacetime), kept rigorously separate
  throughout; the **coefficientwise Hahn** reduction theorem (positive global
  support, Neumann support lemma) and its corollary that positive-order
  corrections cannot repair a singular shadow, with five named escape routes;
  the algebraic endpoint obstruction; the two elementary obstructions (no
  division by zero, `st` not multiplicatively extendable, no smallest positive
  infinitesimal); bounded-frame valuation invariance; the dominant-balance
  principle; anisotropy and the Kasner coefficients with all three flat cases;
  the weak-singularity `s`-weighted tidal diagnostic finite iff `q > 1`; the
  double-null identities; the Borel-residue example and `e^(−1/ε) ∉ R((ε^Q))`;
  `FP` non-multiplicative and reparametrization-dependent; the
  infinite-period proposition for a global phase homomorphism; the
  `1/(x+iη)` distributional non-inheritance; the `H = εσ_z, T = ε⁻¹`
  non-commuting-reduction counterexample; the argument that the ultraviolet
  question is dynamical, not arithmetic; measurement and recoverability; and
  the five-stage A–E program with **failure conditions the system should
  report rather than paper over**.
* **14 — black-hole singularity limits.** The **small-angular-momentum
  crossover**: `r ~ ((5/2)√(2m)|j|s)^(2/5)`, `K ~ s^(−12/5)`, the exact
  dimensionless quadrature, its `J/m → 0` limit uniform *only on bounded
  positive intervals*, `Φ(R) = ∫₀^R u^(3/2)/√(1+u²)du` with `(2/5)R^(5/2)` and
  `(2/3)R^(3/2)` endpoints, and the `α ≶ (3/2)β` sector tests; the
  order-theoretic proof that a leading pole stays unlimited in **any** ordered
  extension fixing `R`; the loss-of-control section, promoted here to Section
  9; the noncanonical-subtraction example `ε = η + cη²`; the purely real
  counterexample `δ·sin(x/δ)` to interchanging reduction and differentiation;
  the remark that the Hayward `r⁵` term becomes `|x|⁵` along a Cartesian line,
  so the ansatz is **not** `C^∞` at the centre; Kerr, near-extremal
  Reissner–Nordström and BKL-oscillatory regimes; the survey of published
  surreal-physics proposals; the beyond-all-orders factorial-series ambiguity
  with residuals for `N = 1..8`; the four-question test for what a resolution
  must deliver; and Projects A–D with explicit success criteria.

### How duplicates and conflicts were handled

* **Printed once**, with the union of statements and caveats: standard part;
  the fine-topology collapse (same Conway-cut proof in all three — with all
  three caveats kept: set-sized only, *not* the proper class, *not* the
  intrinsic valuation topology of a set-sized Hahn field, and four named
  alternative topologies); the finite Hermitian spectral theorem; the
  endpoint obstruction (13 and 14, same one-line proof); the curvature, infall,
  Kasner, Hayward and `r_Q` computations.
* **Both proofs kept, marked.** Pole persistence is two *different* theorems:
  12's valuation argument gives **ramification invariance**, 14's order
  argument gives **extension invariance**. Neither implies the other, and the
  article says so in a dedicated remark.
* **Both frameworks kept, marked.** The Einstein reduction over
  `C^∞(U)[[h]]` (12 and 14, same theorem, printed once) and over a Hahn
  coefficient algebra with strictly positive global support (13) have different
  hypotheses and different proof ingredients. They are separate theorems.
* **Quantum shadow merged, not averaged.** One theorem with four clauses: the
  Born-weight clause (14), the projection and joint-probability clauses (12),
  and the **conditioning boundary** — correct only when the outcome probability
  has nonzero standard part (13).
* **An apparent conflict that is not one.** 13 proves any global phase
  homomorphism extending the finite-angle rule has an *infinite period*; 12
  constructs `Exp_EK` with kernel `2πi·Oz`, which contains infinite omnific
  integers. The construction is an **instance** of the proposition, not a
  counterexample; the article records why.
* **The one editorial conflict** was placement, resolved as described above.

---

## Relation to the neighbouring reports

Nothing else in this collection contains general relativity, quantum mechanics
or field theory, so this report carries the whole burden of its own reading
contract. Two companion reports are load-bearing, and in both cases the
relation is **inherit and cite**, never restate.

* **`docs/foundations-and-computation/foundations/`** owns the
  workspace-localization theorem (every *set* of surcomplex numbers already
  lies inside one divisible set-sized workspace `K_Γ = C((t^Γ))`) and the size
  obstructions any candidate foundation must respect. This report cites the
  localization theorem for its workspace discipline and defers to the size
  obstructions for anything bearing on a genuinely surreal-valued spacetime,
  rather than re-arguing set-theoretic legality. No content is duplicated: the
  physics manuscripts ask a different question of the same facts.
* **`docs/surcomplex/differential-equations/`** owns the oscillation
  obstruction and the phase vocabulary. This report **cites its oscillator
  corollary instead of re-deriving the obstruction**, and adopts its **three
  phase symbols** without exception — the finite angle `θ ∈ O`, the
  infinitesimal phase residue `η ∈ m`, and the accumulated phase `B ∈ No`,
  which is *not* an angle. It does **not** print the false sentence "the phase
  of the solution is `log ω`" except inside the warning that quotes it as
  false; the true sentence is "the accumulated phase of the coefficient `i/ω`
  is `log ω`, which is infinite, so there is no solution."
* **`docs/surcomplex/analysis/`** and **`docs/surcomplex/trigonometry/`**
  supply the Hahn-summation-versus-convergence distinction, the coefficient
  function classes and the common-domain warning example, and the
  Ehrlich–Kaplan integer-part global normalization together with that report's
  explicit refusal to select a scalar derivation.
* **`docs/surquaternions/`** is named only to prevent a transfer. That material
  is **noncommutative**; every result here uses commutativity somewhere
  (valuation additivity, the Neumann series for the metric inverse, `st` as a
  ring homomorphism, the Rayleigh-quotient step, Hahn convolution), and nothing
  here may be lifted there without reproof. The article's derivative and
  exponential ledger records the specific hazard: `Exp_EK` **is** a
  homomorphism on the commutative surcomplex field, while a quaternionic radial
  exponential is **not** one for noncommuting arguments. Both are true, of
  different objects.

---

## What is NOT claimed

Appendix D of the article is the consolidated register: **31 numbered items
covering the 36 explicit non-claims the three manuscripts state between them.
Not one was dropped.** It is part of the result, not a disclaimer appended to
it. In outline:

* **Provenance.** Prepared with AI assistance; not refereed; no priority claim
  for any proposition, computation or benchmark. **No Lean formalization is
  included or claimed**, no member ran the repository's Lean build, no
  declaration-level audit was done, and none was done for this merge. The
  repository review was targeted (root README, documentation catalogue,
  surcomplex analysis, trigonometry), at one pinned commit; not every report
  was read and no repository file was changed. The literature search was
  targeted, not systematic: absence of a predictive model in the inspected
  sources is not proof that none was ever written. Berarducci–Mantova, ADH,
  van den Dries–Ehrlich, Ehrlich–Kaplan and Costin–Ehrlich are **imported**
  with their function-class restrictions intact; Penrose, Raychaudhuri,
  Dafermos, Dafermos–Luk, Donoghue, Hollands–Wald, Steinbauer–Vickers,
  Unruh–Schützhold, Horowitz–Marolf, Hatsuda, Hayward, Carballo-Rubio et al.,
  Andersson–Rendall, Damour–Henneaux–Nicolai, Benci–Horsten–Wenmackers, Loeb,
  Gubser et al. and Nieto are cited with hypotheses retained. One member's
  README lists a checksum file absent from its delivered directory; recorded,
  not repaired.
* **The programs.** 45 + 50 + 37 = **132 finite symbolic identities and nothing
  else**. They implement **no surreal arithmetic** — infinitesimal
  substitutions use ordinary positive symbols. They do not verify a surreal
  field, Hahn summability in general, set-theoretic foundations, global support
  lemmas, either reduction theorem, the discreteness proposition, the spectral
  theorem, analytic or PDE existence, geodesic completion, transseries
  convergence, quantum probability interpretation, or any physical
  interpretation; and they run no black-hole evolution. **Each prints its own
  scope disclaimer, reproduced verbatim in Appendix B** — including 12's "no
  claim of a verified surreal field, general PDE existence, geodesic
  completion, or a physical singularity cure", 13's "general mathematical
  proofs, asymptotic realization, and physical claims were not
  machine-verified", and 14's "finite symbolic identities only; no general
  analytic or physical validation".
* **Mathematical scope.** The discreteness proposition is set-sized only and
  does not claim the proper class is discrete. The endpoint obstruction is
  conditional on preserving that identity at the endpoint. Both reduction
  theorems require a nondegenerate smooth leading metric on one common domain;
  singular perturbations are outside them, and the boundary-layer example is
  evidence the hypotheses cannot be dropped. The shadow corollary is a
  conditional obstruction with five escape routes. The support criteria are
  about Hahn data, not real convergence. The quantum shadow excludes
  standard-probability-zero conditioning and infinite/hyperfinite experiments.
  Infinite-dimensional quantum theory, functional integration and measures are
  *not* supplied by algebraic closure, and a proper-class path sum is not
  licensed by Hahn summability. The realization bridge is open, with a named
  obstruction: differentiating `t^p(x)` produces `p′(x)·log t`. The triple-
  indexed transseries display is schematic.
* **Physical scope.** **A physical resolution of black-hole singularities is
  not supplied by scalar extension and is not claimed anywhere.** All negative
  conclusions are scoped as *missing implications*, not impossibility theorems:
  a future surreal-variable theory could still make nontrivial predictions, a
  quantum bounce is not excluded, and non-standard-part probability
  interpretations are not covered. `r_Q` is power counting, not a derived
  threshold or a minimum radius; the `ε^α, ε^β` families are *families of
  models* and do **not** assert the measured Planck length is infinitesimal —
  it is read throughout as an ordinary small positive real. The regular-core
  effective source `T = G/8π` has no microphysical Lagrangian and no stability
  proof; finite central curvature is not geodesic completeness; the ansatz is
  not `C^∞` at the centre. Kretschmann finiteness constrains no higher
  derivatives and is not a universal Lorentzian curvature norm. Generic
  oscillatory Kasner interiors may admit no single well-ordered expansion, and
  a Schwarzschild Puiseux law licenses no inference about generic interiors.
  Generic Jacobi rates do not apply to every Jacobi field; the crossover limit
  is uniform only on bounded positive intervals. The architecture, the stages,
  the benchmarks, the projects and the proposed module names are **proposals**,
  not descriptions of existing modules.

---

## Build

`article.tex` is standalone: full preamble, internal `thebibliography` (42
entries), no external `.bib`, no bibliography processor, no graphics, no font
files, no shell escape, no network access. Every `\label` carries the `phys:`
prefix (299 of them) and every cross-reference resolves inside the file;
companion reports are cited by title and repository path, never by their
labels.

```sh
latexmk -pdf -interaction=nonstopmode article.tex
```

If `latexmk` is unavailable, run `pdflatex -interaction=nonstopmode` three
times so the table of contents, the cross-references and the `cleveref` labels
settle. The delivered build has **zero LaTeX errors, zero warnings, zero
undefined references or citations, zero multiply-defined labels, zero duplicate
destinations, and zero overfull or underfull boxes**, at 79 pages. (The title
page sets `pageanchor=false` and the front matter is roman-numbered, which is
what keeps the page-anchor destinations unique.)

## Re-running the source verifiers

The programs in `code/` are the originals and their recorded outputs are in
`data/`. **Run them on a copy.** They were re-run that way for this merge and
all three pass again, on a newer interpreter than the one recorded: 45, 50 and
37 checks, every suite exit 0. None of the three writes any file beside itself,
but one member ships build helpers that create a `build/` directory and copy a
PDF over the package-level one, which is why copies are the rule here.

Nothing in `sources/`, `code/` or `data/` was modified to produce this report.
