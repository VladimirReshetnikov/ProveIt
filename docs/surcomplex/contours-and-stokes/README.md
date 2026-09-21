# Contours and Stokes: Jordan separation, Cauchy theory, and Stokes calculus on the surcomplex plane

One article, [`article.tex`](article.tex) (61 pages), assembled from **three
separately delivered manuscripts** with the duplicated mathematics stated once.

## What this is

Three archives arrived, all dated 21 September 2026, with titles differing by
one word — *Stokes **Calculus***, *Stokes **Integration***, *Stokes
**Formulae*** — over one body of work. All three refuse to transfer the
Jordan–Cauchy–Stokes package to `No[i]` as a unit, and all three split it into
the same four theories:

1. a coarse Jordan separation theorem in the standard-part topology, whose
   separator is the whole boundary monad rather than a curve;
2. an imported semialgebraic Jordan theorem (imported, not proved, in all
   three);
3. a Hahn-coefficient de Rham complex with coefficientwise Stokes, extended to
   infinitesimally deformed chains;
4. the holomorphic consequences — Cauchy, endpoint displacement, integer
   winding, microscopic circle and torus realizations of the perturbation
   residue — plus an algebraic rational contour pairing built from semialgebraic
   winding numbers.

They also share the positive-monomial rescaling lemma that turns radius-free
germs into polynomial-coefficient families, which is the technical hinge in
each. Roughly two thirds of each manuscript is the same mathematics in the same
order; that is packaging variation, not three results.

## Which archives, and what each contributed

Sources are kept verbatim under [`sources/`](sources/); the verification
scripts and their recorded runs are under [`code/`](code/) and
[`data/`](data/).

**`02-jordan-cauchy-stokes-calculus` — the base.** Its skeleton and its
versions of the shared theorems are the ones printed. Uniquely it contributes:

- The **unconditional** general contour representation. `Lemma 11.3` (residue
  transformation) and `Theorem 11.4` construct an *ordinary analytic* matrix `A`
  with `A f = (z_1^{d_1},…,z_n^{d_n})` from finite colength alone and insert
  `det A`. It needs only the strong residue expansion, ordinary finite-family
  residue transformation, and positive rescaling — **not** the companion
  geometry manuscript's Nullstellensatz or flatness results.
- The algebraic pairing stated as a **uniqueness characterization**: the unique
  `K`-linear pairing on rational differentials vanishing on exact ones and
  normalizing `dz/(z−a)` to `2πi · wind_sa`.
- **Both** compatibility results — chartwise agreement of pulled-back forms, and
  algebraic pairing versus Hahn integral on separated charts — together with the
  explicit case where they must not be conflated (`I_alg(S¹, dz/(z−(1∓t)))`
  = `2πi` and `0`).
- The quantitative finite-partition obstruction with its explicit bound
  `Σ(x_j−x_{j−1})² ≥ 1/N`.
- Rescaling stated as an **injective `K`-algebra homomorphism**, not a bare
  lemma.

**`03-jordan-cauchy-stokes-integration`.** Five whole bodies of material absent
from the base, all preserved:

- The entire **polynomial-chain theory** (§5): the factorial simplex functional
  taken as a *definition* over any characteristic-zero field, polynomial-chain
  Stokes proved by Zariski density, and the infinite-width/infinitesimal-height
  triangle with `L = ω`, `H = ω⁻¹` returning the ordinary answer `i`. This is a
  third, purely algebraic chain category.
- The **support-preserving Poincaré lemma** with its explicit radial operator.
- The numbered **order-valued ML estimate**.
- The whole **root-of-unity / Schnirelman section**, including the *positive*
  coefficientwise-recovery theorem and the rank-independent aliasing criterion.
- The **six-part comparison** with Berkovich, Chambert-Loir–Ducros, Mihara,
  Kaiser and Costin–Ehrlich, plus the decision table and the support audit.
- Its scope discussion against the base's general representation theorem, kept
  as §11.4 (see below).

**`04-category-sensitive-contour-calculus`.**

- The numbered **admissible-deformation definition** (the base leaves it
  implicit). Both 03 and 04 number a winding-stability theorem; the merged
  article prints 03's affine-scale form, which is the stronger.
- A second, independent route to a determinant torus formula, through
  univariate separating denominators `Q_i` and characteristic polynomials, with
  the explicit `det C` and the four-point cluster worked out — including the
  observation that the separated system has sixteen simple grid points where the
  original has four, `det C` vanishing at exactly the twelve spurious ones.
- The finite-parameter / truncation appendix justifying residue transformation
  when the transformation matrix is only formal in the parameters.

## The two conflicts, resolved rather than averaged

**Whether an arbitrary isolated complete intersection has a contour
representation.** The same statement is *proved* in 02, *assumed* in 04, and
*declined* in 03. The merged article prints 02's lemma and theorem with their
proof, and immediately afterwards reproduces 03's objection as a scope
discussion (§11.4), stating plainly that one of the three sources judged this
unproved and why, and that 04's route is conditional on an unrefereed companion
manuscript rather than independent. The two positions are shown to be consistent
because they concern different integrands: the open problem asks for a cycle for
the **untransformed** integrand, while the theorem supplies a coordinate torus
for the **transformed** one. Both representations are labelled with what each is
sharper for — 02's for logical economy, 04's for computation and zero-scheme
bookkeeping.

**Whether roots-of-unity quadrature recovers the Hahn contour integral.** 02
treats it as a negative result only; 03 devotes a section to the positive side.
They are compatible, and the hypothesis is doing all the work. The article
states the positive theorem **with** its decay condition — for every `γ`, the
set of `k` with `v(A_k) ≤ γ` is finite — and keeps 02's example
(`Q_N = 1/(1−b^N)`, valuation `0` for every `N`) immediately alongside as the
demonstration that the hypothesis cannot be dropped. It also records that the
condition cannot be met by a nontrivial sequence of finite valuations when no
countable subset is cofinal in the positive value group.

## Notation reconciled

One topology carried three names across the sources — *residue* (02),
*reduction* (03), *shadow* (04). The article calls it the **standard-part
topology** throughout, records the three synonyms once, and never uses them
again; the descriptive name is preferred because "residue" is committed to the
residue functionals and "shadow" is used in the analysis report for the ordinary
shadow of a zero.

Eight LaTeX labels (`thm:shadow`, `thm:cohomology`, `lem:pullback`,
`thm:homotopy`, `thm:cauchyformula`, `prop:overlap`, `thm:torus`, `prop:fine`)
occurred in at least two of the three files attached to **different**
statements. Every label in the merged file is prefixed `contours:` and every
cross-reference resolves inside the file.

Other fixed choices: `st` for the standard-part map (never `red`); `wind_sa` for
definable winding (never `Ind` or `w_F`); rescaling exponents always `ρ_j` with
radii `r_j = t^{ρ_j}`; coordinate powers `d_j`; and the three senses of
multiplicity — germ order `m`, global colength `μ`, local multiplicity `e_a` at
the actual displaced zero — kept apart.

## Ring discipline

Four coefficient rings appear under nearly identical notation and carry nearly
word-for-word identical theorem statements. §2.3 tabulates them and **every
theorem names its ring**; none is transferred between rings.

| Ring | Requirement | Where it is used |
|---|---|---|
| `H(U) = O(U)((t^Γ))` | all coefficients holomorphic on **one** common ordinary domain | all of §8 (Cauchy, endpoint transport, winding, Cauchy formula, moving poles) |
| `C[w]((t^Γ))` | every Hahn coefficient an ordinary **polynomial** | the target of the rescaling theorem |
| `A_n = C{z}((t^Γ))` | coefficients individually convergent germs, **no common polydisk** | §§10–11 (protecting radii, microscopic circle, tori, both general representations) |
| `K[[z]]`, `C[[z]]((t^Γ))` | **formal**, no convergence | injectivity of rescaling; the formal residue class `K((u))du / dK((u)) ≅ K` |

The witness `H(z) = Σ_{j≥1} t^j/(1 − jz)` for strictness of the radius-free
inclusion is stated once and reused.

## What is **not** proved

Every per-theorem non-claim from all three sources is preserved and collected in
Appendix C. The load-bearing ones:

- Neither supplied manuscript establishes a Jordan theorem for arbitrary
  fine-topological curves, nor Stokes for arbitrary fine-smooth functions on
  arbitrary surcomplex domains. Neither assertion is attributed to them.
- The full-fine discreteness proposition is **not** a theorem that a Hahn field
  with its own valuation topology is discrete; the radius supplied by the cut may
  lie outside the workspace.
- The standard-part Jordan theorem separates by a **thickened** curve. It cannot
  assign different sides to two infinitesimally separated points in one boundary
  monad, cannot distinguish two zeros in one standard-part fibre, and does
  **not** produce an unbounded exterior in the internal ordered-field sense.
- The semialgebraic Jordan theorem is **imported**, not proved by first-order
  transfer; its components are not connected in the intrinsic topology, and
  definable results do not supply ordinary singular homology of a proper class.
- Definable winding is an ordinary integer, not a surreal number of turns, and
  does not by itself define the integral of a general differential form.
- The mesh obstruction is to a *particular unrestricted finite-mesh definition*,
  not to all integration; hyperfinite partitions need a nonstandard universe and
  transfer structure, **not supplied by the field operations in `No`**.
- Polynomial Stokes certifies a *finite algebraic identity*; it does not transfer
  a statement quantifying over arbitrary integrable functions, and defines no
  integral for a form with poles on the chain.
- In infinite dimension `V((t^Γ))` must **not** be replaced by `K ⊗_C V`, and the
  global uniform-support convention is not claimed to be a sheaf for arbitrary
  covers.
- The deformed-chain pullback is the **specified** jet prolongation; no ordinary
  Taylor convergence and no canonical prolongation of every smooth function is
  claimed, and `Φ` is a parameterized chain, not a fine-continuous map.
- Not all contour integrals are infinitesimally deformation invariant —
  closedness is the controlling condition, and the deformed ellipse exhibits the
  failure exactly.
- The general representation does **not** assert that the *untransformed*
  integrand has the same torus integral; `det A` is not an optional Jacobian
  factor, since `A F` can introduce extra zeros; and `F` and `G` are not claimed
  to have identical zero schemes. Omitting the determinant in the separating-torus
  formula is likewise "generally wrong".
- The algebraic pairing is a **definition**, not a Riemann-limit construction; it
  determines no open-path logarithms and is not defined on all of `H(U)` or `A_n`.
- Coefficientwise sampling recovery is not a fine limit and in general not a
  valuation limit either.

The consolidated status statement: targeted rather than exhaustive literature
search (21 September 2026), no named published conjecture claimed solved, not
formally verified, symbolic checks validate the displayed finite examples only,
all sums and workspaces set-sized.

## Build

```sh
latexmk -pdf -interaction=nonstopmode article.tex
latexmk -c
```

A standard TeX installation with the packages listed in the preamble is enough;
no BibTeX, external graphics, or shell-escape is required. The recorded build is
**61 pages, 0 errors, 0 undefined references, 0 duplicate destinations, 0
overfull or underfull boxes**.
