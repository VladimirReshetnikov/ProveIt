# Contours and Stokes: Jordan separation, Cauchy theory, and Stokes calculus on the surcomplex plane

One article, [`article.tex`](article.tex) (87 pages), assembled from **four
separately delivered manuscripts** with the duplicated mathematics stated once.

## What this is

Three of the four archives arrived together, all dated 21 September 2026, with
titles differing by one word — *Stokes **Calculus***, *Stokes **Integration***,
*Stokes **Formulae*** — over one body of work. All three refuse to transfer the
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

The fourth archive is different in kind. It was written **against** the merged
report, at repository commit `39f2be66`, and it solves the problem that report
posed by name as open: a single admissible cycle for the **untransformed**
integrand `H dz/(F_1 … F_n)`. It contributes §§12–13, and it forced §11.4 and
§17.3 to be rewritten — as the record of a question that was open and of the
exact hypotheses under which it is now closed, not as a deletion.

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

**`05-untransformed-leray-cycles` — the answer to this report's own open
problem.** Everything it contributes is new to the article; it overlaps the
other three only in what it *takes* from them (the perturbation residue `Res_F`,
the support lemma with its exact-exponent sharpening, the four coefficient
rings, and the standing refusal to convert strong summability into fine
convergence). It becomes §12 *One cycle for the untransformed integrand* and §13
*The equation-adapted lift, its normalizations, and its limits*:

- A **discriminant-avoiding monomial direction in the target** (`lem 12.6`) —
  not in the source. This is what admits an arbitrary isolated `f`: it does not
  need the lowest weighted parts of the `f_j` to form an isolated complete
  intersection, which is precisely the objection 03 raised against a diagonal
  source rescaling.
- The **ramified Leray family** `thm 12.7`: a finite unramified cover
  `p : X → A` of a polyannulus of degree `μ`, possibly disconnected, with
  `f_j(Z(q,s)) = s^{κ_j} p_j(q)`, obtained by killing the *radial* monodromy
  only. **All of §12.3 is ordinary complex analysis with an ordinary complex
  radial variable `s`**; `s = t^ρ` is substituted only afterwards. That order of
  operations is the whole mechanism, and reversing it would be exactly the
  interchange of analytic convergence with Hahn summability the article refuses
  throughout.
- **Radius-free substitution of a positive-support Hahn map** into a radius-free
  *or formal* germ (`lem 12.2`). This is **not** the rescaling theorem `10.1`:
  neither implies the other, and neither manufactures a common radius.
- A **rooted-tree implicit-function lemma** (`lem 12.4`) over a commutative
  complex algebra that need not be a field, with uniqueness by least differing
  exponent. Explicitly **not** a Picard limit — it stays valid when the
  multiples of the least valuation are not cofinal.
- The **universal protecting cycle** and `thm 12.10`: one cycle
  `Z_0[T]`, chosen from `f` and a threshold `δ` **alone**, on which the original
  form integrates to `Res_F(H)` for *every* perturbation with support in
  `[δ,∞)` and *every* radius-free numerator. One contour for a whole valuation
  ball of perturbations; only the support certificate depends on the particular
  `E`.
- The **exact** equation-adapted lift `thm 13.2` with `F_j(Φ) = t^{κ_j ρ} p_j`
  holding identically (not modulo truncation), unique in `v(Υ) > Lρ`; the
  pole-free straight homotopy `thm 13.5`; the degree normalization
  `Res_F(J_F) = μ` proved **directly on the cycle** (`thm 13.6`); the
  finite-sheet trace `cor 13.7`; ideal annihilation `prop 13.8`; and the
  formal-coefficient extension `thm 13.10` by a separate finite-jet argument.
- A **worked wrong shortcut** (`ex 13.12`): on a coordinate torus with
  `|y|^3 ≪ |x|^2` the integral of `x y^2 / ((x^2+y^3)(x^2+3y^3))` is `0` while
  the residue is `1/2`. The `det [[1,1],[1,3]] = 2` of that example is used as a
  tripwire against silently replacing the integrand by an ordered-denominator
  transform without its determinant.
- **Pathologies that exercise the hypotheses**: the report's own witness
  `Σ_j t^j/(1−jx)` reused as a *perturbation*, so no common coefficient radius
  exists at all; and `Γ = Q²` lexicographic with `rρ < η` for every integer `r`,
  plus a perturbation support of order type `ω+1` lying in no finitely generated
  positive semigroup.

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

**What became of that open problem.** 05 answers it, and §11.4 now ends with a
paragraph *The resolution, and its exact hypotheses* rather than with an open
question. The history is kept deliberately, because the objection was **right**
about the coordinate torus: `ex 13.12` exhibits an ordinary germ for which the
original coordinate product torus returns `0` while the residue is `1/2`, so no
theorem about the untransformed integrand on a coordinate torus was ever
available. It is the **cycle** that had to change, not `thm 11.4`. Accordingly
four things are unchanged by the resolution, and are said so in the article:

- `thm 11.4` still does **not** assert that the untransformed form has the same
  *coordinate-torus* integral. That assertion is false.
- `det A` in `thm 11.4` and `det C` in `thm 11.5` remain **non-optional** for
  their own formulas. The new cycle does not remove them; it avoids needing
  them, by being a ramified finite cover instead of a torus.
- 03's germwise, coefficient-dependent cycle interpretation of `Res_F` remains
  correct, and remains the right description of what the defining series does by
  itself.
- The question is closed **only** under three hypotheses: a convergent isolated
  leading map `f`; one *specified* positive valuation lower bound `δ` with
  `supp E ⊆ [δ,∞)`; and a radius-free — or, by `thm 13.10`, formal — numerator.
  An arbitrary Hahn tuple with no such leading map, a non-isolated leading zero,
  and a support not bounded below by a positive element are all still outside
  the theorem. §17.3 keeps the problem statement verbatim and then says exactly
  this.

What is still open after 05: a canonical choice-independent cycle (only equality
of the *periods* is proved, `cor 12.11`); a chain-level homology comparison
across protecting weights, covers and scales; the formal-leading-map case; an
intrinsic invariant governing the best protecting and lifting scales; and
effectivity.

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
cross-reference resolves inside the file. **No pre-existing label was renamed or
removed when 05 was merged in** — other documents in this repository cite this
report's labels and a formalization ledger maps obligations to them by name — so
the 166 labels of the three-source article are all still present, with 80 added.

Six symbols of 05 were renamed to keep the conventions above, and §12.1 says so
explicitly: its `m_j`/`M` (target radial weights) became `κ_j`/`κ_Σ`, because
`m` is the order of a one-variable germ and `d_j` the coordinate powers; its
`b`/`c` became `b_pole`/`c_sep`; its `T`/`X` became `T`/`X` in sans-serif,
because `T_r` is the coordinate torus and `T_F` the endpoint correction; its
`⟨P⟩_N` became `P*`; and — the one that matters most — its `R_F` became
`Res_F`, because in this article `R_F` already denotes the **coordinate-torus**
functional of `thm 11.1`, and the entire content of §§12–13 is that a
*different* cycle computes `Res_F`.

`Res_F` itself is identified at its point of definition (§2.4) with the series
functional of the companion report *Finite Hahn Deformations: Division,
Conservation of Multiplicity, and Residue Duality*
(`docs/surcomplex/finite-deformations`), which defines it by the same
alternating series with the same sign, the same `(2πi)^{-n}`, the same ordered
tuple and the same orientation, and which says emphatically that the series *is*
the definition and that supplying a representing contour is a separate question
left to this report. That is the whole point of every contour theorem here: they
earn their value by computing that independently defined functional. Where 05
lifts the ordinary root cover, that report's support-preserving lift with
unchanged monodromy is **cited, not rebuilt** — and §13.9 records the
difference, since 05 deliberately *kills* the finite radial monodromy, before
any Hahn substitution, in order to get one fixed cover.

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
| `K[[z]]`, `C[[z]]((t^Γ))` | **formal**, no convergence | injectivity of rescaling; the formal residue class `K((u))du / dK((u)) ≅ K`; `thm 13.10`, the formal-coefficient contour theorem |

One variant of the first row is used in §§12–13 and is **not** a fifth ring but
the same requirement on a larger base: `H(X) = O(X)((t^Γ))` for one fixed
ordinary complex *manifold* `X`, possibly disconnected, where `X` is a finite
covering of a polyannulus. No theorem stated over `H(U)` for an ordinary open
`U ⊆ C` is transferred to it.

The witness `H(z) = Σ_{j≥1} t^j/(1 − jz)` for strictness of the radius-free
inclusion is stated once and reused — as a *numerator* in §10 and, by `ex 13.14`,
as a *perturbation* in §13.7.

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

From 05, all nine of its own non-claims, preserved in Appendix C:

- **Hypotheses.** An isolated *convergent* ordinary leading map and a
  positive-support perturbation are required. Arbitrary Hahn tuples with no such
  leading map, and non-isolated leading zeros, are out of scope. Extending to a
  **formal** isolated leading map is a *different* open problem: the proof needs
  a bounded analytic finite covering built before any Hahn substitution.
  `thm 13.10` removes convergence only from `E` and `H`.
- **Independence.** Period independence is proved; **no canonical
  choice-independent contour is produced.** The parameter space may be
  disconnected, and it is not claimed that every admissible cycle is homologous
  to the chosen one. Chain-level homology comparison is listed as open.
- **The adapted cycle.** It gives `μ` distinct *regular* points over each
  protected target point, but does **not** assert that every zero of `F` is
  simple or that the deformed zero algebra is reduced — and **its image is not
  identified with the entire class of surcomplex solutions of
  `|F_j| = t^{κ_j ρ}`.** No such identification is needed for any integral
  proved.
- **Descent, not duality.** `Res_F` descends nonzero to `A_n/(F)`; a
  perfect-pairing or flatness theorem is **not** inferred from it. And
  `Res_F(J_F) = μ` is deliberately **not** called conservation of local algebra
  length, which would additionally require the finite-flatness identification.
- **No fine topology.** The Hahn parameterizations are not asserted continuous
  for the fine surreal topology, and the homotopy is not a fine-topological
  homotopy; its parameter is an ordinary real one. All supports, covers and
  parameter manifolds are set-sized.
- **Effectivity, refused explicitly.** A finite coefficient dependency set gives
  **no** decision procedure for membership in an arbitrary well-ordered subset
  of a general ordered group; no uniform complexity bound is claimed; arbitrary
  convergent germs need not have finite effective descriptions; and the scale
  estimates are transparent but can be far from sharp — in the six-sheeted
  example the uniqueness ball `v(Υ) > 13/40` is much larger than the actual
  correction, which attains `36/40`.
- **The 632 symbolic checks are finite examples only.** They do not verify
  arbitrary-support Hahn summability, parameterized removable singularities, the
  rooted-tree construction, or novelty. The source README and the recorded JSON
  both say so.
- **Not identified with Müller–Strohmaier.** Their Hahn-meromorphic category is
  explicitly *not* identified with the coefficientwise ring `A_n` of radius-free
  germs, and no comparison theorem between them is asserted.
- **Search, not priority.** The targeted search of 21 September 2026 located no
  published theorem with the arbitrary-support, radius-free,
  uniform-protecting-cycle hypotheses proved here. **That is not a priority
  certification.** The publisher endpoint for the Neumann reference could not be
  fetched during that search; its details were corroborated indirectly.

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
**87 pages, 0 errors, 0 undefined references, 0 undefined citations, 0
multiply-defined labels, 0 duplicate destinations, 0 overfull or underfull
boxes**.

## The verification scripts

One verification script per source archive is kept under [`code/`](code/), with
its recorded run under [`data/`](data/), each named after its archive — plus a
Wolfram Language companion for 02 and the `build.sh` delivered with 05. They are
preserved as delivered and are not run by the LaTeX build.

`05-untransformed-leray-cycles-checks.py` needs Python 3.10+ and SymPy, and its
recorded run — 632 exact checks, SymPy 1.14.0, exact arithmetic over `Q(t)` with
no floating point — is in
[`data/05-untransformed-leray-cycles-checks.json`](data/05-untransformed-leray-cycles-checks.json),
with the eight category counts (`binomial_jets` 180, `monomial_residues` 225,
`ideal_annihilation` 200, `entire_numerator` 9, `quotient` 7,
`target_equations` 5, `displacement` 4, `normalization` 2). To reproduce it,
**pass an explicit `--output` path outside this directory**:

```sh
python code/05-untransformed-leray-cycles-checks.py --output /tmp/checks.json
```

The script's `--output` default is the *relative* path `data/checks.json`, and
the archive's own `build.sh` changed into the script's directory first, so
running it without that flag writes a stray `data/checks.json` here rather than
updating the recorded run. Nothing under [`sources/`](sources/),
[`code/`](code/) or [`data/`](data/) is modified by a rebuild of the article, and
nothing there was modified when 05 was merged in.

Its matrix route is deliberately **independent** of the contour derivation: with
`M_x, M_y` the multiplication matrices on the basis `1, y, y², x, xy, xy²` of
`C[x,y]/(x²+t, y³−2t)` over `Q(t)`, the trace
`tr(M_x^a M_y^b (12 M_x M_y²)^{-1})` is compared against the closed-form
monomial residue on a 15×15 grid, which tests the determinant factor and all six
sheets at once. `rem 13.13` in the article states plainly that this proves
nothing general.
