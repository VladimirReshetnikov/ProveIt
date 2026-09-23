# Tail-spans and differential transcendence in surreal and surcomplex Hahn fields

`article.pdf` (26 pages) — source `article.tex`, checks in `code/`, recorded
output in `data/`, scope limits in `AUDIT.md`.

An unrefereed AI-assisted draft, prepared 22 September 2026. The
[Lean ledger](../../FORMALIZATION.md) records proofs of cofinite-span
stabilization and multilinear detection in
[TailSpan.lean](../../../Surreal/Algebra/TailSpan.lean). The classification
and differential-independence theorems remain pending. The proofs are complete
*relative to* standard Hahn-field, Galois,
Conway-normal-form and Berarducci–Mantova foundations, which are cited rather
than rebuilt.

All labels in `article.tex` carry the `tail:` prefix.

## What it establishes

The organizing invariant is the **cofinite span**. Let `M` have characteristic
zero, let `(a_i)` in `M^×` have independent square classes with `r_i² = a_i`,
let the exponents `γ_i` be distinct with well-ordered image, and let the
coefficient vectors `v_i` lie in `M^r`. For

    Y = Σ_i t^{γ_i} r_i v_i ,   B = M((t^Γ)) ,
    W = ∩_{F finite} span_M { v_i : i ∉ F }

the exceptional set `E = { i : v_i ∉ W }` is finite and, with `d = dim_M W`
and `B_E = M(r_i : i ∈ E)((t^Γ))`,

    B[Y_1, …, Y_r] = B_E[s_1, …, s_d]   with s_1, …, s_d
                                        algebraically independent over B_E,
    trdeg_B B(Y_1, …, Y_r) = d,   [B_E : B] = 2^{|E|}.

That is `tail:thm:tail`, an equality of subrings inside a named ambient Hahn
field, not a comparison of dimensions. `tail:thm:planes` then decomposes the
whole relation ideal after its finite splitting extension into `2^{|E|}`
pairwise comaximal affine planes of dimension `d`.

The mechanism is elementary and finitary: a degree-`D` relation is destroyed by
finitely many coefficient sign changes. Their alternating sum is a `D`-fold
mixed difference, which by `tail:lem:difference` equals `D!` times the top
polarization; cofinite spanning (`tail:lem:multilinear`) then forces that
polarization to vanish identically. No limiting argument and no infinite
sequence of Galois operations is used.

**Actual surreal numbers (`tail:sec:surreal`).** With `t = ω^{-1}`,
`B_0 = Q((t^Q))` and `H_0 = A_R((t^Q))` as concrete subfields of **No**, and
`ξ_A = Σ_{n∈A} √p_n ω^{-n}`:

- `tail:thm:onesurreal` — for **every** infinite `A ⊆ N_{>0}`, the whole jet
  family `{ ∂_BM^k ξ_A : k ≥ 0 }` is algebraically independent over `B_0`.
- `tail:thm:surreal` — for the binary-prefix almost disjoint family
  `(A_α)_{α ∈ {0,1}^N}`, the combined family
  `{ ∂_BM^k ξ_α : α, k }` is algebraically independent over `B_0`, so
  `dtrdeg_{B_0} H_0 = trdeg_{B_0} H_0 = 2^{ℵ_0}`, and the free differential
  polynomial algebra on `2^{ℵ_0}` generators embeds in `H_0`.

The witnesses are actual positive infinitesimal surreal numbers with
real-algebraic coefficients and positive integer valuation support, not formal
objects awaiting an interpretation.

**Surcomplex analytic functions (`tail:sec:analyticsetup` onward).** For
`F_A(z,t) = Σ_{n∈A} t^n √(1 − z/2^n)` with the branch equal to `1` at `z = 0`:

- `tail:thm:mixed` — for **every** infinite `A`, all mixed jets
  `∂_z^j δ^k F_A` (with `δ = t d/dt`) are algebraically independent over
  `C(z)((t^Q))`. This excludes every algebraic partial differential equation of
  every finite order over that field, not only linear or autonomous ones.
- `tail:thm:continuumanalytic` — continuum many such functions are jointly
  independent, all on the **one** fixed disk `|z| < 1`, with no shrinking as the
  parameter varies.

`tail:thm:closure` gives an exact valuation-approximation criterion, and shows
that `Σ √p_n t^n` is a valuation limit of algebraic truncations when `Γ = Q` but
not after `Γ` is enlarged to lexicographic `Q²` via `q ↦ (0,q)` — the same
surreal expansion, a different answer, because the available precision scales changed.
`tail:prop:undecidable` shows algebraicity and differential algebraicity are
undecidable for unrestricted total computable coefficient streams, while
`tail:cor:finitewitness` gives the bounded-degree finite certificate that does
exist.

## Two places where this report meets its companions

**It cites rather than reproves the Berarducci–Mantova restriction.** The
rational-exponent workspace and the formula `∂(Σ c_q t^q) = Σ (−q) c_q t^{q+1}`
belong to [`surcomplex/differential-equations`](../../surcomplex/differential-equations/):
its `diff:eq:HahnQ` fixes the workspace and its `diff:prop:hahnderiv`
(equation `diff:eq:hahnderiv`) proves the formula. `tail:sec:surreal` cites both
and checks only the one extra step it needs — that restricting from real to
real-algebraic coefficients keeps the subfield stable, since the formula
multiplies each coefficient by a rational and shifts its exponent by one. That
report's `diff:warn:monomialmap`, separating the Conway monomial map from
general surreal exponentiation, still applies; nothing here differentiates a
monomial at a non-real exponent. `diff:rem:tailspans` in that report points back
here.

**It supplies an upgrade a companion warning explicitly declines.**
[`surcomplex/dynamics-and-normal-forms`](../../surcomplex/dynamics-and-normal-forms/)
proves its solutions `H_ε` transcendental over `B = C(w)((t^Γ))` for
`deg V ≥ 2`, and its warning `dyn:warn:diffalg` refuses to upgrade that to
*differentially* transcendental, because its own `H_ε` satisfies the first-order
linear equation `H_ε' = Ω_ε H_ε` with `Ω_ε ∈ B`. **That warning stands and is
not weakened here.** It is true of `H_ε`, and nothing in this report bears on
`H_ε`. What `tail:thm:mixed` shows is that the refusal is about that function
and not about the workspace: different, explicit functions over the `Γ = Q` case
of a base of the same shape, on one fixed disk with no shrinking, do satisfy no
algebraic differential equation of any finite order. `tail:rem:dynupgrade` here
and the added paragraph in `dyn:warn:diffalg` there state the relation from both
sides.

Since then, Part V of [differential-equations](../../surcomplex/differential-equations/)
writes this report's Euler derivation as `∂_τ` (`diff:rs:lem:euler`), and its
Part VI proves algebraic independence of differentially algebraic solutions
(`diff:aut:cor:independent`). That is a different notion from the maximal
differential transcendence degree here (`tail:eq:maxdtrdeg`); neither result
bears on the other.

Two later reports sit beside this one without depending on it.
[transcendence-over-bounded-support](../transcendence-over-bounded-support/)
(`bst:sec:collection`) proves independence over the fraction field of
bounded-support series, from support rather than coefficients; its
integer-coefficient witnesses lie in `B_0`, and its family over all subsets is
independent. [hidden-negative-hermitian-directions](../../surcomplex/hidden-negative-hermitian-directions/)
uses prime-denominator tails as the exponent-side counterpart over a
finite-lattice-supported base (`hnd:thm:independence`); for `Γ = Q` the two
bases do not contain each other.

The holonomic-rigidity report now proves all-order differential transcendence
of every nonpolynomial strongly entire series when the value group has no
order unit, and a continuum-sized differentially independent family
(`hol:cf:thm:continuum`). Nothing transfers between those derivations and this
report's.

## What was checked when this was fitted into the collection

The headline claim — `dtrdeg_{B_0} H_0 = 2^{ℵ_0}` with the explicit `ξ_α` —
was re-derived rather than taken on trust, and it holds as stated. Two things
are worth recording.

- **The witnesses are pairwise, indeed jointly, independent, but the index
  family is not arbitrary.** For finitely many distinct `α`, each `A_α` has
  infinitely many indices in no other member, so the combined coefficient
  vectors have full cofinite span and `E = ∅`. Almost disjointness is doing
  real work: the family `(ξ_A)` indexed by **all** `A ⊆ N_{>0}` is *not*
  independent, since `1_{A∪B} + 1_{A∩B} = 1_A + 1_B` gives the `Q`-linear
  relation `ξ_{A∪B} + ξ_{A∩B} = ξ_A + ξ_B`. `tail:rem:indexfamily` was added to
  say this in the article.
- **The cardinality argument does not assume what it proves.** The lower bound
  is the construction; the upper bound is a separate count that uses only the
  countability of `A_R` and `Q` — a Hahn series in `H_0` is a function
  `Q → A_R`, so `|H_0| ≤ ℵ_0^{ℵ_0} = 2^{ℵ_0}` — and a transcendence degree is
  bounded by the cardinality of the field. The proof's closing sentence
  previously attributed the upper bound to the independent family; it was
  rewritten to attribute each bound to its actual source. No claim changed.

The triangular relation `tail:eq:BMtriangular`,
`∂_BM^k = (−1)^k t^k δ(δ+1)⋯(δ+k−1)`, was checked by induction; it is what
transfers Euler-jet independence to `∂_BM`-jet independence, and it is
invertible over `B_0` because its leading coefficient `(−1)^k t^k` is a unit
there.

## What it does NOT claim

- **Proposed contributions, not certified priority.** A targeted literature
  search did not identify these formulations. No exhaustive MathSciNet or
  Zentralblatt audit, and no full citation-network audit, was performed. No
  named historical open problem is claimed solved.
- **Not refereed; partial Lean coverage.** The two cofinite-span lemmas are
  formalized as recorded above; this does not verify the main classification
  or the infinite differential-independence constructions.
- **The coefficient sign changes are not order-preserving.** They act on a
  multiquadratic intermediate field and its Hahn field only. They are *not*
  asserted to extend to all real-algebraic numbers, or to an automorphism of
  **No**. `tail:rem:noorder` says so; the proofs need no such extension.
- **"Cofinite span" means intersection over finite deletions**, not deletion of
  an arbitrary transfinite initial segment of an ordered support.
- **The hypotheses are load-bearing.** Characteristic zero, finite-dimensional
  coefficient vectors, independent square classes, and distinct well-ordered
  exponent indices are all used. Dropping any of them needs a new argument.
- **`C(z)((t^Q))` is not a ring of functions on a common domain.** Its elements
  can have coefficient poles approaching `0`. `L((t^Q))` and `O(D)((t^Q))` are
  both embedded in the meromorphic-germ Hahn field `M_0((t^Q))`; **neither is
  asserted to contain the other**. The constructed functions lie in the
  intersection.
- **Analytic independence is not asserted to survive point evaluation.** At
  `z = 0` the full-series Taylor jets are rational functions of `t`; at any
  ordinary `z_0 ∈ D` the values lie in `C((t^Q))` itself. Unlike the actual
  numbers of `tail:sec:surreal`, those point values are not claimed
  transcendental.
- **The formal Taylor series in `z` is not an admissible Hahn sum** over Taylor
  order at an ordinary nonzero complex `z`: infinitely many terms contribute at
  `t^1` (`tail:warn:taylor`). Halo substitution has its own joint-support
  certificate (`tail:prop:halo`) and is not a fine-topology convergence claim,
  nor a claim that `F_A` is defined at every infinite surcomplex argument.
- **The two analytic derivations are not automatically Berarducci–Mantova
  differentiation** after arbitrary surreal substitutions. Specializing `z` to a
  nonconstant surreal expression can introduce a chain-rule term. The analytic
  theorems are stated before such substitutions; the actual-number result is
  proved separately and directly.
- **A dilation identity is not a differential equation.** `F` satisfies
  `F(2z,t) − tF(z,t) = t√(1−z)` exactly, and is still differentially
  transcendental. Nothing here excludes functional equations in shifted or
  dilated arguments.
- **Continuum cardinality is not a basis claim.** The independent families are
  not asserted to be transcendence or differential transcendence bases, and
  cardinal maximality is not maximality under inclusion.
- **Valuation closure is relative to a specified set-sized value group.** It is
  not the fine topology of the proper class `No[i]`, and Hahn summability is not
  valuation convergence of finite truncations in an arbitrary-rank field.
- **Set-sized throughout.** `2^{ℵ_0}` is a cardinal statement about named
  set-sized subfields of **No**, not an appeal to the proper-class size of the
  surreals.

## Build

MiKTeX or TeX Live with the AMS packages plus New PX text/math, `geometry`,
`microtype`, `fancyhdr`, `titlesec`, `needspace`, `enumitem`, `booktabs`,
`tabularx`, `longtable`, `xcolor` and `hyperref`. The bibliography is internal:
no BibTeX, no shell escape, no external image, no network access. The source
uses installed TeX fonts; no font files are distributed here.

```sh
pdflatex -interaction=nonstopmode -halt-on-error article.tex   # three times
```

from the report directory. The delivered `code/build.py` does the same, but it
looks for `article.tex` beside itself, as in the delivered package; to use it,
copy the directory and move `build.py` next to `article.tex` in the copy. Last verified build: exit 0, **26 pages**, no
LaTeX warnings, no undefined references, zero overfull or underfull boxes.

`code/build.py` is kept byte-identical to the delivery. An earlier edit that
made it look one directory up has been undone, because delivered code is not
modified in this collection.

## Rerun the checks

Python 3.10 or later; the recorded run used Python 3.13.5 with SymPy 1.14.0.

```sh
python -m pip install -r data/requirements.txt
python code/verify.py --output /tmp/tail-review-results.json
```

Use a scratch output path to preserve the delivered record.

Deterministic seed `20260922`. The checks use exact integers, rationals,
polynomial identities and exact symbolic differentiation; they do **not**
numerically approximate infinite surreal sums. Last run here: **404 checks,
all passed**.

**404 is a check count, not a count of independently proved theorems**, and
some checks exercise different aspects of one small example. The record is not
a proof of any arbitrary-support theorem, of any hereditary statement about all
infinite subsets, or of any continuum-sized independence statement. A finite
rank calculation does not prove `tail:lem:jetspan`; finite sign-orbit examples
do not prove `tail:thm:tail`. Those are proved in the article, by the pole
argument with `tail:lem:expgraph` and by the Galois-action, finite-difference
and cofinite-spanning argument respectively.

`data/layout_audit.json` records page-boundary measurements of the **originally
delivered** 23-page PDF, before the editorial changes described above. It does
not describe the 26-page `article.pdf` in this directory.

## Provenance

The article's own targeted documentation audit used revision
`608dd23c0539fce73723843949ee627641c27b30` of `VladimirReshetnikov/Surreal`,
and does not claim coverage of that repository's full archive or of its Lean
formalization.

Unlike the source package, this one **does** change two other reports in the
collection: the pointer paragraph added to `dyn:warn:diffalg` in
`surcomplex/dynamics-and-normal-forms`, and `diff:rem:tailspans` plus its
bibliography entry in `surcomplex/differential-equations`. Both additions are
additive. No existing `\label` in either file was renamed or removed, and both
still build with no new LaTeX warnings.

`AUDIT.md` carries the full mathematical, bibliographic and verification
limitations, including the proof-checkpoint reading order and the per-category
check inventory.

## Subsequent proof review

The sign-change lemma now states its characteristic-not-two hypothesis, and
the polarization and orbit arguments state characteristic zero explicitly.
A counterexample in `F₂(u,v)` shows why the sign lemma needs its restriction.
The mixed-difference proof uses the finite polynomial Taylor identity, so it
also covers zero directions and a vanishing top directional derivative.
The exceptional-field proof constructs a separating functional explicitly and
explains coordinate recovery; the affine-plane proof derives its Galois
splitting from the primitive element and the Chinese remainder theorem.

The approximation example now uses lexicographic `Q²`, with `q ↦ (0,q)`,
so it really enlarges the original rational value group. The former `Z²`
example was a valid comparison of two workspaces, but did not contain the
original `Q`-workspace. The same surreal series fails approximation by
**any** algebraic element in the enlarged workspace at threshold `(1,0)`.

The extension-of-embeddings citation was checked against
[Stacks, Lemma 9.15.7(2)](https://stacks.math.columbia.edu/tag/0BME);
the former tag pointed to the finite fundamental theorem instead.
The BM restriction was checked against the cited companion proposition.
Other foundational imports, literature comparisons and original-source
reconciliation remain outside this review.

The unchanged verification program passed all 404 checks on a temporary copy
under Python 3.13.14 and SymPy 1.14.0. Every check record matches the delivered
output; only the Python version and elapsed time differ. The article and
catalogue were rebuilt in three passes, with no warnings or box issues.
Historical code, data and the delivered audit were preserved.
