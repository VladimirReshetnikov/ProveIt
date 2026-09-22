# Sharp Moment Reconstruction at Surreal Scales

**Collision geometry, optimal precision, and Hahn-supported inversion**
Single-source research report, 22 September 2026, built from one manuscript
(number 13 of batch 18) whose repository comparison is pinned at `4cf691c`.
An AI-assisted draft (the manuscript was prepared with ChatGPT), not refereed.
The [Lean ledger](../../FORMALIZATION.md) records proved Prony uniqueness,
cofactor orthogonality, the exact last-moment annihilator and algebraic
local-root identities in
[PronyHankel.lean](../../../Surreal/Algebra/PronyHankel.lean).
Valuation localization and the remaining precision estimates are pending.

```
article.tex   the report, standalone LaTeX with an internal bibliography
article.pdf   the compiled report, 26 pages
README.md     this guide
code/         verify.py, the exact finite SymPy checks (unmodified)
data/         verification.txt       the recorded run of code/verify.py
              build_summary.txt      the source package's own build record
              requirements.txt       the tested SymPy version
```

Every label in `article.tex` carries the prefix `prony:` (75 labels: the
manuscript's 69, all kept, and 6 added on placement).

## Why the directory says "Prony"

"Moment" means three different things in this collection, and this report
fixes its own meaning once (Section 1.4):

- **here**, a moment is one of the finitely many power moments
  `m_k = Σ w_i a_i^k`, `0 ≤ k < 2n`, of a finite weighted configuration with
  arbitrary nonzero weights. That vector is the input of reconstruction; no
  measure and no positivity is involved;
- in [`surreal/hahn-valued-measures-and-probability`](../../surreal/hahn-valued-measures-and-probability/),
  power moments of Hahn-valued measures and moment functionals, including
  infinite moment sequences and their representation problem;
- in [`surcomplex/hahn-herglotz-positivity`](../hahn-herglotz-positivity/),
  Fourier (trigonometric) moments on the circle, tested by Toeplitz matrices.

Unit-weight power sums of roots are also called moments in
[`surcomplex/analysis`](../analysis/) (the contour moments of `d:thm:moments`).
The directory is therefore named after Prony, and the manuscript's title is
kept.

## Provenance

One manuscript, delivered as the archive `surcomplex_moment_reconstruction`
with its article, verification program, recorded run and build summary. This
is **not a merge**: no other manuscript of the batch proves its main results,
and the nearest material is cross-referenced (below), not merged. The
statements, proofs, limitations and priority caveats are the manuscript's.
What changed on placement:

- **Labels** received the prefix `prony:`; none was dropped.
- **Notation** now follows `surcomplex/polynomial-algebra`, so that the
  comparison with its stability theorem reads directly:

  | Here | Manuscript (and `verify.py`) | Meaning |
  |---|---|---|
  | `d_ij` | `s_ij` | `v(a_i − a_j)` |
  | `δ_i` | `r_i` (`r`) | `max_{j≠i} d_ij`, as in polynomial-algebra |
  | `ϖ_i` | `α_i` (`alpha`) | `v(w_i)`; `α_i` are roots in polynomial-algebra |
  | `χ_i` | `h_i` (`hi`) | `ℓ_i'(a_i) = Σ_{j≠i} 1/(a_i − a_j)`; `h = t^s` in the examples |

  `d_i` and `Θ` keep their names. `Θ` is a value-group threshold, unrelated
  to the theta series of `hahn-tate-uniformization`.
- **Added:** Section 1.4 ("This report in the collection": provenance,
  notation, the meaning of "moment", neighbours); Section 6.2 with
  Remark 6.2 (the comparison with the coefficient threshold); a note after
  Proposition 3.1 on the Hankel identity; two rows of the ledger in
  Appendix A; five bibliography entries for collection reports; a two-sentence
  closing paragraph of the abstract pointing to Section 1.4.
- **Stale repository statements corrected, with the pin kept as provenance.**
  At `4cf691c` searches for "Prony" and "Hankel" found nothing, `docs/new`
  held eighteen ZIPs and `docs/README.md` listed twenty-six reports. The
  report now says so as statements about the pin, and records that the
  collection has since gained the Hankel and Prony-type material below and
  that the archives then in `docs/new` (and this manuscript's own archive)
  have been placed into reports (Sections 1.3, 1.4 and Appendix B). "The package
  contains" became "this directory contains"; "no repository file was
  modified" became "the manuscript modified no repository file". The Lean
  paragraph (Section 10.3) now names the ledger entries it relies on: the Hermite and
  Lagrange interpolation clauses of `polynomial:thm:crt` in
  `docs/FORMALIZATION.md`.
- `code/verify.py` and the three files in `data/` are byte-identical to the
  delivery. The delivered member README, checksum manifest and PDF are not
  shipped; the manifest was verified when the batch was placed.

## What the report claims

Let `K = k((t^Γ))` with `k = R` or `C` and `Γ` **any nontrivial ordered
abelian group** (not assumed divisible). The nodes `a_i` are distinct and
integral, the weights `w_i` nonzero, of any valuation, possibly negative. Put
`d_i = Σ_{j≠i} d_ij`, `δ_i = max_{j≠i} d_ij`, `ϖ_i = v(w_i)`,
`E_i = ϖ_i + 2d_i` and `Θ = max_i (E_i + δ_i)`.

- **Theorem 1.1 (`prony:thm:main`), optimal uniform reconstruction.** If all
  `2n` moment errors have valuation at least `κ > Θ`, there is a unique regular
  `n`-node realization, uniquely labelled by the strict nearest-neighbour balls
  `v(â_i − a_i) > δ_i`, with node errors of valuation at least `κ − E_i` and
  weight errors of valuation at least `κ − 2d_i − δ_i > ϖ_i`. Perturbing only
  `m_{2n−1}` attains every node bound at once; at valuation exactly `Θ` that
  perturbation leaves no realization with the strict-ball labelling, for
  **every** configuration.
- **Proposition 6.1 (`prony:prop:last`).** The last-moment annihilator
  `P_e = P − e Σ Q_i/(w_i P'(a_i)²)` is exact for every `e`.
- **The machinery:** the exact cofactor correction system
  (Lemma 3.2), cofactor localization (Lemma 4.1), the finite Padé and
  cross-numerator identities and the weight estimate (Lemmas 5.1–5.3), and
  preservation of reality, positivity and node order (Corollary 5.4).
- **Hermite precision.** Proposition 7.1 gives the exact Gauss valuations of
  the inverse Hermite rows, `−2d_i` and `−2d_i − q_i`, with a cancellation
  depth `q_i` that the separation tree does not determine (Section 9.3).
  Proposition 7.2 is a support-based arbitrary-rank form of the
  Caruso–Roe–Vaccon precision-lattice principle; Corollary 7.3 gives the exact
  nonlinear uncertainty set under an extra finite criterion; Proposition 9.1
  shows that for `(−h, 0, h)` the improved weight bound fails nonlinearly when
  `5s < κ < 6s`.
- **Theorem 8.1 (`prony:thm:graph`).** A directed-path sufficient certificate
  for nonuniform moment precisions, now valid for **nondivisible `Γ`** as
  well. The proof uses auxiliary fractional exponents and returns the
  reconstruction in the original Hahn field. Divisibility still guarantees
  the nonempty interval discussed in Proposition 9.1.
- **Corollary 2.3.** Everything transfers to finite configurations in `No` and
  `No[i]` through set-sized Hahn workspaces.
- Worked examples (Section 9): one atom; two nodes with an actual boundary
  collision at `c = i/2` and, for real `c`, a positive real realization that
  loses its labels; a rank-two lexicographic configuration with
  `Θ = 3e_1 + 3e_2`; nonuniform errors for two nodes.

## Relation to the coefficient threshold of polynomial-algebra

Theorem 1.1 is the moment-input analogue of `polynomial:thm:stability` in
[`surcomplex/polynomial-algebra`](../polynomial-algebra/), whose threshold for
coefficient perturbations is `T(P) = max_i (d_i + δ_i)`. Remark 6.2 states the
relation (an editorial comparison added on placement; no new theorem):

- `Θ = max_i ((ϖ_i + d_i) + (d_i + δ_i))`. The extra summand
  `ϖ_i + d_i = v(w_i P'(a_i))` is the cost of passing from moments to the
  annihilator; with it, polynomial-algebra's displacement bound `ε − d_i`
  becomes the node bound `κ − E_i`. If every `ϖ_i ≥ 0` then `Θ ≥ T(P)`;
  weights of negative valuation can make `Θ` smaller.
- Lemma 4.1 is a nodewise form of the matching step of that theorem: its
  hypothesis is implied by `ε > T(P)`, not conversely (nodes `0, t^s, 1`).
- Theorem 1.1 does not follow merely by composing Lemma 3.2 with
  `polynomial:thm:stability`: for two unit-weight nodes at separation `s`,
  the last-moment perturbation with `3s < κ ≤ 4s` is covered here but not
  there.
- `polynomial:ex:sharpdisc` proves strictness for one family; Theorem 1.1
  proves boundary failure at every configuration. No coefficient-side analogue
  of the latter is claimed.

## What the report does not claim

All of the manuscript's limitations are kept in the article, chiefly in
Sections 1, 2, 7, 8, 9, 10 and 11 and Appendices A–B:

1. **Classical material is credited, not claimed.** Classical Prony
   reconstruction, Hermite interpolation, and differential precision tracking
   are explicitly separated from the proposed refinements. Batenkov–Yomdin and
   Katz–Diab–Batenkov already have the `w_i P'(a_i)²` denominator;
   Akinshin–Goldman–Yomdin already have the last-moment (Prony-curve)
   direction; precision lattices are Caruso–Roe–Vaccon's.
2. **Priority is not certified.** No named published conjecture is claimed
   solved, and the further questions of Section 11 are research directions,
   not known open problems. Partial Lean coverage is stated above; the full
   precision theorems are not formalized.
3. The threshold is optimal for the **strict-ball labelling guarantee**, not
   for the bare existence of some realization; failure at the threshold need
   not be a collision or a loss of positivity.
4. The `q_i`-improved weight bound holds for the tangent map, and for the
   whole nonlinear set only under the extra finite criterion, which is not
   claimed optimal; Proposition 9.1 shows the improvement can fail.
5. Theorem 8.1 is a **sufficient** certificate only, not the exact admissible
   precision region.
6. The reconstruction is a mathematical construction, **not an unconditional
   Turing algorithm** on surreal inputs, and its support control is relative:
   the output is not claimed to use only the supports of the raw moment
   errors.
7. Confluent configurations, infinite configurations, and uniqueness beyond
   the fixed `n`-node model are out of scope.
8. The surreal transfer concerns finite algebraic data: not integration, a
   global surreal exponential, or paths in the fine topology; strong Hahn
   summability is not convergence of partial sums.
9. The finite checks do not prove the general theorems, arbitrary Hahn
   support or rank, the class/universe claims, or novelty.
10. The repository and literature audits were targeted; negative searches are
    observations, not proofs of absence.
11. The comparison added on placement (Remark 6.2) proves no new theorem and
    claims no coefficient-side universal sharpness.

## Relation to the neighbouring reports

- **[`surcomplex/polynomial-algebra`](../polynomial-algebra/)**: the
  coefficient-input antecedent, above. Its finite Hermite jets
  (`polynomial:thm:crt`), factor lifting and root-cluster geometry are
  antecedents, not contributions of this report.
- **[`surcomplex/spectral-theory`](../spectral-theory/)**, its section on
  Hankel square-class profiles (from another manuscript of batch 18). The
  **common classical input is the identity** that the Hankel matrix
  `H = V diag(w) Vᵀ` of Proposition 3.1 is, with unit weights, the Hankel
  matrix of Newton power sums (the trace form), with `det H = Disc P`. That
  section studies square classes modulo `2Γ` of leading principal minors over
  nondivisible `Γ`; this report studies valuation thresholds for weighted
  moments. Their further theorems address different questions, and neither
  proof depends on the other report.
- **[`surreal/hahn-valued-measures-and-probability`](../../surreal/hahn-valued-measures-and-probability/)**
  contains, from another manuscript of batch 18, a Prony-type lemma on finite
  signed exponential sums and finite Gaussian quadrature over real closed
  fields: the signed-sequence lemma requires real roots but no positivity;
  Gaussian quadrature requires positivity. This report
  studies stability of an `n`-node reconstruction and uses no measure.
  Cross-referenced, not merged.
- **[`surcomplex/hahn-herglotz-positivity`](../hahn-herglotz-positivity/)** and
  **[`surcomplex/analysis`](../analysis/)** use "moment" in other senses
  (above).

## Build and reproduce

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The reviewed build gives 27 pages with zero errors, zero LaTeX or package
warnings, zero undefined references or citations, zero multiply defined
labels and no overfull or underfull boxes. `data/build_summary.txt` is the
source package's own record and reports 22 pages: that is the manuscript
before the placement additions.

**Run the checks on a copy of this directory.** `code/verify.py` deletes
`data/verification.txt` when it starts and rewrites it at the end, with the
Python and SymPy versions on its second line; if an assertion fails, the old
record is already gone and no new one is written.

```sh
cp -r prony-reconstruction-at-surreal-scales /tmp/prony-copy
cd /tmp/prony-copy
python -m pip install -r data/requirements.txt
python code/verify.py
```

The recorded run passed **10,052 exact assertions** under Python 3.13.5 and
SymPy 1.14.0. On placement, a run on a copy under Python 3.14.4 and SymPy
1.14.0 reproduced every line except the version line (on Windows the rewritten
file also has CRLF line endings). The count includes finite graph-walk
enumeration and is not a count of theorems. The checks use exact symbolic and
rational arithmetic, no floating point and no network. They cover Hermite
duality and the Hankel determinant, the cofactor, Padé and cross-numerator
identities, the two-node formulas and boundary collision, the three-node
cancellation comparison and nonlinear obstruction, the rank-two threshold
arithmetic, and a directed-graph certificate. Compiling the article does not
run them.

## Subsequent proof review

The nonuniform graph theorem no longer requires a divisible value group.
Its scaling potentials are chosen in the ordered divisible hull; the
adjugate inverse and unscaled Hahn expansion descend to the original field,
where residue-simple lifting produces the nodes. A two-vertex integer-weight
example explains why auxiliary fractional potentials may be necessary.

The classical uniqueness proposition now explicitly includes arbitrary
`n`-node representations, which the invertible Hankel matrix forces to be
regular, and rules out fewer nodes using only the first `2n−1` moments.
These clauses are already covered by the Lean ledger. The report also
specifies `n ≥ 1`, corrects the collision terminology, and restores the
real-root and positivity distinctions in the measure-report comparison.

The cited precision-lattice antecedent was checked against
[Caruso–Roe–Vaccon v1](https://arxiv.org/abs/1402.7142v1), Lemma 3.4 and
Proposition 3.12. Its normed-space hypotheses are now explicit; the Hahn
proof remains independent of that theorem. Other literature comparisons,
priority and original-source reconciliation remain outside this review.

The reviewed article and catalogue rebuild without warnings or box issues at
27 and 21 pages. The unchanged program was rerun on a temporary copy under
Python 3.13.14 and SymPy 1.14.0: all 10,052 assertions pass, and every output
line matches the delivered record except the version line. Historical code
and data are unchanged.
