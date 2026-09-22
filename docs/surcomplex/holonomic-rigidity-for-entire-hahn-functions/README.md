# Holonomic Rigidity for Entire Hahn Functions

**A sharp order-unit criterion for dilations, with uniform exclusion bounds**
Merged research report, 22 September 2026, from two manuscripts written
independently on the same day.

```
article.tex   the report, standalone LaTeX with an internal bibliography
article.pdf   the compiled report, 40 pages
README.md     this guide
08-finite-recurrences-PROOF_AUDIT.md          source 08: assumptions and critical proof steps
08-finite-recurrences-SOURCES_AND_SCOPE.md    source 08: sources, repository pin, priority limits
09-entire-hahn-holonomic-literature_audit.md  source 09: literature audit
code/         08-finite-recurrences-verify.py, 09-entire-hahn-holonomic-verification.py
data/         the recorded runs and build reports of both sources
```

Every label in `article.tex` carries the prefix `hol:`. The audit files and
programs keep the source numbers `08` and `09` of the batch they arrived in.

## Why one report

Manuscripts 08 and 09 are one report written twice. Both prove the same
holonomic rigidity theorem, the same order-unit dilation criterion, the same
finite-step escape lemma, the same partial-theta sharpness witness, and the
same explicit counterexample series. **08 is the base** because it assumes only
`Γ ≠ 0`, while 09 assumes divisibility. Every proof taken from 09 was re-read
for a hidden division before it was attached to an 08 statement. Divisibility
now enters in exactly four places, and each prints the hypothesis itself
(Section 1.4):

1. the refined recurrence threshold of Corollary 3.5 (`hol:cor:periodic`),
   whose divisibility-free predecessor is Corollary 3.4 (`hol:cor:boundedcost`);
2. the refined coarsened threshold in Theorem 7.4 (`hol:thm:coarse`), which
   also states the divisibility-free form;
3. the "only if" half of the torsion eigenspace equivalence,
   Proposition 9.1(c) (`hol:prop:torsion`), which extracts an `m`th root;
4. the worked sparse threshold of Example 13.1 (`hol:ex:sparse`), an
   instance of (1).

The divisibility-free predecessors are weaker in the constant only, not in the
conclusion.

## What the report claims

Let `K = C((t^Γ))` for a nonzero set-sized ordered abelian group `Γ`, **not
assumed divisible**. *Entire* means that the evaluation family is strongly Hahn
summable at every point of this one field, not at every point of the full
surcomplex class.

- **Theorem A, differential rigidity.** Every strongly entire D-finite power
  series is a polynomial. More strongly, a fixed nonzero operator `L` has an
  exterior valuation region, computed from finitely many coefficients, on
  which strong evaluation of any formal solution already forces a polynomial
  of degree below a common bound.
- **Theorem B, the sharp dilation criterion.** For `q` of infinite
  multiplicative order, a nonpolynomial strongly entire solution of a nonzero
  linear `q`-difference equation with polynomial coefficients exists **if and
  only if** `v(q) ≠ 0` and `|v(q)|` is an order unit of `Γ`. A nonzero
  valuation is not enough in higher rank. The proof covers units whose
  residues are roots of unity. When the criterion holds, a partial theta
  series is a witness.
- **Theorem C, several variables.** A function strongly summable at every
  point of `K^d` whose mixed partial derivatives span a finite-dimensional
  space over `K(z_1, …, z_d)` is a polynomial.
- Further: mixed differential–dilation rigidity at every nonzero noncofinal
  scale (Theorem 10.2); a recurrence exclusion bound that is **attained**,
  boundary included, by a formal exponential (Proposition 5.3); a coarsened
  exclusion bound valid at every nonzero dilation valuation (Theorem 7.4); and the exact strong evaluation domain of
  the partial theta series for an arbitrary Hahn parameter (Theorem 8.1).
- In an explicit surreal workspace with countable cofinality and no order
  unit, `Σ ω^(−ω^n) z^n` is strongly entire (Theorem 11.2) yet satisfies no
  nonzero linear differential equation and no nonzero linear dilation equation for any
  nontorsion parameter of that workspace.

## What the report does not claim

- The arbitrary-rank classification is offered as a **proposed original
  contribution**. Priority is not certified, no named published conjecture is
  claimed solved, and the proofs have not been independently refereed or
  checked in Lean.
- Classical material is credited, not claimed: Stanley's D-finite/P-recursive
  correspondence, Hahn–Neumann support lemmas and Higman's lemma, partial
  theta series and their functional identity, and the Conway normal-form
  identification. Ramis, Garoufalidis and Di Vizio are named antecedents;
  their conclusions are neither inferred nor strengthened here.
- `D_z` differentiates only the formal variable and kills every scalar. It is
  **not** the Berarducci–Mantova derivation, and no theorem about that
  derivation is restated as D-finite rigidity.
- Finite-order dilations are excluded from the main dilation theorem
  (Section 9). **No nonlinear differential transcendence claim is made**; the
  nonlinear case is open (Question 15.1), and the escape proof does not extend
  to it. Mixed equations at unit valuation are also open (Question 15.2).
- The exclusion thresholds are explicit and uniform but need not be optimal.
- The finite checks validate coefficient conversions, identities, cancellation
  examples and finite ordered-group examples. They do not establish the
  infinite support arguments, the cofinality claims, the generic-line theorem,
  or the nonexistence of annihilating operators.

## Relation to the neighbouring reports

**[entire-functions-at-arbitrary-rank](../entire-functions-at-arbitrary-rank/)**
studies the same class of entire functions over the same kind of workspace.
None of its ring-theoretic conclusions is used here. This report cites its
order-unit coarsening lemma `ent:lem:coarsening` rather than repeating it, and
takes from it the background facts about countable cofinality and the group
`⊕_{j≥0} Q ω^j`. **The two order-unit dichotomies are not the same theorem.**
There, the order unit decides Hermite interpolation and the Bézout property of
the ring. Here, it decides which annihilating operators a nonpolynomial member
can satisfy. Neither implies the other.

**[differential-equations](../differential-equations/)** uses a derivation on
surreal *scalars*; this report does not. **[rank-one-berkovich](../rank-one-berkovich/)**
already contains the quadratic-exponent example `Σ t^(n²) z^n`, so the partial
theta witness is not counted as a new function.

## Build and reproduce

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The recorded build has zero errors, zero undefined references and zero
duplicate PDF destinations. Both check programs use only the Python standard
library with exact integer and rational arithmetic. Run them on a copy of this
directory. `08-finite-recurrences-verify.py` requires an explicit `--output`
path, so that a rerun cannot overwrite the delivered record. The recorded runs
passed 3,705 checks (08) and 2,043 checks (09), with no failures.
