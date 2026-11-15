# Lean completion plan: finite contours, then an actual iPRA derivation

## Current status and exact completion criterion

`FiniteCore.lean` contains complete proposed proof scripts for elementary ring
identities: oriented edge reversal, affine exactness, four-triangle internal
edge cancellation, finite geometric sums, and differences of powers. **It is an
uncompiled candidate.** No `lean`, `lake`, or `elan` executable was available in
the authoring environment. Neither this file nor the exact-arithmetic Python
checks constitute a formalization of the analytic theorems.

The full paper contains the human-readable quantitative proof. The remaining
formalization has a concrete finish line: construct derivations with target
`Γ ⊢[PRAAx] φ` in ProveIt's deeply embedded intuitionistic primitive recursive
arithmetic. A proof about ordinary Lean `Nat`, `Rat`, or `Complex`, even a
constructive one, does not establish that finish line.

The repository source inspected was pinned to ProveIt commit
`0bba41d70f061442357cae0f6de055434a33fb09`, with toolchain
`leanprover/lean4:v4.32.0`. The relevant package root is
`Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/`, namespace
`LeanProofs.ConciseIPRA`. The supplied provenance directory records the exact
source-file hashes, pinned URLs, and inspection scope. It is a provenance
manifest, not a standalone checkout of ConciseIPRA.

Use the real bridge, from `ConciseIPRA.NativeBiInterpretation`:

```lean
theorem pra_iff_native {Γ : List (Fm PTm n)} {φ : Fm PTm n} :
    (Γ ⊢[PRAAx] φ) ↔
      NPrf (Γ.map NFm.ofPRA) (NFm.ofPRA φ)
```

Once the iPRA proof exists, `pra_iff_native.mp h` produces the native scalar proof.
No theorem turning arbitrary Lean proofs into iPRA proofs is assumed.

## 1. State the theorem as an arithmetic schema

For each fixed family of primitive recursive approximation and modulus
programs, add the corresponding ordinary `PR` function symbols. Geometry,
precision, signed coefficient indices, finite lists, and rational numerators
and denominators are numerical parameters. Do not introduce unrestricted
first-order quantification over functions, a set of all real numbers, or a
universal primitive recursive evaluator of arbitrary primitive recursive code.

Use one consistent rational-complex encoding throughout:

- An integer is a signed natural code, or a pair of naturals modulo the
  explicitly proved signed-arithmetic normalization.
- A rational is an integer numerator and a strictly positive natural
  denominator. Reduction by gcd is unnecessary.
- A rational complex number is a pair of rationals.
- Its norm is `|re| + |im|`. Comparisons use positive cross-multiplication.
- A finite chain is a coded list of oriented edges with integer multiplicities.
  Vertex equality is exact rational equality, and common edges use common
  vertex codes after canonical rational normalization or a verified equality
  test.

For a fixed integrand family, use `F(q,n)` and `D(q,n)` for rational-complex value
and derivative approximations. The hypotheses are explicit first-order
arithmetic formulas, including the following clauses on valid sample points:

1. `norm(F(q,n)-F(q,N)) <= 2^(-n)+2^(-N)`.
2. If `norm(q-r) <= 2^(-nu(k))`, then
   `norm(F(q,n)-F(r,N)) <= 2^(-k)+2^(-n)+2^(-N)`.
3. If `d=norm(r-q) <= 2^(-mu(k))`, then
   `norm(F(r,n)-F(q,n)-D(q,n)*(r-q))`
   `<= 2^(-k)*d + 2^(-n)*(2+d)`.
4. When needed for products, quotients, and Laurent coefficients, explicit
   rational bounds for values and derivatives, with their approximation slack.
5. Positive rational separation from singularities and excluded holes;
   decidable finite geometric membership and boundary identities.

These hypotheses supply uniform rates; bare pointwise complex
 differentiability does not automatically supply them in this theory.
Moduli can be replaced by their bounded running maxima to make them monotone.

At a fixed requested precision, the finite checker verifies the local
inequalities and incidence identities used by the proof. It must not merely
check the final Cauchy or residue conclusion. The universally quantified
analytic assumptions imply these finite checks by ordinary universal
elimination. Passing one finite check does not establish global analyticity.

A useful final formula shape is

`AnalyticHyp(data) -> forall k, FinalError(data,k) <= 2^(-k)`.

`FinalError` is a fixed primitive recursive rational computation at the
explicit mesh and precision schedule. The displayed norm inequality is an
abbreviation for its signed-integer cross-multiplied version. Name equality is
this family of arbitrarily small estimates, not a decidable equality test.

## 2. Establish executable finite mathematics first

Use ordinary Lean finite types and rational arithmetic to validate the
algorithms. The proposed file is only the first part of this layer.

| Proposed module | Definitions and finite statements | Required inputs |
|---|---|---|
| `RationalCodes` | Signed arithmetic, rational pairs, comparison, complex arithmetic, taxicab norm | Positive-denominator certificates |
| `Chains` | Edge reversal, integer chain sums, splitting at rational points, boundary normalization | Exact common vertex table |
| `Subdivision` | Four-child triangle subdivision; `4^m` cells; diameter and perimeter scale by `2^-m` | Rational vertices; orientation conventions |
| `Quadrature` | Dyadic trapezoidal sums, linearity, affine exactness, nested-grid comparison | Explicit continuity checks |
| `CauchyFinite` | Finite triangle bound and precision scheduler | Explicit differentiability checks |
| `SquareMoments` | Integer-power primitive estimates and kernel normalization | Positive half-side and apartness |
| `AnnularFormula` | Outer square minus two holes; small-square error; quotient modulus | Annular holomorphy contracts |
| `LaurentFinite` | Finite geometric expansion, coefficient names, uniform tail, uniqueness | Concentric annular data |
| `PlanarFilling` | Rational arrangement, crossing indices, grid/fan triangulation, boundary identity | Closed polygonal chain and separated squares |
| `ResidueFinite` | Finite chain reduction plus local tail and numerical errors | All preceding finite contracts |
| `EffectiveCurves` | Optional controlled polygonal approximation and homotopy extension | Explicit curve and homotopy moduli |

Keep the triangle-cell bound separate from the topology routine. The analytic
proof accepts a verified finite chain certificate; `PlanarFilling` is one
producer of that certificate. For axis-aligned outer rectangles and square
holes, implement the much smaller rectangular-grid producer first.

The `four_triangle_cancellation` lemma in the candidate source produces the
six-edge refined boundary. It deliberately does not identify coarse and fine
quadrature for arbitrary functions. Exact splitting of a general contour
integral is obtained later from common-refinement estimates.

## 3. Give every computation a primitive recursive witness

ConciseIPRA's `PR k` has constructors `zero`, `succ`, `proj`, `comp`, and `prec`.
For every program used in the statement or proof, construct an expression of
that syntax, or compile a restricted primitive recursive DSL with a proved
translation. A terminating Lean definition alone is not such a witness.

Required witnesses include:

- addition, multiplication, bounded subtraction, signed normalization,
  absolute value, equality and order tests;
- list coding, length, bounded indexing, concatenation, bounded folds and sums;
- rational arithmetic and comparison, with positivity preservation;
- complex multiplication, norm, conjugation, and inversion when the
  norm-square denominator has a positive certificate;
- natural powers, signed powers away from zero, dyadic rationals, and finite
  power/geometric sums;
- midpoint subdivision, dyadic sample points, boundary accumulation, and
  trapezoidal sums;
- bounded sorting, segment-intersection tests, bounded generic-shear search,
  and the finite grid/fan triangulation;
- all precision schedulers and finite coefficient/integral evaluations.

Use rational numerator-denominator arithmetic directly. Inversion may be made
an everywhere-defined PR operation with a fixed output at zero, while every
use in the theorem has a proved nonzero-denominator premise. No undecidable
apartness test on named complex numbers is introduced.

The analytic programs remain fixed externally. A bounded interpreter with
explicit fuel is a possible alternative, but is unnecessary for this theorem
schema and must not be confused with a universal PR evaluator.

## 4. Internalize finite rational lemmas with quantifier-free induction

For every ordinary finite Lean lemma, produce the corresponding `Fm PTm`
formula and a `PRAAx` derivation. Prove the ring and ordered-rational code laws
first. The `ring` tactics in `FiniteCore.lean` validate polynomial identities in
Lean; their results are not automatically object-theory proofs. Internalize
these particular finite identities by equational derivations, or implement a
verified polynomial normalizer whose certificate checker is proved sound in
iPRA.

The real derived induction rule from `PR.lean` is:

```lean
theorem PRA.qfInd
    (φ : Fm PTm (n + 1)) (hφ : φ.QF)
    (h0 : Γ ⊢[PRAAx] φ.subst (inst zero))
    (hS : φ :: Γ.map Fm.shift ⊢[PRAAx]
      φ.subst (repl (succ (var 0)))) :
    Γ ⊢[PRAAx] Fm.all φ
```

Record the actual quantifier-free invariant at every invocation. The following
invariants suffice for the finite loops:

| Loop | Quantifier-free invariant after coding |
|---|---|
| Rational arithmetic | The accumulated denominator is positive and the encoded result satisfies the cross-multiplied identity |
| Edge accumulation | The partial normalized list has the stated signed multiplicity at each fixed edge index |
| Triangle subdivision | Partial boundary sum equals its accumulated refined outer edges plus explicitly paired internal edges |
| Norm estimation | Partial contour sum has norm bounded by the partial rational error budget |
| Quadrature refinement | Partial fine sum minus partial affine sum has the stated continuity bound |
| Power/kernel expansion | Partial finite sum plus explicit remainder satisfies the exact rational identity |
| Arrangement sweep | Cumulative signed crossing count equals the sum of processed edge contributions |
| Final residue accumulation | Partial weighted local sum has error at most the accumulated Cauchy and Laurent budgets |

A bounded universal check of a decidable PR relation is represented by a
Boolean fold, with assertion `allChecks(...)=1`. This does not justify bounded
comprehension for formulas containing unbounded quantifiers. Freeze all
external precision parameters before induction; use only rational instances
of the analytic hypotheses in its step. Universally generalize over precision
after the finite derivation is finished.

## 5. Cauchy: the exact finite target and convergence adapter

Let a triangle have taxicab diameter `D0` and perimeter `P`. After `m` midpoint
subdivisions, every cell has diameter `D0*2^-m`, perimeter `P*2^-m`, and there
are `4^m` cells. Require `D0*2^-m <= 2^-mu(k)`. The finite target is

`norm(T_(m,n)(boundary triangle))`
`<= D0*P*2^-k + P*2^-n*(2^(m+1)+D0)`.

The second term is essential. The aggregate perimeter of all small cells grows
like `2^m`; using finite value approximations at the original target precision
would leave an error gap. The common value precision on shared edges ensures
exact cancellation.

Internal proof order:

1. Subtract `A(z)=F(a,n)+D(a,n)*(z-a)` on one small triangle.
2. Use the affine annihilation identity.
3. Apply the finite differentiability inequality at its vertices.
4. Apply norm submultiplicativity and the finite triangle inequality.
5. Sum over all cells, using the explicit count/scale identity.
6. Cancel internal edges and prove the displayed bound.
7. Prove the scheduler makes its two terms smaller than the allotted dyadic
   budget.

Separately formalize the nested-grid comparison, for `M>=m` and
`D0*2^-m <= 2^-nu(k)`:

`norm(T_(M,N)(chain)-T_(m,n)(chain))`
`<= L*(2^-k+2^-n+2^-N)`.

For an integer `B>=max(1,D0,L)`, use the paper's regular integral name

`a(r)=r+B+3`, `m(r)=nu(a(r))+B`, `n(r)=a(r)`.

Prove the name's coherence as an arithmetic statement from the comparison
bound. Do not induct on “the integral exists” or “the integral is zero.”
Neither a completed complex-number type nor a completeness theorem belongs in
this object-theory layer.

## 6. Kernel normalization, annular formula, and Laurent expansion

Proceed in this order to avoid circular dependence.

1. **Elementary real integration.** Establish the finite trapezoidal/midpoint
   comparison for `(1+t^2)^(-1)` on `[0,1]`, whose rational Lipschitz constant is
   2. The finite geometric identity proves the Gregory truncation error
   `<=1/(2N+1)`. Define the regular name of pi by four times that integral and
   prove `8/3 <= pi <= 4` in the arithmetic-name sense.
2. **Square kernel.** Parameterize one side by `r*(1+i*t)`. The identity
   `i/(1+i*t)=(t+i)/(1+t^2)` and symmetry give the four-side normalization
   `2*pi*i`. Include the explicit midpoint/trapezoidal adapter if their grids
   differ; do not silently identify different finite quadratures.
3. **Other moments.** For signed `k != -1`, use the difference-of-powers
   identities and `F(u)=u^(k+1)/(k+1)`. With
   `A=max(1,2r,2/r)` and `C_k=(abs(k)+1)*A^(abs(k)+1)`, prove the local primitive
   defect `<=C_k*norm(delta)^2`. Summing finitely telescopes. Integer division
   is legitimate only under the already-decided condition `k+1 != 0`.
4. **Quotient moduli.** If inverse denominator norms are bounded by `A`, values
   by `M`, and derivatives by `D`, prove the Taylor remainder bound
   `A*R_f + (D*A^2+M*A^3)*norm(delta)^2` for `f/(.-z)`.
5. **Annular Cauchy formula.** Use an outer square, an inner square, and a small
   square centered at the evaluation point. Their six possible x coordinates
   and six y coordinates produce at most 25 grid rectangles, hence 50
   triangles before deleted cells. Small-square replacement of `f(w)` by
   `f(z)` costs at most `16*epsilon`.
6. **Laurent coefficients.** Put `s=r/8`, `R=8r`. Define nonnegative coefficients
   from the outer contour and negative coefficients from the inner contour.
   The already-proved kernel identity has geometric ratios at most `1/2`.
   Derive the uniform finite tail on the middle square:

   `norm(f(z)-sum_(k=-N)^(N-1) a_k*(z-a)^k) <= C*2^-N`,

   `C = 16*R*M_R/(R-r) + 16*s*M_s/(r-s)`.

7. **Uniqueness.** Prove radius independence by square-annulus Cauchy and
   coefficient uniqueness by multiplying a tail by a fixed signed power and
   applying the moment identities. Only then identify `a_-1` as the residue.

This route proves the needed Laurent existence result from effective punctured
holomorphy. It does not assume a Laurent theorem from classical complex
analysis. The coefficient names are PR in coefficient index and requested
precision for the fixed analytic input family. Essential singularities are
allowed: no finite bound on the number of negative powers is used.

## 7. Finite topology and global residue estimate

Implement and prove the rectangular-grid boundary identity first. For general
rational polygonal chains, follow the paper's explicit arrangement algorithm:

1. Split all proper intersections and collinear overlaps by rational tests.
2. Choose a shear `(x,y)->(x,y+t*x)` by searching
   `t=0,...,V*(V-1)/2`; at most one value is forbidden by each distinct vertex
   pair.
3. Slice at vertex heights, form rational convex strip cells, split horizontal
   seams at all incident endpoints, and triangulate by a rational interior
   center fan.
4. Label cells by the signed right-ray crossing sum of the original chain.
5. Use closed-chain incidence conservation to show matching labels across
   horizontal seams, and the left-minus-right edge rule on other seams.
6. Delete cells in pole squares and prove
   `boundary T = Gamma - sum_j w_j * boundary Q_j`.

Do not import a classical Jordan or winding-number theorem to justify this
step. Require that the nonzero-weight retained triangles have the stipulated
analytic data; the full-plane producer need not lie in an arbitrary open
domain. Local square labels are constant because each square avoids the chain.
Applying the square kernel to two filling certificates proves uniqueness of
their integer indices. This also identifies the indices with the finite
crossing computation.

The final internal error budget can use

`H*2^-K + sum_j abs(w_j)*8*r_j*C_j*2^(-N_j)`
`+ eta_Gamma + 2*B_res*eta_pi + 10*W*eta_c`,

where `W=sum abs(w_j)`, `B_res=sum abs(w_j)*b_j`, and `b_j` bounds the norm of
residue j. The inner moment gives the usable bound `b_j=8*s_j*M_sj`. Choose all
precisions by bounded binary exponent search to put this expression below the
requested dyadic error. Establish the search bound itself in iPRA; an
unbounded “increase precision until it works” loop is not a substitute.

## 8. Effective curves and homotopies: a controlled extension

A first extension can use piecewise continuously differentiable curves with
fixed PR value/derivative names, supplied uniform moduli, derivative bounds,
and a finite rational partition. A broader version can use uniformly
continuous curves with a supplied finite-variation bound. In either case:

- Prove explicit comparison between the curve's finite sums and its polygonal
  interpolants. Include the accumulation of vertex approximation errors as
  the number of segments increases.
- Supply a PR mesh modulus for a homotopy and a positive rational clearance
  from excluded points and the domain boundary. Grid vertices sampled from
  the homotopy give a finite triangle chain inside certified small balls.
- Use shared endpoint samples to make opposite sides cancel exactly; equality
  of limiting endpoint names by itself is not exact finite cancellation.
- Prove the polygonal residue index is unchanged at sufficiently fine meshes,
  using the explicit annular/certificate argument and the clearance bound.
- Pass to the curve names by finite error estimates and universal precision
  generalization.

Do not claim a PR null-homotopy, a PR variation bound, or a positive clearance
can be recovered from an unrestricted classical curve or a bare topological
existence assertion. The polygonal theorem is already the complete core
version; this extension has its own additional effective input contracts and
acceptance tests.

## 9. Object-theory export and final acceptance criteria

Once the arithmetic formulas and derivations exist, the intended targets are
`[] ⊢[PRAAx] CauchyStatement` and `[] ⊢[PRAAx] ResidueStatement`, or their versions
with explicit assumptions in a context Γ. Those names are proposed module
interfaces, not declarations presently supplied by this archive.

The following is the exact short bridge that can be used inside the pinned
ConciseIPRA project after a proof h has been constructed:

```lean
import ConciseIPRA.NativeBiInterpretation

namespace LeanProofs.ConciseIPRA
open Syn
open scoped Fm

example {n : ℕ} {Γ : List (Fm PTm n)} {φ : Fm PTm n}
    (h : Γ ⊢[PRAAx] φ) :
    NPrf (Γ.map NFm.ofPRA) (NFm.ofPRA φ) :=
  pra_iff_native.mp h

end LeanProofs.ConciseIPRA
```

Acceptance requires all of the following:

1. Build the candidate finite source in a matching Mathlib project with
   `lake env lean FiniteCore.lean`; resolve any elaboration/API differences.
2. Build every new module in the pinned ProveIt toolchain with no admitted
   proof terms or newly postulated analytic assumptions beyond the displayed
   input contracts.
3. Supply `PR` witnesses and object-theory defining equations for every
   arithmetic program appearing in the final formulas.
4. Check every induction formula supplied to `PRA.qfInd` is quantifier-free;
   record its mathematical invariant in the source.
5. Inspect the final theorem types and verify they are object-theory
   derivations, not semantic theorems about standard natural numbers.
6. Prove the analytic hypotheses imply the finite checks and the scheduler
   achieves the claimed dyadic error at every requested precision.
7. Export through the actual `pra_iff_native` bridge; audit metatheoretic
   dependencies with `#print axioms`. The latter is useful but does not replace
   checking the deeply embedded target type.
8. Keep any optional interpretation into ordinary Mathlib complex contour
   integrals separate. Completeness or classical reasoning used only for that
   semantic comparison must not discharge object-theory proof obligations.

The archive currently supplies the mathematical derivation, exact finite
reference computations, elementary uncompiled Lean scripts, and this plan. It
does not supply the completed deep formalization described by these criteria.
