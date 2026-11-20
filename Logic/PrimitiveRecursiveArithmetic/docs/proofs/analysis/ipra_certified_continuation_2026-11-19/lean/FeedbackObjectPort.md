# Object-theory port: finite weighted feedback

## Scope and provenance

Pin: ProveIt `3ee850b4c2d650cf01263823fd5415963747c5d0`.
Target toolchain supplied by the report: Lean 4.32.0, Mathlib
`81a5d257c8e410db227a6665ed08f64fea08e997`.

The target judgment is the existing

```lean
open LeanProofs.ConciseIPRA
open scoped Fm
-- Γ and φ have the same finite variable scope.
Prf PRAAx Γ φ
```

This is distinct from a theorem about `Rat`, real numbers, `Nat → Rat`, or
an arbitrary Lean function. `FeedbackReference.lean` is only the rational
reference layer. It was not compiled. No new object endpoint is claimed.

## Existing source interfaces actually inspected

Paths are below `Logic/PrimitiveRecursiveArithmetic/`.

* `Derivations/Lean/IPRADerivations/Core/Basic.lean`: `PTm n`, `PR k`,
  fixed-symbol equations, `ind`, and `inst`.
* `Derivations/Lean/IPRADerivations/Foundations/PrecisionCostDAG.lean`:
  guarded finite list entries, rational decoders, finite rational sums,
  `rec2`-based list construction, actual row-length and lookup proofs,
  variable numerical graph size.
* `Derivations/Lean/IPRADerivations/Foundations/PrecisionCostDAGSchedule.lean`:
  actual QF induction over a rational budget, a derived dyadic precision
  schedule, and use of `Analysis.GaussianRootSchedule.binaryLength`.
* `Derivations/Lean/IPRADerivations/Foundations/FiniteReplay.lean`:
  `TraceReflection.Run`, `run_zero`, `run_succ`, and guarded loop induction.
* `Derivations/Lean/IPRADerivations/Foundations/UniformCertificates.lean`:
  finite error composition using `ipra_le` and rational denominator clearing.
* `Bridge/README.md`: `IPRABridge.conciseToStandard` transports an already
  constructed closed Concise derivation to Foundation's standard theory.

The older `Foundations/GraphDemand.lean` and `QueryCompilation.lean` concern
metalevel proof graphs. They must not be cited as evidence that numerical
graphs were previously absent: the newer PrecisionCostDAG modules already
provide them. Our new target is *cyclic* quantitative feedback.

## Numerical data and total primitive-recursive definitions

The definitions below are finite algorithms that can be translated using
the existing `PTm.toPR`, finite sequence and `rec2` interfaces. They are not
unbounded operations on sets of real numbers.

1. Encode a signed rational by a triple `(p,n,d0)`, with value
   `(p-n)/(d0+1)`. Translate to the repository's canonical rational code using
   `Analysis.RationalIntegerNormalization.normalize` on the difference of
   natural terms and the positive denominator `succ d0`.
2. Encode a vector as a length and a sequence code. A read beyond the stored
   length is guarded to the zero triple before decoding. This matters:
   the raw decoder's behavior outside its stored range is not assumed.
3. Encode a matrix as a length and a sequence of row codes. Read only indices
   below the numerical dimension `m`; guard absent rows and entries to zero.
4. Rational addition, subtraction, multiplication, absolute value, order,
   finite sum, finite maximum and positive-denominator division are explicit
   PR operations on these codes. The maximum scans a numerical prefix and
   retains the earlier index on equality, so its argmax is an explicit code.
5. `row(A,v,i,m)` is the bounded sum of `A[i,j]*v[j]` for `j<m`.
6. `cert(A,w,m)` is the product of comparison bits for all `w[i]>0`, all
   `A[i,j]>=0`, and all `2*row(A,w,i,m)<=w[i]`. Empty products are one.
7. `within(w,r,x,y,m)` is the product of bits for
   `abs(x[i]-y[i]) <= r*w[i]`. Equivalent violation sums may be used instead.
8. `step(data,x)` is **one fixed PR program**. For polynomial systems it is
   the bounded evaluator for a finite list of monomials and a finite matrix
   preconditioner. The list lengths, degrees, dimensions and coefficients
   may be numerical data. There is no interpretation of an arbitrary PR
   syntax code as an unrestricted total evaluator.
9. `orbit(data,c,0)=c` and
   `orbit(data,c,n+1)=step(data,orbit(data,c,n))` are a `rec2` definition.
10. `clock(B,w,m,k)` computes `W=max(1,ceil(max_i w[i]))`,
    `J=max(1,ceil(2*B*W))`, and the least `c<=J` with `2^c>=J`, then returns
    `k+c`. Bounded search terminates because `2^J>=J` for `J>=1`.

Malformed data have total default outputs. Correctness is asserted only
under the relevant numerical certificate and well-formedness guards.

## Formula-level contracts

Use the open object-theory formulas, not Lean-side truth assertions:

* `Good(data,x)` is a fixed QF domain predicate, normally a rational box.
* `Gain(data,A,w,m,x,y)` is the bounded comparison fold expressing
  `abs(step(data,x)[i]-step(data,y)[i]) <= sum_j A[i,j]*abs(x[j]-y[j])`.
* `Closed(data)` means the object formula `∀x, Good(data,x) →
  Good(data,step(data,x))`.
* `Lipschitz(data,A,m)` means the object formula asserting `Gain` for all
  rational vector codes `x,y` satisfying `Good` and length guards.

These latter formulas may contain quantifiers in the context. The induction
formula itself remains QF. For a polynomial kernel, prove the two contracts
from finite coefficient/box certificates and discharge the hypotheses.
For a generic fixed kernel they remain explicit hypotheses of the schema.

## Main lemmas and the exact QF invariants

| Lemma | Object-level conclusion | Induction/finite mechanism |
|---|---|---|
| Rational weighted row domination | `within w r x y=1` and `cert=1` imply every gain row is at most `(r/2)*w[i]` | Finite rational sum monotonicity and cleared inequalities |
| Orbit domain | `Good(data,orbit(data,c,n))` | QF domain bit; specialize `Closed` at the current state |
| Increment bound | `sum_(i<m) [2^n abs(x_(n+1,i)-x_(n,i)) > B*w[i]]=0` | QF equation on a PR sum; combine with the domain bit in one coded invariant |
| Finite geometric identity | `sum_(h<j) 2^(j-1-h) = 2^j-1` | QF integer equality; guard the exponent's truncated subtraction under `h<j` |
| Finite tail | `within w (2*B*2^-n*(1-2^-j)) x_(n+j) x_n=1` | QF fold of rational inequalities, induction on numerical `j` |
| Argmax | numerical index `i<m` attains the largest rational ratio | Bounded scan, guarded comparisons, no choice on real values |
| Residual comparison | two residual bounds imply `within w (2*(r+s)) x y=1` | Max witness and rational cancellation at positive weight |
| Inexact comparison | finite convolution bound | QF recurrence invariant in `n`; all input errors are finite data |
| Neumann residual | `(I-A)z_n=b-A^n b` coordinatewise | QF matrix/list equality; finite Fubini and distributivity |
| Name endpoint | coordinate difference at stages `k<=l` is at most `2^-k` | Substitute computed clock in finite tail and apply integer power comparison |

For all loops, the bounded coordinate statements are Booleanized before
induction. Never apply QF induction to `∀i<m,...` merely because it is bounded;
write its PR comparison fold and the equation that this fold equals one.
The local step proof may unpack a particular coordinate using the existing
bounded-fold lemmas, prove its inequality, and repack the fold.

## Build order and remaining obligations

1. First compile `FeedbackReference.lean`; correct elaboration issues without
   weakening its statements. Print axiom reports for the public lemmas.
2. Add `Foundations/WeightedFeedbackSyntax.lean` with the actual codes above,
   substitution lemmas, decoding laws and positive-denominator facts.
3. Add `WeightedFeedbackRows.lean`, proving sum monotonicity and the weighted
   row comparison in `Prf PRAAx` at arbitrary terms.
4. Add `WeightedFeedbackOrbit.lean`, defining the actual orbit code and proving
   domain and dyadic increment invariants by QF induction.
5. Add `WeightedFeedbackTail.lean`, deriving the finite tail, clock and name
   endpoint as object formulas with numerical dimension and stage variables.
6. Add `WeightedFeedbackResidual.lean`, constructing the rational argmax and
   deriving the residual/data-perturbation comparison.
7. Add `WeightedFeedbackInexact.lean` and `WeightedNeumann.lean`; their loop
   bodies use the already derived rational sum/matrix arithmetic.
8. Instantiate a concrete polynomial preconditioner or a coupled linear
   kernel, derive its gain and invariant-domain certificates, close all local
   assumptions, and add its endpoint to the existing axiom audit.
9. Only then export a closed endpoint through `IPRABridge.conciseToStandard`.

The human-readable proof establishes the mathematical finite scheme and
identifies QF invariants. The object port is a defined formalization task, not
completed formalization. The endpoint is local to a valid contraction
certificate and does not cover singular branches or arbitrary noncontractive
systems.

## Concrete producer blueprints

`PolynomialBlueprint.lean` gives actual host definitions for the multivariate
producer in the report. Exponents are finite vectors, terms are rational
coefficient/exponent pairs, and a polynomial is a finite term list. Its
`insertTerm`/`normalize` algorithms combine equal exponent vectors and remove
zero coefficients. This is essential for useful preconditioned certificates:
otherwise syntactically duplicated `h` and `-h` terms could obscure exact
cancellation and inflate a coefficient-derived gain bound.

The file implements finite addition, scaling, multiplication, powering,
substitution and shift expansion; both direct and expanded versions of
`h-B*F(center+h)`; the coefficient-derived gain matrix; positive-weight and
inverse checks; the actual orbit, polynomial residual, and bounded dyadic
clock. The clock includes the largest weight, converting weighted tail bounds
to ordinary coordinate accuracy. The executable example is the coupled
quadratic map in the report.

Its `ProofObligations` structure lists the precise stages to prove:
normalization and finite algebra first, substitution and update equality
second, the monomial and polynomial gain estimates next, Boolean-checker
correctness, then the finite orbit estimates and name theorem. These fields
are uninhabited proof requirements, not assumed axioms or completed lemmas.

`FactorBlueprint.lean` supplies a separate fully finite rational list model
for the factor producer. It defines convolution, default-zero coefficient
reads, the Sylvester matrix, finite inverse checks, monicity/length checks,
column-sum norms, the correction recurrence, its actual factor residual, and
its own dyadic clock. Its main obligations include the exact residual identity
and the reference-factor stability bound. It implements the rational case;
the Gaussian-rational variant requires replacing a coefficient by a pair of
rationals and proving its l1 multiplication bound. Neither file is compiled,
and neither is an embedded-iPRA implementation.

## Reflection and circularity safeguards

The matrix certificate checks rational inequalities. It is not a certificate
that an arbitrary program is globally Lipschitz. The latter must be supplied
as an object derivation for the selected fixed template, or proved from that
template's own finite algebraic certificates.

Similarly, the theorem does not assert internally that every object proof
accepted by a generic proof checker is sound. Object proof assembly remains
an external construction of a `Prf PRAAx` term. A cyclic list of logical
contracts is never discharged by feeding a desired conclusion back into
itself. Only the constructed finite orbit, with its QF geometric invariant,
discharges the numerical feedback.
