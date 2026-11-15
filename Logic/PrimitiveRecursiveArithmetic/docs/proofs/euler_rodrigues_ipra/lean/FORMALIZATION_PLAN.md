# Euler–Rodrigues formalization boundary and implementation plan

## Status

`RodriguesKernel.lean` supplies finite polynomial proof scripts without
`sorry` or new axioms. `ObjectLanguageBoundary.lean` supplies the actual
repository symbol type and an application of an existing transport theorem.
Neither file was compiled here: Lean and Lake were unavailable. The source
is a prototype, not a verified formalization of the main theorem. In
particular, a Lean proof about Mathlib real numbers would not itself prove
derivability in intuitionistic primitive recursive arithmetic.

Repository target: `VladimirReshetnikov/ProveIt`, commit
`c1bda76f7f86d2ade505355980826f625e36fff3`, Lean and Mathlib `v4.32.0`.

## Exact repository interfaces

The inspected `ConciseIPRA.PR` defines function symbols by zero, successor,
projections, composition, and primitive recursion. `PTm` supplies their
first-order terms; `PRAAx.ind` permits induction only for `Fm.QF` formulas.
`PRA.qfInd` is the derived induction interface. `BiInterpretation.lean`
proves `pra_theorem_iff`; `NativeBiInterpretation.lean` proves
`pra_iff_native`. These are bridges for an object-language derivation after
it exists. They are not a bridge from an arbitrary semantic Lean theorem.

## What “a PR real” means here

Use a *schema*: fix finitely many primitive recursive rational-valued
functions of precision and a fixed finite tuple of natural parameters.
Represent signed integers and positive denominators by natural-number
tuples. Regularity, orthogonality, determinant-one, and the rational gap
certificate become first-order premises, generally universally quantified
over precision. The output name functions are new concrete PR definitions,
built from the fixed input definitions by composition and primitive
recursion. For each such family the resulting implication is an iPRA
theorem. The input functions are not object-language variables.

Do not quantify over arbitrary PR-program codes and silently assume a total
PR evaluator. There is no total universal PR evaluator with that property:
the usual diagonal argument would produce a new PR function omitted by it.
Codes can instead be used with an explicitly bounded evaluator and a
resource certificate, or with a metatheoretic derivation generator; these
are distinct statements and require their own proofs.

## Modules and concrete proof obligations

1. **Encoded arithmetic.** Construct PR symbols for signed-integer and
   positive-denominator rational arithmetic, exact comparison, powers of
   two, bounded maximum, bounded search, finite lists, and finite sums.
   Establish their defining equations and order lemmas as `Prf PRAAx`.
   Clearing *positive* denominators reduces every comparison to natural
   arithmetic. Decidable bounded predicates can be represented by PR
   characteristic functions, so their bounded quantifiers can be eliminated
   before invoking `PRA.qfInd`.

2. **Polynomial certificate elaborator.** Encode multivariate polynomials
   as finite coefficient lists. Prove that PR evaluation commutes with
   addition and multiplication, then build object-language ring identity
   derivations from coefficient-normalization certificates. The proposed
   Lean kernel acts as an independent specification. Exported certificates
   must be checked by the object-language elaborator; `ring` alone does not
   cross the object-language boundary.

3. **Rapid Cauchy-name arithmetic.** Choose and fix one representation and
   state its regularity formula. For each operation, give a PR precision
   transformer plus a rational error inequality at every requested output
   precision. Bounds are numerical inputs. Do not perform induction on a
   formula that says “for all precisions”: prove the finite error inequality
   by quantifier-free induction with the target precision free, then apply
   universal introduction afterward. All input name laws needed for a
   finite estimate are instantiated only at explicitly chosen indices.

4. **Positive reciprocal and square root.** A reciprocal takes an explicit
   positive rational lower bound. For `0 <= x <= B`, first obtain a
   rational sample at precision `2*k+4` and replace it by `b = max(0,b)`.
   Put `N = 2^(k+2)` and use bounded integer search to find the largest `j`
   satisfying `j*j <= N*N*b`; the range
   `j <= (ceil(B)+2)*N` suffices. Then `j/N` approximates `sqrt(b)` with
   error below `1/N`, while
   `abs(sqrt(x)-sqrt(b)) <= sqrt(abs(x-b))` controls the input error. The
   total error is at most `2^(-k-1)`. Every comparison in the search is
   rational and decidable; there is no exact comparison of a real input
   against a rational square. The loop invariant consists of finite
   rational inequalities, with its bounded conjunction encoded by a PR
   Boolean fold, and is quantifier free. The stopping precision is fixed
   in advance. An unbounded search for a positive denominator is not an
   admissible substitute for a supplied lower bound.

5. **Finite matrix algebra.** Instantiate the polynomial elaborator for
   three-dimensional dot and cross products, adjugate identities,
   orthogonality consequences, the symmetric rank-one certificate, and the
   Rodrigues determinant and norm identities. No eigenvalue decomposition,
   maximum principle, exact real equality test, or choice of eigenvectors
   is needed.

6. **Axis extraction with a gap.** The theorem supplies a positive rational
   gap from the identity. At a precision computed from that gap, compare
   the three rational diagonal approximations of the symmetric matrix and
   choose the first maximum. Prove a positive lower bound for the selected
   pivot. Normalize the selected column using the preceding reciprocal and
   square-root routines. Its index is selected once, at the gap-dependent
   fixed precision; recomputing a pivot at every output precision without
   such a fixed choice can destroy the Cauchy property.

7. **Unconditional approximation.** At a target accuracy, make a finite
   robust comparison with a threshold. One branch returns a coordinate
   vector and proves that the rotation is close to the identity. The other
   supplies a gap certificate and invokes the preceding construction.
   Different output accuracies need not select compatible axes: an
   approximate-axis theorem is not a convergent exact-axis constructor.

8. **Real-valued angle by two uniform charts.** The algebraic theorem is
   naturally stated with a circle-valued angle `(c,s)`, `c*c+s*s=1`.
   Compute once a rational `z` with `abs(z-c) <= 1/4`. If `z >= 0`, use
   `theta = 2 * A(s/(1+c))`; otherwise use
   `theta = pi - 2 * A(s/(1-c))`. In the chosen branch the denominator is
   at least `3/4`, hence the argument has absolute value at most `4/3`.
   Thus the uniform integer bound `M=2` suffices. Define `A` by the dyadic
   finite sums in `trigonometric_bridge.tex`, define `E(t)` by the finite
   Taylor polynomials with explicit tails, and prove the Cayley identity
   `E(2*A(t)) = (1+i*t)/(1-i*t)` using the displayed finite product error
   bound. Set `pi = 4*A(1)`. These constructions prove `E(theta)=c+i*s`
   without invoking the fundamental theorem of calculus. The chart is
   chosen once and retained at all output precisions; it gives a valid
   angle, not a globally continuous single-valued principal argument.

9. **Unconditional exact rational-input theorem.** A rational matrix is a
   finite natural-number code, so all nine tests against the identity are
   decidable. Return `e1` for the identity. Otherwise compute the positive
   rational `d = (3-tr(R))/2`, choose the largest exact diagonal entry of
   `S`, and obtain the rational certificate `(v,q,b)` from the article:
   `q = v dot v > 0`, `R*v = v`,
   `c*c + b*b/q = 1`, and
   `R = c*I + (d/q)*v*v^T + (b/q)*crossMatrix(v)`.
   All comparisons and certificate equations are rational. The preceding
   name constructors produce `u=v/sqrt(q)`, `s=b/sqrt(q)`, and the angle.
   Because the input is a finite code, this is a single arithmetic
   construction, unlike the schema used for arbitrary fixed PR real names.

10. **Unconditional exact quaternion theorem.** Compute once a rational
    `z` with `abs(z-c) <= 1/4`. If `z >= 0`, set
    `a = sqrt((1+c)/2)` and `v = w/(2*a)`; here `1+c >= 3/4`, so `a >= 1/2`.
    Otherwise `d > 3/4`; use the separated-axis constructor with the fixed
    gap `delta=1/2`, and set `v = sqrt(d/2)*u`, `a = s/sqrt(2*d)`.
    Prove in each branch `a*a + v dot v = 1`, `2*v*v^T = S`, and `2*a*v=w`.
    The finite algebra then gives
    `R = (a*a-v dot v)*I + 2*v*v^T + 2*a*crossMatrix(v)`.
    All denominator bounds are uniform. The vector part may vanish at
    the identity; normalizing it is not part of this theorem. As with the
    angle charts, the construction selects a representative on names and
    does not promise an extensional globally continuous sign choice.

11. **Final object-language theorem.** Build the actual formula from the
   preceding rational-name definitions. Construct
   `Prf PRAAx [] (Fm.imp hypotheses conclusion)` using the finite estimates and
   first-order intuitionistic rules. Audit every induction call for `QF`.
   Apply `pra_theorem_iff` or `pra_iff_native` only now. Finally compile and
   inspect the dependencies of the derivation-generating Lean declarations.

## Expected validation

In a checkout of the pinned repository, place the proposed files under an
appropriate Lean source directory, run `lake env lean` on each, and fix
syntax/API differences if needed. For the polynomial kernel, inspect
`#print axioms` on the final theorems. For the full result, require an actual
`Prf PRAAx` term and no extra arithmetic axioms; a small list of semantic
axioms in a Mathlib theorem is not sufficient evidence.

## Logical limitations that must remain explicit

- Uniform exact unit-axis extraction for *every* Cauchy-real rotation,
  including rotations arbitrarily close to the identity, has a genuine
  constructive obstruction. A classical split on `R = I` is inadmissible.
- A unit axis supplied as part of the input makes Rodrigues' formula a
  finite algebraic theorem with no such obstruction.
- Rational input matrices have an unconditional exact-axis theorem because
  equality of their entries is decidable; the quaternion theorem for real
  input avoids exact-axis selection by allowing a zero vector part.
- A proof of `not not (exists axis)` is not a computational construction.
- A parameterized family of fixed PR definitions is not the same thing as
  unrestricted quantification over all real matrices.
- Each finite computational estimate can be iPRA-valid while a careless
  appeal to induction over its universally quantified limit formulation
  exceeds the permitted induction scheme.
