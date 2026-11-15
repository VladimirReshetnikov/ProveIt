# Lean formalization outline

## Status

**These files are an uncompiled blueprint, not a completed Lean proof.**
No Lean/Lake executable was available in the creation environment. The files
contain concrete finite definitions, exact proposed statements, and a small
conditional interface to the existing repository. They do not contain an
inhabitant of the main isoperimetric theorem. There are no added axioms or
unfinished proof terms disguised as completed results.

The accompanying report supplies the human-readable mathematical argument.
The purpose of these files is to make the remaining formalization work
specific and to distinguish an ordinary Lean proof from a proof *inside iPRA*.

## Pinned environment

The source inspection used ProveIt commit
`329161f8da0b319d51ba9f6246c4b19d243f7193`.

| Item | Value |
|---|---|
| Lean toolchain | `leanprover/lean4:v4.32.0` |
| Mathlib revision | `81a5d257c8e410db227a6665ed08f64fea08e997` |
| Existing Lake library | `ConciseIPRA` |
| Existing namespace | `LeanProofs.ConciseIPRA` |
| Existing source directory | `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean` |

The files use these verified repository APIs:

- `ConciseIPRA.PR`: `PR`, `PTm`, `PRAAx`, `PRA.qfInd`.
- `ConciseIPRA.Syntax`: `Fm`, `Fm.QF`, scoped terms and substitution.
- `ConciseIPRA.Deduction`: `Prf`, the embedded intuitionistic derivability
  judgment.
- `ConciseIPRA.NativeBiInterpretation`: `pra_iff_native`, `NFm.ofPRA`, `NPrf`.

The roadmap can instead remain entirely in the ordinary `PRAAx` presentation;
the native-calculus translation is optional and can be done last.

## Files

### `IsoperimetricIPRA/FiniteData.lean`

Defines rational points, cyclic edges, signed shoelace area, explicit bounded
maximization, and the downward dyadic square-root algorithm. It implements
the specified lower approximation:

1. `r = k + 4`, `t = 4*k + 16`, `h = 2^(-t)`.
2. Start with `cHat = 0` and apply
   `cHat := sqrtDown((1+cHat)/2,t)` exactly `r-1` times.
3. `cBar = min(1,cHat+2*h)`.
4. `piLower(k) = 2^r * sqrtDown(1-cBar^2,t)`.

For `x >= 0`, `sqrtDown` is the largest rational `j/2^t` whose square is at
most `x`. Its scan bound is
`2^t * (abs(x.num) + 1)`. This bound is intentionally inefficient but explicit
and primitive recursive. No real square root is invoked.

The desired finite inequality is:

```text
4 * piLower(k) * abs(area(p)) <= (sum u)^2 + 2^(-k)
```

under the hypotheses that `p` is nonempty, `u` has one entry per edge, and
each `u_i >= 0` has `u_i^2 >= edgeNormSq_i`. Invalid input is accepted
vacuously by `finiteCheck`, so the universal statement can be expressed by
one equation for a total numerical function.

### `IsoperimetricIPRA/PrimitiveCoding.lean`

Specifies a concrete natural-number coding:

- Positive pairing: `pair(a,b) = 2^a*(2*b+1)`.
- List zero represents the empty list; a positive pair represents a cons.
- Pair decoding divides out powers of two with explicit fuel.
- List decoding uses its own code as an explicit fuel bound.
- Integers use even codes for nonnegative values and odd codes for negative
  values.
- Rationals store a signed numerator and denominator minus one; all decoded
  denominators are positive.

The codec inverse laws and the primitive-recursive compilation are still
obligations. The file defines the concrete total function
`checkNat(polygonCode,upperLengthCode,precision)`, returning zero on success.

### `IsoperimetricIPRA/InternalGoal.lean`

Constructs the precise internal formula, for the to-be-compiled `PR 3` symbol
`checkCode`:

```text
forall p, forall u, forall k, checkCode(p,u,k) = 0
```

The genuine completion target is:

```lean
Prf PRAAx [] (finiteFormula checkCode)
```

The explicit parameter `checkCode` must be compiled from the specified
`Codec.checkNat`, with the required defining-equation correspondence. Choosing
an arbitrary symbol or a constant-zero symbol would not meet the specification.
The file does not hide this missing compilation in an axiom.

`transferToNative` is a short conditional consequence of the repository's
existing `pra_iff_native`. Its premise is the uncompleted internal proof.
It must not be reported as a proof of the isoperimetric inequality.

## Completion roadmap

The suggested modules below are work units, not existing files.

| Module | Main statements | Proof method and iPRA audit |
|---|---|---|
| `CodecLaws` | Inverse laws; positive denominators; decoded list fuel is sufficient | Bounded division, pairing, and prefix invariants. Translate finite membership and bounded quantification to PR Boolean scans. |
| `RationalArithmetic` | Addition, multiplication, order, absolute value, clearing denominators, finite Cauchy-Schwarz | Signed integer arithmetic and polynomial identities; use only quantifier-free induction over coded finite arrays. Canonical gcd normalization is optional mathematically, but must be matched to the chosen implementation. |
| `DyadicSqrt` | `d^2 <= x < (d+2^-t)^2`; positivity; total scan bound | Prove correctness of the bounded maximum scan, then clear the positive denominator. Never search until an approximation happens to separate from zero. |
| `RadicalTower` | Exact arithmetic and sign tests for nested nonnegative square roots | At `a+b*sqrt(d)`, determine signs recursively; in opposite-sign cases compare `a^2` with `b^2*d` in the previous level. Use a ring with rational denominators and explicit positive cross-multipliers. Avoid an unjustified inverse formula in a possibly reducible quadratic extension. |
| `DyadicCircle` | Half-angle identities, exact powers of the dyadic root of unity, chord/tangent bounds, bounds for `piLower` | Iterate the finite radical recurrences. Prove every required order fact by finite algebra and explicit error recurrences. Ordinary trigonometric names are explanatory notation rather than new object-language functions. |
| `CyclicFourier` | Finite orthogonality; finite Parseval; signed area and edge-energy identities | Expand finite sums and collect terms. The geometric-sum identity uses a positive norm square to justify cancellation; no infinite Fourier series is involved. |
| `FourierBound` | `4*sin(pi/N)*abs(A) <= cos(pi/N)*E` for dyadic `N >= 4` | Bound every signed frequency contribution by its energy coefficient, then sum. All statements are ultimately inequalities in an explicitly coded finite radical ring. |
| `Subdivision` | Area preservation; finite edge-count bound; energy estimate | Divide each original edge into an explicit positive number of equal rational pieces, and pad with repeated vertices as needed. Use the exact subdivision rule and budget from the report, including `S=0` separately. |
| `FiniteBound` | The desired rational inequality at precision `k` | Substitute the explicit dyadic size and arithmetic error budget. Obtain the checker equation and introduce its three universal quantifiers. |
| `CurveSchema` | The represented-curve inequality at each requested precision | Fix PR approximation and modulus symbols. Instantiate the finite theorem at the explicitly chosen index and use the given rational error bounds. |

For reference, with normalized finite Fourier coefficients `w_l`, the
identities to formalize are:

```text
E = N * sum_l 4*sin(pi*l/N)^2 * |w_l|^2
A = (N/2) * sum_l sin(2*pi*l/N) * |w_l|^2.
```

The notation is complex-number shorthand for pairs in the finite radical
ring. These formulas do not require analytic completeness, a limiting Fourier
series, or an infinite-dimensional spectral theorem.

### The induction boundary matters

Lean's ambient natural-number induction permits formulas much stronger than
iPRA does. Therefore proving `FiniteTheorem` in ambient Lean, even without
classical choice, is not the completion criterion. For each internal use of
`PRA.qfInd`, construct the `Fm.QF` witness. A bounded conjunction such as
`forall i < n, P(i)` is represented by the equation asserting that a PR
Boolean fold returns true, rather than passed unchanged as a quantified
induction formula.

An implementation may prove an external semantic correctness theorem first
as a useful check, but it must additionally construct the `Prf PRAAx`
derivation. Existing bi-interpretation theorems do not automatically turn an
arbitrary Lean theorem into a derivation in iPRA.

### The curve boundary matters

There is no primitive-recursive universal evaluator for all PR programs.
The curve theorem is a schema for fixed PR polygon-approximation and modulus
symbols, or a theorem about explicitly bounded computation traces with a
supplied PR bound. It is not one formula evaluating arbitrary function codes.
An arbitrary classical real curve is not a first-order numerical object.

## Suggested integration and verification

Copy the `IsoperimetricIPRA` directory into a new Lean source directory in a
checkout of the pinned ProveIt revision, then add a Lake library declaration
pointing to that directory. For example, with sources under
`Analysis/IsoperimetricIPRA/Lean`:

```toml
[[lean_lib]]
name = "IsoperimetricIPRA"
srcDir = "Analysis/IsoperimetricIPRA/Lean"
```

Then build one module at a time, fixing any elaboration/API discrepancies:

```sh
lake build +IsoperimetricIPRA.FiniteData
lake build +IsoperimetricIPRA.PrimitiveCoding
lake build +IsoperimetricIPRA.InternalGoal
```

After completing each proof module, inspect its actual theorem type and
dependencies. Ultimately check the internal target itself, not merely the
conditional transfer theorem. An audit of Lean's metatheoretic axioms is
useful, but it is separate from the embedded iPRA rule/induction audit.

No repository files were modified by the creation of this packet.
