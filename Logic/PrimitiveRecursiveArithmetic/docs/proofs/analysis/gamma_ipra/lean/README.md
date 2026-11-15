# Lean companion: finite gamma foundations

## Status

`GammaIPRA.lean` is a self-contained Lean 4.32.0 module using only `import Std`.
It compiles without Mathlib, Lake packages, network access, admitted proofs,
axiom declarations, or `native_decide`.

The module contains executable definitions and fourteen named, kernel-checked
finite arithmetic lemmas. Every named lemma is followed by a `#print axioms`
audit; all fourteen report that they depend on no axioms.

The analytic certificate structures are definitions of the remaining proof
obligations. They have **not** been instantiated for gamma. This is a
formalization foundation and an explicit interface for the roadmap, not a
completed Lean proof of the gamma-function theory, and not a completed
object-level iPRA derivation.

## Build

With Lean 4.32.0 on the executable search path:

```sh
cd lean
lean GammaIPRA.lean
```

Alternatively:

```sh
GAMMA_LEAN_BIN=/absolute/path/to/lean ./build.sh
```

The version used for validation was:

```text
Lean (version 4.32.0, x86_64-unknown-linux-gnu,
commit 8c9756b28d64dab099da31a4c09229a9e6a2ef35, Release)
```

`proof_audit.txt` records the successful run and its dependency audit. The
`#eval` lines are reproducible demonstrations, not mathematical certificates.
The proved examples use ordinary kernel reduction, not a trusted native
evaluation oracle.

## Executable definitions

| Part | Definitions |
| --- | --- |
| Finite arithmetic | `factorial`, `rising`, `qsum`, `CQ.sum`, `CQ.product` |
| Exact rational complex arithmetic | `CQ`, addition, subtraction, multiplication, scalar multiplication, conjugation, powers, squared norm, rational 1-norm, checked inverse |
| Elementary finite approximations | `expTaylor`, `logAtanhTaylor`, `positiveLog?`, `positiveLogAt?` |
| Harmonic and zeta sums | `harmonic`, `harmonicPower`, `eulerConstantApprox?` |
| Euler products | `eulerHead`, `eulerReciprocalApprox?`, `eulerGammaApprox?` |
| Explicit natural bounds | `diskMajorant`, `diskB`, `lowerDenominator`, `reciprocalCutoff`, `gammaCutoff` |
| Finite domain tests | `rationalPoleTest` |

`terms` always denotes a term count, not the largest exponent. For example,
`expTaylor z 6` sums degrees 0 through 5. The logarithm function returns
`none` on a nonpositive rational argument. An inverse returns `none` when its
rational input is zero. Such failure checks must not be confused with deciding
whether an arbitrary real or complex name represents zero.

The Euler routines expose both elementary truncation lengths. Their finite
definitions are checked and executable; correctness of their analytic error
bounds is part of the remaining formalization work. In particular,
`gammaCutoff` is the natural cutoff from the paper, not a theorem that the
independently chosen logarithm and exponential lengths have adequate precision.
The `EulerErrorCertificate` explicitly requires that missing connection.

## Checked lemmas

The principal identities include

```text
rising 1 n = factorial n
rising a (m+n) = rising a m * rising (a+m) n
factorial (m+n) = factorial m * rising (m+1) n
factorial m ∣ factorial (m+n)
```

They also establish positivity of factorials and positive rising products,
positivity of the lower-bound denominator, and the relevant inequalities
between the natural cutoff expressions. Small direct induction proofs of
distributivity, associativity, and maximum bounds avoid unnecessary
propositional-extensionality dependencies in these lemmas.

## Certificate interfaces and their intended meaning

`Name` is `Nat → CQ` in the **host metatheory**. `Regular` records a geometric
Cauchy estimate; `NameEq` expresses equality with explicit precision slack;
`ApartAt` is one finite rational witness of separation from zero. These
definitions do not supply a universal primitive recursive evaluator and do
not assert that every Lean function is primitive recursive.

`DiskAnalyticCertificate` requires fixed coefficient names, a coefficient
majorant on a strictly larger disk, a growing truncation schedule, an explicit
coefficient-roundoff budget, and an approximation estimate. The outer-radius
and coefficient conditions are essential: arbitrary polynomial approximation
alone would not establish analyticity.

`ContinuityCertificate` specifies a modulus for extension from rational input
to fixed Cauchy names. `DerivativeRemainderCertificate` specifies a quadratic
first-order Taylor remainder with an adjustable evaluation-precision function.
`EulerErrorCertificate` ties a pole-separated target name to the actual finite
Euler approximation routine and the paper's cutoff.

## Remaining path

1. Prove the rational norm inequalities and finite-series tail estimates.
2. Prove the logarithm and exponential precision bounds, including propagated
   error through the finite Euler head and inversion.
3. Build regular names for Euler's constant, the reciprocal gamma function,
   and gamma on each certified pole-separated disk.
4. Instantiate the analytic, continuity, derivative, and Euler certificate
   interfaces with the paper's explicit formulas.
5. Prove the remaining gamma identities from finite product algebra and the
   estimates; add presentation theorems over Mathlib's real and complex types
   only as a separate layer if desired.
6. Reimplement or certify the finite routines in the repository's primitive
   recursive syntax, generate quantifier-free induction derivations, and
   compile the error inequalities into ConciseIPRA's object theory.

The last step is logically distinct from Lean's host termination checker and
from the fact that a mathematical calculation happens to be executable.
