# Lean completion plan and the iPRA boundary

## Current status

The mathematical proof is in the accompanying paper. The Lean files in this
directory are a formalization outline with concrete proof scripts for the
finite algebra. **They were not compiled:** this environment has neither a
Lean nor a Lake executable. The files add no axioms and contain no unfinished
proof placeholders; that fact does not certify their elaboration or complete
the missing proofs.

In particular, this package does **not** contain a proof of an
`InternalTarget` from `ObjectTargets.lean`. It also does not contain completed
formal proofs of `RootCorrectness` or the Cauchy-name representation lemmas.
These omissions are explicitly represented as specifications and work units.

The external Lean kernel and the internal iPRA proof are separate tasks.
`ring` establishes the displayed identities in Lean's ambient type theory;
it does not, by itself, construct a derivation in `Prf PRAAx`. The internal
arithmetic proof must be constructed from the axioms and inference rules
listed below. Neither a proof about `Real` nor a generic ordered-field theorem
would discharge that task automatically.

## Files

| File | Content | Status |
|---|---|---|
| `FiniteAlgebra.lean` | Coordinate cosine identity, Gram identity, Heron polynomial/factorizations, circumcenter dot/norm/equidistance identities, vertex determinant identities, angle-product numerators | Concrete proof scripts using `ring`; uncompiled |
| `RationalAlgebra.lean` | Side/sine normalizations, doubled-radius identity, cosine normalization, semiperimeter product, quantitative square-difference bound | Concrete proof scripts using `field_simp`, `ring`, and `nlinarith`; uncompiled |
| `DyadicSpec.lean` | Total bounded square-root scan and precise correctness propositions | Executable-definition and theorem-statement outline; uncompiled; correctness proofs absent |
| `FiniteTargets.lean` | Fully expanded finite Heron and trigonometric propositions with the paper's exact schedules | Proposition specifications only; uncompiled; proofs absent |
| `ObjectTargets.lean` | Quantifier-free checker formula, universal closure, internal derivability targets, conditional transport to native ConciseIPRA | Target specification and conditional proof script; uncompiled; target derivations absent |
| `VALIDATION.txt` | Independent exact polynomial-expansion results and compilation status | Executed symbolic checks; not a Lean verification log |
| `lean-toolchain` | The toolchain used by the inspected ProveIt commit | Version pin only |

## Pinned source and actual API

Repository: <https://github.com/VladimirReshetnikov/ProveIt>

Inspected commit: `38cafaa5be7f4602567440bcebc754abdbacefc9`.

The root toolchain is `leanprover/lean4:v4.32.0`; the root Lake configuration
requires Mathlib `v4.32.0`. All ConciseIPRA modules below are beneath
`Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/` and use
namespace `LeanProofs.ConciseIPRA`.

* `Syntax.lean` defines the scoped term interface `Syn`, first-order formulas
  `Fm`, substitution, and the predicate `Fm.QF`.
* `Deduction.lean` defines `Prf Ax Γ φ`: intuitionistic natural deduction with
  equality and explicit scoped quantifier rules.
* `PR.lean` defines `PR k` using zero, successor, projections, composition,
  and primitive recursion; `PTm n`; and the theory `PRAAx`. Its axioms are the
  defining equations, successor separation/injectivity, and quantifier-free
  induction. `PRA.qfInd` requires an explicit witness of `φ.QF`.
* `BiInterpretation.lean` supplies `pra_iff_teq` and `pra_theorem_iff`.
* `NativeBiInterpretation.lean` supplies `NFm.ofPRA` and `pra_iff_native`.

The existing file
`Algebra/SurrealNumbers/Surreal/Algebra/Geometry.lean` already follows the
dot/determinant method for generic finite geometry. Its `normSq_sub`,
`dot_sq_add_cross_sq`, `heron_factorization`, and `heron` are useful external
proof patterns. Its ordered-field and square-root structure is **not** an
iPRA construction. The present finite kernel avoids importing that larger
theory and adds the circumcenter identities needed for the extended sine law.

## Recommended implementation order

### 1. Elaborate the external algebra scripts

In a checkout of the pinned ProveIt revision that already has the prescribed
Lean toolchain and Mathlib cache, run each file using the project's Lake
environment:

```sh
lake env lean /absolute/path/to/triangle_ipra/lean/FiniteAlgebra.lean
lake env lean /absolute/path/to/triangle_ipra/lean/RationalAlgebra.lean
lake env lean /absolute/path/to/triangle_ipra/lean/DyadicSpec.lean
lake env lean /absolute/path/to/triangle_ipra/lean/FiniteTargets.lean
lake build ConciseIPRA.NativeBiInterpretation
lake env lean /absolute/path/to/triangle_ipra/lean/ObjectTargets.lean
```

These commands are instructions for a future configured environment; they
were not run here. Resolve any elaboration or tactic-version differences
before regarding the scripts as checked. `FiniteAlgebra.lean` and
`FiniteTargets.lean` are intentionally independent of the other new files.
The latter takes a root routine as a parameter: its intended instantiation
is the rational version of `DyadicSpec.rootLower`, together with the missing
proof of `RootContract`. The proposition definitions `finiteHeron` and
`finiteTrig` are not theorem declarations or hidden assumptions that those
results already hold.

### 2. Fix the natural-number codec and PR symbols

Use one explicit total codec throughout. A convenient signed-integer code is
`2z` for nonnegative `z` and `-2z-1` for negative `z`. Represent a rational by
a signed numerator and a positive denominator. Fixed-length tuples require
only elementary pairing and projections. Unreduced fractions suffice, provided
equality and order are compared by cross multiplication. Decode invalid
denominator inputs to a specified default.

Construct the actual `PR` syntax trees for addition, multiplication, powers,
comparison, truncated subtraction, pairing/unpairing, signed arithmetic,
rational arithmetic, and the bounded scan. Derive their equations using
`PRA.proj`, `PRA.comp`, `PRA.precZero`, and `PRA.precSucc`. Prove the codec and
arithmetic laws within `Prf PRAAx` by quantifier-free induction. This is the
compiler/correspondence obligation behind the `checkCode` parameters in
`ObjectTargets.lean`; an arbitrary symbol with the right arity is insufficient.

No universal primitive-recursive evaluator for all PR program codes is
assumed. A fixed primitive-recursive definition can be translated into its
particular `PR` syntax tree. Quantification over a numerical program code
followed by an unbounded universal evaluation operation is not allowed.

### 3. Replay the finite algebra in the object theory

First prove addition/multiplication ring laws for coded signed integers and
rationals. Every displayed geometric identity then has a finite equational
derivation obtained by expansion, associativity, commutativity, and
distributivity. One can either write these few derivations directly or build
a verified polynomial normalizer that returns such derivations. A Boolean
polynomial checker alone is not sufficient unless its soundness is proved
inside the theory.

The normalized variables in `FiniteAlgebra.lean` correspond to

```text
U = x*x + y*y             c*c
V = z*z + w*w             b*b
W = (x-z)^2 + (y-w)^2     a*a
p = x*z + y*w            dot product
t = x*w - y*z            signed doubled area
N = (U*w - V*y, V*x - U*z).
```

The essential identities are `W = U+V-2p`, `UV = p²+t²`, the Heron
factorization, the two center dot equations, and `|N|² = UVW`. The remaining
identities are convenient consequences or direct polynomial checks.

### 4. Prove the bounded square-root bracket

For inputs `p,q,k` with `q ≥ 1`, put `S = 2^k` and `J = (p+1)S`. The scan in
`DyadicSpec.lean` retains the last `j ≤ J` satisfying

```text
P(j) : q*j*j ≤ p*S*S.
```

There is a particularly small **quantifier-free** invariant. If `r_n` is the
scan result after processing all indices through `n`, prove

```text
r_n ≤ n  and  q*r_n² ≤ p*S²  and
  (r_n < n -> p*S² < q*(r_n+1)²).
```

At `n=0`, `r_n=0`. At a successor, if `P(n+1)` holds, replace the result by
`n+1`; the last implication has false antecedent. Otherwise keep the old
result. If `r_n<n`, use the previous invariant; if `r_n=n`, the failed
`P(n+1)` test gives the required strict upper bound. These cases are decidable
natural comparisons, with no excluded-middle step for arbitrary propositions.
Every comparison is represented by its PR characteristic equation, so the
induction formula remains quantifier-free in the actual object language.

Now

```text
q*J² ≥ (p+1)²*S² > p*S²,
```

because `S≥1`, `q≥1`, and `(p+1)²>p`. Thus `r_J<J`; otherwise its lower
bracket would contradict the endpoint bound. The invariant at `J` gives

```text
q*r_J² ≤ p*S² < q*(r_J+1)².
```

Clear the positive denominator to obtain the rational interval bracket of
width `2^-k`. Formalize this proof using `PRA.qfInd`, and then establish the
specific `SquareRootTarget` for the compiled checker.

### 5. Build the finite-precision representation layer

Use regular rational names with a supplied primitive-recursive modulus, or
the equivalent interval representation in the paper. Fixed parameters and
moduli are part of the schema. Define each output approximation by a PR
recipe and prove its numerical error bound at a free precision parameter.
Only afterward universally close that parameter. Do not apply induction to
an unbounded Cauchy assertion.

The work units are concrete:

| Lemma | Finite argument |
|---|---|
| Addition/subtraction | Sum the rational input errors; choose one extra bit for two summands |
| Absolute value | `abs(abs(x)-abs(y)) ≤ abs(x-y)`, by decidable rational sign cases |
| Multiplication on a bounded range | Expand `xy-x'y' = x(y-y') + y'(x-x')` and insert supplied rational size bounds |
| Square-root stability | For nonnegative rationals, `(r-s)² ≤ abs(r²-s²)`; combine with the dyadic bracket. `RationalAlgebra.square_difference_bound` is an external script for the key inequality |
| Inversion with separation | From `abs(x)≥δ>0` and an approximation error at most `δ/2`, obtain `abs(x')≥δ/2`; use `abs(1/x-1/x') = abs(x-x')/abs(xx')` |
| Nonnegative-root uniqueness | Given desired error `ε`, make the squared difference at most `ε²`; apply the square-difference estimate. No exact real equality test is required |

Use the explicit safe bounds and precision choices from the paper rather
than a generic appeal to continuity. Every finite error inequality is a
signed rational comparison that can be discharged by denominator clearing.
The denominator lower bound for nondegenerate triangles is supplied as
positive data; no search for a sign change or a separation witness is hidden
inside a supposedly primitive-recursive procedure.

### 6. Assemble the three geometric theorems

Define sides by the computed nonnegative square roots of `W,V,U`, area by
`abs(t)/2`, and angle values by normalized dot/determinant pairs. Prove the
unit-circle relation from Gram's identity. Relate those pairs to geometric
angles by normalized orthogonal coordinates; the algebra itself needs no
transcendental angle measure or numerical `π`.

The cosine law follows from `W=U+V-2p` and normalization. The three sine values
have a common doubled-area numerator and give the same ratio after division
by the opposite side. The explicit center `N/(2t)` has equal squared distance
to all three vertices; `|N|²=UVW` and nonnegative-root uniqueness give
`R=abc/(2|t|)`. Thus the common side-over-sine ratio is `2R`.

For Heron, substitute the side-square equations in the polynomial
factorization, use `t²=4Δ²`, and divide by `16`. The nonnegative-root version
then follows from root uniqueness. This part extends to degenerate triangles;
the ratio and circumradius statements retain their explicit nondegeneracy
hypotheses.

The angle-product identities in the finite kernel provide a direct algebraic
check of compatibility among the three unit angle pairs. If a separate
radian-valued trigonometric library is desired, its identification with those
geometric pairs is an additional representation theorem; it is unnecessary
for the usual geometric sine and cosine laws proved here.

### 7. Complete the actual iPRA endpoint

Construct the concrete checker code and a proof of its `InternalTarget`.
For the represented-coordinate schema, fix the PR approximation and modulus
symbols, encode the finitely many named premises, and derive each
finite-precision conclusion at a free index. Universal quantification and
intuitionistic implication are then introduced using `Prf`'s ordinary rules.

Finally apply `pra_iff_native` if a statement in the concise native language
is desired. `transferToNative` demonstrates only that last conditional step.
The acceptance criterion is the displayed object-language theorem with its
intended concrete code and hypotheses, not merely successful compilation of
the external algebra or absence of classical axioms in a host-Lean theorem.
