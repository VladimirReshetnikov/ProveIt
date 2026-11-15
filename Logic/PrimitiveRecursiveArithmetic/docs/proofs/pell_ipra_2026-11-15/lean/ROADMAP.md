# Lean and object-iPRA formalization roadmap

## Status

The mathematical argument is intended for first-order intuitionistic primitive
recursive arithmetic (iPRA). The included `PellCore.lean` is an ordinary Lean
algebraic starting point. `Transfer.lean` records the exact existing bridge
from embedded iPRA derivations to the native scalar calculus. Neither file was
compiled in this environment: no `lean` or `lake` executable was available.
No full machine-checked Pell theorem or native iPRA certificate is claimed.
The source files contain no `sorry` or added axioms. That textual fact does
not replace compilation or checking the axioms of elaborated declarations.

## Pinned foundations inspected

Repository: `VladimirReshetnikov/ProveIt`.
Revision: `f1b0582aada7262b10924ea1ba12e2e490d2934b`.
Toolchain and Mathlib tag: `v4.32.0`.
Paths below are relative to the repository root.

| Path | Git blob SHA | Relevant fact inspected in source |
| --- | --- | --- |
| `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/PR.lean` | `3251631592070d9ed3687cc0bf7dbd5eb452e46f` | `PR`, `PTm`, `PRAAx`, `PRA.qfInd` |
| `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/TeqReflect.lean` | `0123475a8659dac1725b1b2b15fbf22166d79a8b` | `chi`, `chi_iff`, `Teq.qfInd` |
| `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/TeqRec.lean` | `08d8b38514913c2c689495b762cd58ac002561e8` | pair-accumulator implementation of primitive recursion; `Q.prc_zero`, `Q.prc_succ` |
| `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/NativeBiInterpretation.lean` | `ccfe499b9687ea0e176f832686d8e492fe15544b` | `pra_iff_native`, `native_iff_pra` |
| `Computability/HilbertTenthProblem/Lean/Diophantine/Common/Pell.lean` | `a274d33765c9989c4223864a8c67be90877d57c7` | special discriminant `a*a-1`; `χ_sq`, growth and congruence formulas |
| `Computability/HilbertTenthProblem/Lean/Diophantine/Common/PellMod.lean` | `0e669cfca380d4318038d814f1485ea70f410afe` | residue formulas; the current `exists_dvd_yn` uses infinite-domain pigeonhole |
| `Computability/DiophantineConsistency/Lean/DiophantineConsistency/NativePellBootstrap.lean` | `94c590a476bda379cf8af3c4617c4a48092f3f87` | ordinary Lean/Mathlib Pell classification for special discriminants; no embedded iPRA derivation |

The repository README was also inspected (blob
`8f810145b9ac8502748080a4ec4f15f2ad4c99bb`). Its description of the foundation
agrees with the actual source files above.

## Exact object theory

The `PR` inductive type has constructors `zero`, `succ`, `proj`, `comp`, and
`prec`. `PTm n` is the first-order term language with `n` free variables.
`PRAAx` contains the defining equations of these primitive recursive symbols,
successor separation and injectivity, and induction only for `φ.QF`.
The underlying `Prf` relation uses intuitionistic natural deduction.

Signed integers should be implemented as canonical natural-number codes,
for example `2a` for nonnegative `a` and `2a-1` for `-a` with `a>=1`, with all operations
defined by bounded arithmetic. Pairs and finite vectors should use the
repository's pairing and primitive recursion support. The ordinary Lean
`Int × Int` representation in `PellCore.lean` is a convenient mathematical
layer; its coding and correctness proofs are separate formalization work.

The final object theorem should be a declaration of the form

```lean
-- Target shape; PellCorrect is to be constructed from explicit PR symbols.
-- theorem pellCorrect :
--   ([] : List (Fm PTm 0)) ⊢[PRAAx] Fm.all PellCorrect := ...
```

Here `PellCorrect : Fm PTm 1` is a quantifier-free formula with free input
`D`. Its ordinary reading is

    2 <= D and isqrt(D)^2 != D  ->
      0 < Y(D) and Y(D) <= H(D) and X(D) <= H(D)
      and X(D)^2 = D*Y(D)^2 + 1.

The functions `X` and `Y` are explicit primitive recursive functions, with
default output on invalid inputs. The independent norm-collision construction
permits the coarse constants

    C(D) = 2D+1,
    M(D) = 2 C(D)^3,
    H(D) = (D+2)^2 C(D)^(2(M(D)+1)).

Thus existence is obtained from an explicit pair of terms, not from an
unbounded least-number operation. Universal generalization and existential
introduction then give the customary Pell existence statement. Once this
embedded derivation exists, the inspected theorem `pra_iff_native` converts
it directly to `NPrf [] (NFm.ofPRA (...))`.

The main finite continued-fraction construction gives a smaller bound and
computes the fundamental pair directly. With `a=isqrt(D)`, set

    S(D)=2a(a+1),     B(D)=(2a+1)^(2S(D)).

Use `B` in place of `H` in the final Skolemized theorem when formalizing that
route. The `BoundedExistence` and `SolverCorrect` definitions in the supplied
Lean core use this CF bound. The independent norm-collision bound remains
available as `coordinateBound`.

## Finite continued fractions and the exact fundamental solution

The executable reference program follows this route. Its formalization
requires the following additional modules, which can replace the Dirichlet
and norm-collision modules for the main existence theorem:

1. **ReducedCF.** The state `(m,d)` satisfies `0<=m<=a`, `1<=d<=2a`,
   `d|(D-m*m)`, and `sqrt(D)-m<d<sqrt(D)+m`. The last two strict
   inequalities are the decidable tests `D<(d+m)^2` and
   `(d-m<0 or (d-m)^2<D)`. Define the digit `c=(a+m)/d` by natural
   division, then `m'=dc-m`, `d'=(D-m'^2)/d`. Prove closure and
   injectivity by the elementary inverse-state calculation in the article.
2. **CFPeriod.** Enumerate at most `S+1` states. A finite collision and
   injectivity give a return to the initial reduced state `(a,D-a*a)`
   within `S` steps. Bounded minimization finds the first period `ell`.
   Its final reduced state is `(a,1)`.
3. **Convergents.** Simultaneous recursion produces the numerator and
   denominator with their preceding values. Maintain the two linear
   identities and determinant invariant from the article. Derive
   `p_(n-1)^2-Dq_(n-1)^2=(-1)^n d_n`. Norm one therefore occurs within
   `2ell<=2S` convergents, and all their coordinates are at most `B`.
4. **FiniteLegendre.** For a candidate denominator `q`, compute only the
   first `q+2` denominators. Find the last `n<=q` with
   `q_n<=q<q_(n+1)`. Express a candidate pair in the unimodular basis
   of the two consecutive convergents. Opposite signs of successive
   errors prove the finite best-approximation inequality. A nonzero
   determinant then contradicts an error less than `1/(2q^2)`.
5. **FundamentalEndpoint.** Every positive norm-plus-or-minus-one
   solution satisfies that strict error inequality and is a convergent.
   The exact norm identity and the unique state with `d=1` show that
   unit positions are precisely `n+1=t*ell`. Consequently the
   fundamental positive solution occurs at `n=ell-1` for even `ell`,
   and at `n=2ell-1` for odd `ell`. Negative Pell is solvable exactly
   when `ell` is odd, with least negative solution at `n=ell-1`.

All of these proof obligations concern finite traces. The first period
search is bounded by `S`, the solver by `2S`, and the Legendre comparison
for an arbitrary candidate by `q+2`. The sign tests use integer squares;
no type of infinite continued fractions or arbitrary reals is required.

## Required modules and their proof obligations

1. **Arithmetic.** Define total division/remainder, bounded minimum, integer
   coding, `isqrt`, finite arrays, and powering by `PR` syntax. Prove the
   equations and elementary inequalities as embedded derivations. Implement
   Euclid's algorithm with a counter bounded by the initial sum; use it for
   the fact that a rational square root of an integer is an integer.
2. **QuadraticOrder.** Work with pairs representing `a+b*sqrt(D)`. Define
   sign by sign tests on `a,b` and the integer comparison `a*a` versus
   `D*b*b`. Under the nonsquare guard, equality and order are decidable.
   Prove addition, multiplication by positive elements, conjugation, and
   norm identities by finite sign cases. There is no real-number completion.
3. **FinitePigeonhole.** For each specific PR list of `B+1` values below
   `B`, compute the first collision by a bounded scan. Maintain an
   occupancy array of length `B`. Under the no-collision flag, its number
   of occupied entries equals the number scanned; the count is always at
   most `B`. These are equalities/inequalities of PR terms. This proves a
   bounded witness-producing collision lemma.
4. **Dirichlet.** For `Q+1` multiples of `sqrt(D)`, compute their bins with
   `isqrt(D*(Q*j)^2)-Q*isqrt(D*j^2)`. Prove that each bin is below `Q`.
   The collision yields explicit `p,q`, `1 <= q <= Q`, and a strict error
   bound `|p-q*sqrt(D)| < 1/Q`. Use cross multiplication and the quadratic
   sign function to express this inequality arithmetically.
5. **Existence.** Use `Q_i=C^(i+1)` for `i <= M`. Prove the nonzero norm
   bound, the separation `q_(i+1)>Q_i`, and the finite signature bound.
   Bounded collision in the signatures gives the quotient of two equal-norm
   elements with integral coefficients and norm one. Prove the second
   coefficient is nonzero and both absolute values are bounded by `H`.
   This completes the existence certificate needed for the bounded solver.
6. **FundamentalUnit.** Search the finite box through `H` for the smallest
   positive second coordinate. Implement division by this unit as an
   integer pair transformation with fuel equal to the input second
   coordinate. Every active step preserves norm one and strictly decreases
   that coordinate. A loop invariant reconstructs the input as a computed
   power times the current pair. Terminal correctness proves exhaustive
   generation and returns the exponent.
7. **Extensions.** Prove the negative equation's bounded decision and
   parametrization; implement generalized-norm reduction with explicit
   fuel and seed bounds. Record a separate bound for every scan and descent.
   Congruences modulo `m` use the first `m*m+1` pair residues, giving a
   period in `[1,m*m]`; no infinite-domain pigeonhole lemma is needed.
8. **Native.** Apply `pra_iff_native` to the closed iPRA theorem. Print and
   archive axioms of the resulting Lean declaration, as well as a fresh
   build log. If a Python checker certificate is produced, replay it too.

## Quantifier-free induction audit

Bounded quantifiers in the prose abbreviate primitive recursive Boolean
folds. A universal bounded check is a finite conjunction; an existential
check is a finite disjunction with a witness accumulator. Induction is
applied to the equality of the corresponding characteristic term with its
truth value. For witness extraction, the invariant includes the output
witness and its bounds, so an existentially quantified induction formula
is unnecessary.

| Construction | Induction parameter | Quantifier-free invariant data |
| --- | --- | --- |
| floor square root | bounded trial counter | current square below the input; next trial either accepted or rejected |
| finite collision | number of entries scanned | occupancy count, collision flag and bounded witness indices |
| approximation list | index `i <= M` | explicit coordinates, norm, error-test Boolean, coordinate bounds |
| signature scan | index `i <= M` | code below `M`; returned indices and equality of signature components |
| unit powers | exponent | norm and two recurrence equations |
| descent | fuel consumed | norm, decrease when active, and reconstruction by an accumulated power |
| bounded least unit | scan counter | current candidate and finite-prefix minimality Boolean |
| modular periods | scan counter up to `m*m` | pair residues and an explicit collision |

All inputs other than the induction counter remain free numerical
parameters. Compound bounded assertions are reflected to equations of PR
terms before using `PRA.qfInd`. Generic higher-order Lean lemmas over arbitrary
functions may help organize the metatheory, but their object-level instances
must be generated for the specific primitive recursive symbols used here.

## Reuse boundary

Mathlib's ordinary Pell theory and the repository's special Pell sequences
are useful for checking algebraic identities and later comparing results.
They do not by themselves supply a derivation in `PRAAx`. In particular,
`Finite.exists_ne_map_eq_of_infinite` in the existing modular argument must
be replaced by the finite bounded scan described above. The title or
namespace of a file containing the word `Native` does not identify its
object theory; inspect the theorem's type.

## First build steps

With the pinned toolchain available, the standalone starting point is:

```sh
lake update
lake exe cache get
lake env lean PellCore.lean
```

`Transfer.lean` is checked from the pinned ProveIt workspace after building
`ConciseIPRA.NativeBiInterpretation`. The supplied Lake project intentionally
does not list it as a standalone target because it imports that repository
library. No build log is supplied for a build that was not run.
