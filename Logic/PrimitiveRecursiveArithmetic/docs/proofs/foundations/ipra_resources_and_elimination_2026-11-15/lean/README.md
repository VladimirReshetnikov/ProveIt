# Explicit primitive-recursive demand compilation

This is a standalone Lean 4.32.0 development using only `Std`. New modules
contain no `sorry`, `admit`, or added `axiom`. Build with `./build.sh` after
installing the version in `lean-toolchain`; alternatively set `LEAN_BIN` to
that compiler's absolute path. The script compiles every module and checks
the printed axiom lists. Generated `.olean` files are disposable.

## What is new and what is reused

The earlier `ipra_finite_demand/lean/BackwardDemand.lean` proved a two-pass
construction semantically, and explicitly left its PR syntax and object-theory
proof compiler unimplemented. `DemandCompiler.lean` now constructs that syntax:
for arbitrary fixed `D : PR 2`, `b : PR 1`, `F : PR 3`, it returns
`compiled D b F : PR 2`. Its denotation satisfies

```
C(0,k) = b(k)
C(N+1,k) = F(N,k,C(N,D(N,k))).
```

The recursion parameters change at each predecessor call. This cannot be
expressed by merely reusing one accumulator at the unchanged parameter `k`.
The compiler solves this by calculating the complete backward demand schedule
and then replaying a forward recursion. It uses ordinary `PR.prec` only.

`TermCompiler.lean` adds a separate generic, proof-producing compiler. A term
`t : PTm k` becomes `symbol t : PR k`, with a checked theorem

```
symbol_correct :
  Prf PRAAx Γ (Fm.eq (PTm.app (symbol t) σ) (Syn.subst σ t)).
```

This theorem has an actual object-theory derivability conclusion. It follows
by induction on the finite syntax of `t`, using `PRA.proj`, `PRA.comp`,
`Prf.eqCongr`, and `Prf.eqTrans`. It is useful for compiling arbitrary composite
terms introduced by the mathematical framework into the repository's fixed
PR symbol language, without assuming semantic reflection.

`ObjectDemand.lean` uses that compiler to prove the generic backward pass's
zero and successor equations as actual `Prf PRAAx` derivations. The demand
symbol `D` is arbitrary; these are not a single numerical instance or a
hard-coded toy loop.

Two dependencies are deliberately reused:

* `BackwardDemand.lean` is copied unchanged from
  `Logic/PrimitiveRecursiveArithmetic/docs/proofs/foundations/ipra_finite_demand/lean/BackwardDemand.lean`.
* `ObjectKernel.lean` uses the earlier standalone arrangement from
  `ipra_coherent_methods_2026-11-15/lean/ObjectKernel.lean`. Its three source
  sections were compared afresh with the actual current repository files
  `ConciseIPRA/Syntax.lean`, `Deduction.lean`, `PR.lean`. All are identical
  after import lines and boundary whitespace are removed. Only the enclosing
  provenance comment was updated.

The inspected repository commit is
`b0f6f535ffc16324683fef2c263260a88ae03755`. The included MIT-0 license applies
to the reused ProveIt sources. No modifications to the remote repository were
made by this package.

## Exact status

| Claim | Lean status | Logical level |
|---|---|---|
| Every finite `PTm` term has an equivalent compiled `PR` symbol | Proved, checked | Object iPRA (`Prf PRAAx`) |
| Backward pass zero equation | Proved, checked | Object iPRA |
| Backward pass successor equation | Proved, checked | Object iPRA |
| Explicit two-pass compiler returns a `PR 2` term | Implemented, checked | Syntax construction |
| Generated symbol denotes the intended two-pass algorithm | Proved, checked | Host semantics |
| Full parameter-changing zero/successor equations | Proved, checked semantically | Host semantics |
| Full parameter-changing equations as `Prf PRAAx` derivations | Targets defined; not implemented | Pending object proof |
| Every fixed-dimensional lexicographic fuel has explicit PR syntax | Proved, checked | Syntax and host denotation |
| Controlled-chain bound and automatic bounded termination | Targets defined; human proof in article | Pending Lean proof |
| Complete rational-root list algorithm | Implemented, compiled; correctness targets defined | Pending Lean proof |
| Shear, Sylvester determinant, rational plane-intersection list, and finite auxiliary box | Concrete executable definitions, compiled | Native finite programs |
| Plane-elimination identities, completeness, cardinality, and auxiliary-envelope correctness | Fourteen exact target propositions defined; human proofs in article | Pending Lean proof |

The printed axiom dependencies of all eleven audited theorems are contained in
`[propext, Quot.sound]`; there is no `sorryAx` or `Classical.choice` dependency.
These are Lean's metatheoretic dependencies. They do not add axioms to the
object iPRA calculus. Conversely, a checked host proof about `denote` does not
by itself establish object-iPRA derivability.

The function `denote` is an external interpreter for the inductively defined
PR syntax. It is not claimed primitive recursive and is never added to the
object language as a universal evaluator. The mathematical claim is that for
each *fixed* triple of PR input symbols the generated output is one PR symbol.

## Defined data and arity convention

Primitive recursion arguments follow the actual repository's convention:
`PR.prec f g` receives `(counter, parameters...)`, while `g` receives
`(index, accumulator, parameters...)`.

| Symbol | Arity | Argument order |
|---|---:|---|
| `predSymbol` | 1 | number |
| `monusRev` | 2 | subtrahend, minuend |
| `backStep D` | 4 | reverse index, previous demand, terminal time, final demand |
| `backwardSymbol D` | 3 | reverse-step count, terminal time, final demand |
| `horizonSymbol D` | 3 | terminal time, final demand, forward time |
| `forwardBase D b` | 2 | terminal time, final demand |
| `forwardStep D F` | 4 | forward index, previous value, terminal time, final demand |
| `forwardSymbol D b F` | 3 | forward-step count, terminal time, final demand |
| `compiled D b F` | 2 | terminal time, final demand |

## Path to complete object formalization

`ObjectTargets.lean` defines the exact pending propositions, using actual
`PR`, `PTm`, `Fm`, `PRAAx`, `Prf` types. None is asserted as an axiom.

1. Derive predecessor and truncated-subtraction equations from
   `PRA.precZero` and `PRA.precSucc`; prove the elementary identities needed
   for horizons by equation/QF induction. In particular prove `n ∸ n = 0`
   and `(N+1) ∸ (j+2) = N ∸ (j+1)`.
2. Prove `BackwardCoherenceTarget` by QF induction on `j`. Its base is the
   already implemented `object_backward_succ` at zero, followed by
   `object_backward_zero`; its step uses the same successor equation and the
   subtraction identity in item 1. This target has no order hypothesis.
3. Introduce the PR Boolean comparison symbol and prove that the guarded
   equality for the horizons holds for `t ≤ N`. The arithmetic premise is
   `N+1 ∸ t = (N ∸ t)+1`. The entire induction invariant is a Boolean guard
   implying an equation, hence is QF. `HorizonFinalTarget` follows from
   `MonusSelfTarget` and `object_backward_zero`.
4. Derive the forward base and step targets by unfolding composition and
   recursion, using `TermCompiler.symbol_correct` for the composite bodies.
5. For fixed `N,k`, use QF induction on `t` to prove the guarded equality
   between the two forward executions up to `t ≤ N`. Their initial states
   agree by horizon coherence, and at each step their demanded precisions
   agree. All semantic uses of `advance_congr` have now been replaced by an
   explicit equality invariant.
6. Unfold `compiled`, use the forward step at time `N`, use the terminal
   horizon identity, and apply the equality from item 5. This proves
   `CompiledSuccessorTarget`; the zero target uses the corresponding base.
7. When a closed iPRA result is obtained, transfer it using the actual
   `LeanProofs.ConciseIPRA.pra_iff_native` theorem in
   `ConciseIPRA.NativeBiInterpretation`. Do not apply that theorem to a
   semantic Lean equality: its left side requires `Prf PRAAx`.

All quantified mathematical parameters in this route are first-order numeric
parameters of one fixed PR program. Host syntax induction is used only to
construct derivations, never as a purported induction rule inside iPRA.

## Repository API inspected

The exact source names needed by this package are in namespace
`LeanProofs.ConciseIPRA`:

* `PR`, `PTm`, `PRAAx`, `PRA.proj`, `PRA.comp`, `PRA.precZero`,
  `PRA.precSucc`, `PRA.qfInd` in `ConciseIPRA.PR`;
* `Fm.QF`, `Syn.inst`, `Syn.repl`, `Fm.subst` in `ConciseIPRA.Syntax`;
* `Prf.eqCongr`, `Prf.eqTrans`, `Prf.subst`, `Prf.trans` in
  `ConciseIPRA.Deduction`;
* `NFm.ofPRA` and `pra_iff_native` in
  `ConciseIPRA.NativeBiInterpretation`.

To integrate into the Mathlib-backed repository, replace
`import ObjectKernel` in `TermCompiler.lean` with `import ConciseIPRA.PR`,
place the modules under a dedicated namespace/path, and preserve the explicit
separation between host semantics and object derivations. That integration
build was not run; the standalone build was.

## Fixed-dimensional lexicographic fuel

`LexFuel.lean` implements the exact functions from the article:

```
F₀(h,s) = s+1
F_(d+1)(h,s) = (F_d(h,·)) iterated h(s)+1 times, starting at s.
```

There are checked PR syntax constructors in two forms. `fuelSymbol d h`
handles a fixed unary envelope. `fuelParamSymbol d h` handles a binary envelope
`h(input,time)` while keeping `input` as a variable; thus it provides one PR
program for all inputs at a fixed dimension, not merely a family specialized
at closed input numerals. `boundSymbol d h` specializes the start to zero.
The checked denotation theorem is

```
denote_boundSymbol :
  evalB (boundSymbol d h) x = fuel d (fun t => evalD h x t) 0.
```

The module also defines fixed tuples, Boolean lexicographic decrease, a finite
trajectory, its running-coordinate maximum, the controlled-chain predicate,
and concrete coded machines with Boolean activity/invariant fields. Their
correctness hypotheses occur as premises of `BoundedTerminationTarget` and
`WitnessTarget`; the propositions are not asserted as axioms. The controlled
chain theorem, monotonicity theorem, and bounded-termination theorem remain
Lean targets even though their full mathematical proofs are supplied in the
article. To finish them, implement the bounded partition into maximal blocks
with equal leading coordinate, prove the first-coordinate drop counts the
blocks, and apply induction on the fixed dimension in the metatheory. The
object version uses coded lists and Boolean predicates, followed by QF
induction on the finite block and execution counters.

The host definition `fuel` permits a dimension argument. This is not a
primitive-recursiveness claim about the joint function `(dimension,input)`.
The compiler produces a different finite PR syntax tree for each fixed
dimension; there is no internal universal evaluator for these trees.

## Concrete rational-root program

`RationalRoots.lean` provides low-to-high coefficient lists, rational polynomial
evaluation, coefficient-denominator clearing, the numerator/denominator boxes,
an executable total root-list routine, native heights, and exact completeness,
degree and height target propositions. It also fixes the finite plane-data
convention: the `i`th row contains coefficients of `X^i Y^j` in increasing `j`.

To prove the root routine complete, first show the product of denominators is
positive and is divisible by each denominator. Show the integer coefficient
list is a positive scalar multiple of the original polynomial. Its first
nonzero and last nonzero coefficients bound the reduced numerator and positive
denominator of every nonzero rational root, by the rational-root divisibility
argument after removing an initial power of the indeterminate. Zero is tested
explicitly, and exact evaluation filters all candidates. `eraseDups` preserves
membership and gives `Nodup`. The root-count theorem follows by synthetic
division at distinct roots. None of those proofs is claimed implemented here.

## Concrete plane-elimination programs

`EliminationTargets.lean` imports the root routine and supplies actual Lean
definitions for every program in the extension: low-to-high coefficient
reads, coefficient addition and convolution multiplication, Pascal binomial
coefficients, the finite shear expansion, total degree, the bounded canonical
shear, the Sylvester matrix, its determinant via a bounded `N^N` vector scan
filtered for permutations, specialization in one variable, the rational
intersection list, point heights, the finite coefficient auxiliary box, and
the filtered union of its intersections. No program is supplied by an opaque
interface or an assumed correctness kernel.

`Good` applies strictly to the nonzero positive-degree branch. The total
`intersect` routine returns `some []` when either polynomial is a nonzero
constant, returns `none` for unsupported inputs, and never equates unsupported
with an established empty solution set. Rational values are normalized by the
standard `Rat` implementation. Trailing zero coefficients are permitted;
`coeffEq1` and `coeffEq2` state coefficientwise equality independently of list
lengths.

Fourteen declarations ending in `Target` state precise propositions and are
not proved, postulated as axioms, or used as theorem assumptions elsewhere.
They cover shear evaluation and the bounded shear choice; the determinant
degree bound; common-point projection; explicit polynomial-quotient witnesses
for fibre multiplicity; complete intersection lists, cardinalities, and
heights; the triangular monomial count; coefficient-box size and coverage;
and complete lists, cardinalities, and heights from bounded pointwise
auxiliary witnesses. The fibre divisibility target asks for an actual finite
quotient polynomial, not merely an abstract ideal-membership assertion.

The completion order is coefficient normalization and the binomial identity;
synthetic division and root correctness; finite determinant specialization,
adjugates, and the termwise degree audit; complete fibre enumeration; then
the Vandermonde divisibility lemma and sharp cardinality. The auxiliary-box
and union targets follow by finite enumeration and membership invariants.
The human proofs are supplied in the article, but none of these target
propositions is claimed as a checked Lean theorem. A host theorem about
Mathlib's abstract resultant would need an additional array representation
and PR computation bridge; it cannot replace it silently.
