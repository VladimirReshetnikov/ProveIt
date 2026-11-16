# iPRA arithmetic audit and repository provenance

## Exact theorem boundary

The literal arithmetic theorem is a universally closed implication about five
**coded rationals**, not a first-order assertion quantifying over arbitrary real
manifolds. Put `u=1-x^2`, `S=r^2+a^2*x^2`,
`D=r^2-2*m*r+a^2+q^2`. Let `Valid(v)` mean that the input is a five-tuple of
rational codes with positive denominators, and let `Regular(v)` additionally
test `S(v)*D(v)*u(v) != 0`. Then iPRA proves

    forall v, Regular(v)=1 -> ResidualsZero(v)=1.

`ResidualsZero` is the fixed Boolean conjunction of the rational inverse-matrix,
Ricci/Einstein--Maxwell and Maxwell/Bianchi identities specified in the paper.
The evaluator differentiates the **symbolic formulas first**, then evaluates at
the rational input. Numerical differentiation is not substituted for calculus.
For the Boyer--Lindquist Lorentzian interpretation add `S>0` and `u>0`; a
quantitative apartness witness handles `D`. The final paper proves signature
by an explicit null coframe, so no decision of the sign of an arbitrary real
`D` is necessary. Its ingoing stereographic atlas requires only `S>0` with
apartness and is regular even at `D=0`. The arithmetic field-equation
identities themselves only need the stated nonzero denominators.

The closed assertion `Check(certificate)=1` is true by a finite computation and
can be proved by unfolding the defining equations. That closed assertion alone
is not the main theorem. The essential extra result is finite algebraic
evaluation soundness, proved below. Its application yields the uniformly
quantified coded-rational theorem. No claim that every true property of a
primitive recursive function is provable in iPRA is used.

## Base theory

Use intuitionistic first-order logic with equality; function symbols for each
specified primitive recursive definition; defining equations for zero,
successor, projection, composition and primitive recursion; successor
injectivity/nonzeroness; and quantifier-free induction with parameters. New PR
symbols abbreviate explicit definitions. Case distinctions on coded integers,
rationals, exponents and finite Booleans are decidable. There is no need for
excluded middle on arbitrary propositions, choice, Markov's principle, a
completeness theorem, or a consistency/reflection principle.

## Explicit coding and totality

One serviceable natural-number pairing is

    pair(b,c) = ((b+c)*(b+c+1))/2 + c.

Use `nil=0`, `cons(b,c)=1+pair(b,c)`. A nonempty tail is smaller than its list
code. Decode by a search bounded by the input code; perform recursive list folds
with fuel bounded by the original code, and freeze once finished. Thus projections,
length, indexing, append, maps and folds are PR. Integer `z>=0` has code `2*z`;
integer `-(z+1)` has code `2*z+1`. A rational is a numerator code and a positive
denominator. It need not be reduced: equality is integer cross multiplication.
All operations have designated total defaults on invalid input and carry
separate validity tests. Gcd, if an efficient implementation uses it, is a bounded
Euclidean loop and is unnecessary for the mathematical proof.

A monomial consists of a signed integer coefficient and five natural exponents;
a polynomial is a finite list of monomials. Products enumerate the bounded
Cartesian product and add exponent vectors. Like terms are collected by bounded
search and integer addition. Alternatively store a dense coefficient array with
coordinate degree cap `d` and `(d+1)^5` entries. The representation and all its
operations are data interpreters for one fixed polynomial grammar, not a
universal interpreter for all PR functions.

## Quantifier-free version of bounded assertions

For a fixed Boolean PR predicate `P(w,i)`, define

    allP(w,0)=1,
    allP(w,k+1)=allP(w,k)*P(w,k).

Every predicate used here has values 0 or 1. The formula `allP(w,k)=1` is atomic.
Its elementary unfoldings and the implication from the product to any queried
factor use quantifier-free induction, keeping the queried index and all input
data free. The reverse direction from a bounded-universal hypothesis is proved
with an ambient bound `B` fixed, using the invariant
`k<=B -> allP(w,k)=1`; the bounded-universal hypothesis remains in the context,
outside the induction formula. Nested bounded assertions use repeated Boolean
folds. This avoids inserting an unbounded universal quantifier into an induction
formula.

## Polynomial evaluation soundness: a concrete invariant

Fix the polynomial input code `p` and the rational environment `v` as free
parameters throughout. Let `L` be the list length, and let `d` bound every
coordinate exponent occurring in the input. Enumerate exponent vectors by the
base-`d+1` number `e < E=(d+1)^5`. Write `M(e,v)` for the corresponding monomial
value and

    C(k,e) = sum(i<k, coefficient(i) * [exponent(i)=e]).

The following equality is the induction invariant in the processed-term counter
`k<=L`:

    sum(i<k, coefficient(i)*M(exponent(i),v))
       = sum(e<E, C(k,e)*M(e,v)).

Both sides are fixed PR rational functions; rational equality is a cross-product
integer equation. At zero both sides vanish. At the successor, the coefficient
array changes only at the single explicitly given index `exponent(k)`, and the
same summand is added on both sides. The finite delta-sum identity is proved by
quantifier-free induction on the sum counter with the selected exponent free.
Consequently the evaluation of the raw term list equals evaluation of its
collected coefficient array.

If every collected coefficient is zero, this equality gives evaluation zero.
If a sparse checker inspects only exponent vectors occurring in its input, an
absent exponent has coefficient zero by the defining Boolean filter. Thus a
bounded scan supplies the equivalent dense all-coefficients-zero condition.
Again all queried exponents and the rational environment are fixed free
parameters; universal generalization happens after these inductions.

For multiplication the analogous invariant expands the first `k` index pairs
in the finite Cartesian product. Distributivity identifies this bounded double
sum with the product of the two evaluations. Addition and negation have the
corresponding one-loop invariants. These prove the polynomial evaluator's ring
laws inside iPRA. Exponentiation is its ordinary PR iteration; the identity
`v^(b+c)=v^b*v^c` has an atomic induction on `c` with `b,v` free.

## Rational normalization soundness: a concrete invariant

Convert the finite expression tree to a topologically ordered instruction list.
An instruction is a variable, integer constant, addition, multiplication,
negation or reciprocal of earlier registers. The symbolic register is a pair
`(N_j,D_j)` of integer polynomials. Addition uses

    (N,D)+(P,Q) = (N*Q+P*D,D*Q),

multiplication uses `(N*P,D*Q)`, negation changes the numerator sign, and
reciprocal swaps numerator and denominator. No factorization is required.
The numerical register evaluates the same instruction at the rational input.

Let `SafePrefix(k,v)` assert, as a Boolean fold, that all reciprocals among the
first `k` instructions have nonzero numerical operands. Use the single
quantifier-free invariant

    SafePrefix(k,v)=1 ->
      all(j<k,
          eval(D_j,v) != 0 AND
          numericalRegister(j,v)*eval(D_j,v)=eval(N_j,v))=1.

The point `v`, the whole instruction-list code and its length remain free
parameters. For a successor instruction the premise implies the preceding
prefix guard. Addition and multiplication use the polynomial ring laws proved
above. Negation is immediate. For inversion, the old denominator and old value
are nonzero, so its old numerator is nonzero; swapping the numerator and
denominator preserves the cross-product equation. This is decidable rational
arithmetic, with its familiar elementary cancellation proof. The invariant is
therefore maintained by quantifier-free induction on the instruction counter.

The fixed metric program only inverts `2`, `4`, `S`, `D`, `u`, and products and
powers of these quantities. Its formal differentiation introduces squares of
already guarded operands. Thus `Regular(v)` implies `SafePrefix(L,v)` by a
fixed finite proof. An exact zero coefficient certificate for each numerator,
together with the invariant, proves each residual vanishes. Their finite
conjunction yields the displayed arithmetic theorem.

A reduced implementation may cancel a common polynomial factor for efficiency.
Such a cancellation is accepted only with a multiplication certificate
`before = factor * after` for numerator and denominator, and a nonzero guard for
the factor. Alternatively cross multiply the original and reduced fraction and
check the resulting polynomial is zero. The raw no-cancellation normalizer in
`lean/RationalGeometry.lean` avoids that additional rule entirely.

## Why all computation is primitive recursive

The grammar is fixed; data size and expression length can vary. Parsing and
evaluation are bounded traversals. At each arithmetic instruction, numerator
and denominator polynomial degree caps can be doubled. If `H` bounds the term
count and coefficient magnitude, replace it by a sufficiently generous fixed
polynomial such as `8*(H+1)^4` after an instruction. Iterating that explicit
majorant for the input instruction count is primitive recursion and bounds
every intermediate coefficient list. Nested loops and finite exponentiation are
PR. There is no unbounded minimization. For the actual Kerr--Newman program the
list and all symbolic bounds are constants.

Equivalently, because the master calculation is fixed, expand every successful
normalization into a fixed sequence of commutative-ring equalities, plus
guarded inverse laws. Their derivations over coded rationals give the main
uniform identity directly. This route is especially simple proof-theoretically:
it requires no theorem saying that iPRA trusts arbitrary proofs accepted by its
own proof checker. The only inductions are the finite arithmetic library laws.

## Formal differentiation and real semantics

Formal differentiation is a PR transformation on the fixed expression grammar,
with product and reciprocal rules. It is distinct from a theorem asserting
real differentiability. For real interpretation, specify each PR Cauchy name
externally, supply value bounds and positive lower bounds for denominators,
and use the local value/derivative error bounds developed in the paper. At every
fixed precision the output contract is arithmetic and admits the same bounded
reasoning. This is a schema for fixed names and explicit guards, not a claimed
PR evaluator for arbitrary codes of PR functions. It makes no assertion about
all set-theoretic real numbers inside first-order iPRA.

## Lean endpoint

The checked repository bridge requires an actual object derivation

    Prf PRAAx [] closedStatement

before `pra_iff_native` can produce `NPrf [] (NFm.ofPRA closedStatement)`.
A host theorem in Lean about `Rat`, `CommRing`, `Matrix`, or a smooth manifold
does not supply that object derivation automatically. The included outline keeps
the host target, PR-symbol compilation and object proof as separate obligations.

## Inspected sources and status

Pinned commit: **87ccad4659b63acdce75540d17a69d799bbd25ad**.
All links below use this commit. Accessed during this task.

1. [PrimitiveRecursiveArithmetic/README.md](https://github.com/VladimirReshetnikov/ProveIt/blob/87ccad4659b63acdce75540d17a69d799bbd25ad/Logic/PrimitiveRecursiveArithmetic/README.md).
   It distinguishes the kernel-checked ConciseIPRA library from 62 research
   packets filed as delivered and not rerun, checked or compiled by intake. It
   expressly says no packet claims a `Prf PRAAx` derivation for its main theorem.
   We do not promote those packets to checked dependencies.
2. [PR.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/87ccad4659b63acdce75540d17a69d799bbd25ad/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/PR.lean).
   Read in full. Defines `PR`, `PTm`, `PRAAx`; its `PRA.qfInd` exposes the exact
   allowed object induction. Recursion counter is the first input of `PR.prec`.
3. [Syntax.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/87ccad4659b63acdce75540d17a69d799bbd25ad/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/Syntax.lean).
   Read in full. Defines scoped first-order `Fm`, substitution and `Fm.QF`.
4. [Deduction.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/87ccad4659b63acdce75540d17a69d799bbd25ad/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/Deduction.lean).
   Read in full. Defines intuitionistic `Prf`, substitution, cut, equality
   congruence/transitivity and quantifier rules.
5. [NativeBiInterpretation.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/87ccad4659b63acdce75540d17a69d799bbd25ad/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/NativeBiInterpretation.lean).
   Read in full. `pra_iff_native` transfers existing derivations. No new
   consistency or uniform semantic-reflection claim is extracted from it.
6. [Cayley--Hamilton foundations](https://github.com/VladimirReshetnikov/ProveIt/blob/87ccad4659b63acdce75540d17a69d799bbd25ad/Logic/PrimitiveRecursiveArithmetic/docs/proofs/algebra/cayley_hamilton_ipra/sections/foundations.tex).
   Read in full as an unverified research exposition. Its separation of
   arithmetic, algebraic interpretation and effective analytic interpretation
   is useful; no theorem is imported on the strength of that file alone.
7. [Presentation-to-witness framework](https://github.com/VladimirReshetnikov/ProveIt/blob/87ccad4659b63acdce75540d17a69d799bbd25ad/Logic/PrimitiveRecursiveArithmetic/docs/proofs/foundations/ipra_presentations_to_witnesses/paper/sections/02_framework.tex)
   and its [FiniteAlgebraTargets.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/87ccad4659b63acdce75540d17a69d799bbd25ad/Logic/PrimitiveRecursiveArithmetic/docs/proofs/foundations/ipra_presentations_to_witnesses/lean/FiniteAlgebraTargets.lean).
   Both read in full. The latter deliberately defines proposition-valued targets
   without asserting them as proved. Our source files follow that honest status
   pattern. The framework's fixed-grammar versus arbitrary-PR-program distinction
   is respected above. Its separate enumeration theorem is not used here.
8. [lean-toolchain](https://github.com/VladimirReshetnikov/ProveIt/blob/87ccad4659b63acdce75540d17a69d799bbd25ad/lean-toolchain)
   and [lakefile.toml](https://github.com/VladimirReshetnikov/ProveIt/blob/87ccad4659b63acdce75540d17a69d799bbd25ad/lakefile.toml).
   Read to identify Lean/mathlib v4.32.0 and the ConciseIPRA library path.

No Lean executable was available in the task environment. The new Lean outlines
have not been compiled; their complete kernel proof, especially the concrete
object-language derivation, is explicitly unfinished.
