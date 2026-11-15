# Lean implementation and object-level iPRA plan

## 1. Exact delivered status

The files in this directory contain **complete, compiler-checked native Lean
proofs of the finite descent and finite search kernels**. They do not contain
an object-level derivation of Mordell--Weil in the repository's first-order
iPRA calculus. In particular, no theorem in this directory constructs weak
Mordell--Weil representatives for an arbitrary elliptic curve or abelian
variety.

| File | What is established |
| --- | --- |
| `DescentCore.lean` | Explicit finite-fuel descent; height decrease; a bounded number of iterations; a compact word in fixed finite generator families; correctness and a linear bound on compact word size. |
| `FiniteSearch.lean` | A supplied finite list can be searched constructively, and a Boolean witness is returned whenever the list contains one. |
| `E1FiniteTable.lean` | The four-element group table corresponding to the proposed rational points of `y² = x³ − x`; associativity, commutativity, exponent two, and two explicit generators. |
| `EllipticSpec.lean` | Concrete native definitions of the codecs, rational affine points, curve equation, chord-and-tangent operations, height, halving quartic, coverage, finite division search, generator words, and explicit propositions that remain to be proved. |
| `DescentExample.lean` | An executable instance on the natural-number additive monoid, used to check the descent machinery. It is not an elliptic-curve result. |
| `Audit.lean` | Prints the foundational axiom dependencies of the principal native Lean results. |

All six Lean source files compile using Lean 4.32.0, commit
`8c9756b28d64dab099da31a4c09229a9e6a2ef35`. They import only `Std` or the other
files in this directory. No source file introduces an `axiom`, uses `sorry`,
or invokes `Classical`. The main descent/search theorems use Lean's
`propext` and `Quot.sound`; `E1FiniteTable.two_generators` uses no axioms.
Consequently this is a useful native formalization, but its axiom report
must not be confused with an object-level iPRA proof.

`EllipticSpec.lean` supplies type-checked definitions and target propositions,
not proofs of the target propositions. Its use of native `Rat` is deliberately
separate from the minimal kernel: Lean's rational implementation has proof
fields whose transitive dependencies can include `Classical.choice`. The
codecs and arithmetic laws therefore still require the explicit first-order
implementation and verification described below; a `Rat` computation is
not an iPRA derivation. The completed descent/search proofs retain precisely
the axiom dependencies reported above.

To reproduce, install the toolchain specified by `lean-toolchain` and run
`bash build.sh`. Alternatively set `MW_LEAN_BIN` to an existing Lean 4.32.0
binary. The script compiles the four library files, prints the axiom
audit, and evaluates the natural-number example. The example returns 37
and its compact word has 16 constructors. The source `Word` representation
uses a dedicated doubling constructor, rather than storing two copies of
each preceding word.

## 2. Exact generic interface

`DescentData α` supplies:

* an addition operation `add : α → α → α`;
* a natural-number height `height : α → Nat` and cutoff `C`;
* finite families `rep : Fin r → α` and `base : Fin b → α`;
* total functions `repIndex`, `baseIndex`, and `child`;
* three proved input laws:

```
height p ≤ C → base (baseIndex p) = p
C < height p → (child p + child p) + rep (repIndex p) = p
C < height p → 2 * height (child p) ≤ height p + C
```

The two finite indexing types make finiteness explicit. The core needs no
group axioms: it evaluates an additive syntax tree by the supplied operation.
For an abelian-group application, the usual group laws turn this word into
an ordinary integer linear combination. Its coefficients are already
computable by `Word.baseCoeff` and `Word.repCoeff`, which return natural
numbers. Natural coefficients suffice because the finite generator family
contains all required low-height points and chosen representatives; negative
points have their own such expressions.

The theorems state, with truncated subtraction on natural numbers,

```
height (run n p) ≤ C + (height p - n)
height (run (height p) p) ≤ C
eval (coordinates p) = p
Word.size (coordinates p) ≤ 3 * height p + 1.
```

These are conditional theorems. `decompose`, `contract`, and `baseComplete`
are fields of an explicitly supplied structure, not unproved global
axioms about an elliptic curve.

## 3. First-order coding to use in the arithmetic bridge

Use the following fixed, elementary coding conventions. Native versions of
the integer, tuple, rational, and point codecs are defined in the compiled
`EllipticSpec.lean`, together with curve operations and target propositions.
Their arithmetic correctness and object-level iPRA translation remain to be
proved. The text below supplies the explicit conventions and required laws.

### 3.1 Naturals, integers, tuples, and finite lists

Encode the integer `z` by `2*z` when `z ≥ 0`, and by `2*(-z)-1` when `z < 0`.
Thus even codes represent nonnegative integers and odd codes represent
negative integers. Addition, multiplication, negation, absolute value,
comparison, and equality are primitive-recursive functions of these codes.

Use the same pairing function as the paper:

```
pair(a,b) = 2^a * (2*b+1) - 1.
```

To decode `n`, find the exponent of two in `n+1` by a search bounded by
`n+1`, then recover the odd quotient; both projections are primitive
recursive. Encode lists by `nil=0` and

```
cons(head,tail) = 1 + pair(head,tail).
```

For every nonempty list code, its tail code is strictly smaller than the
list code. A traversal bounded by the original code therefore suffices
for length, projection, concatenation, replacement, and finite sums.
These are primitive-recursive operations; no unbounded decoder is needed.

### 3.2 Canonical rationals

A rational is a pair `(z,d)` with `d > 0` and `gcd(abs(z),d)=1`. Normalize by
dividing numerator and denominator by their gcd; use the canonical zero
`(0,1)`. Invalid external codes are sent to zero by a total normalization
function. Integer quotient, divisibility, gcd, and reduction are primitive
recursive, for example by searches bounded by the input magnitudes.

Rational equality is equality of canonical pairs. Comparison uses
cross-multiplication. Addition and multiplication are followed by
normalization. Division uses the reciprocal when its input numerator is
nonzero and defaults to zero otherwise; theorems supply nonzero hypotheses
where genuine division is intended.

### 3.3 Short Weierstrass points over Q

Fix integers `a,b` with `4*a^3 + 27*b^2 ≠ 0`. A valid point code is either
`0`, representing `O`, or

```
1 + pair(code(x), code(y))
```

for canonical rationals satisfying `y^2 = x^3 + a*x + b`. A Boolean validity
test checks these finitely many integer equalities. All invalid point
codes are normalized to `O`. Point equality is canonical-code equality.

Define addition by the rational chord-and-tangent formulas, with explicit
branches for `O`, equal x-coordinates, and opposite points:

```
lambda = (y2-y1)/(x2-x1)                when x1 ≠ x2
lambda = (3*x1^2+a)/(2*y1)              when P1=P2 and y1 ≠ 0
x3 = lambda^2-x1-x2
y3 = lambda*(x1-x3)-y1.
```

The vertical case returns `O`; the identity cases return the other point.
All branches are decidable rational comparisons. Closure, associativity,
commutativity, inverses, and the duplication formulas are finite rational
polynomial identities after case splits and denominator clearing. They must
be formally proved, not inferred from the existing four-point table.

### 3.4 The x-projective bit height and bounded enumeration

For `x=n/d` in lowest terms, put `H(x)=max(abs(n),d)`. Define `h(O)=0` and

```
h(P) = least k ≤ H(x(P)) such that H(x(P)) ≤ 2^k.
```

The search is bounded, since `H≥1` and `H≤2^H`. This is the ceiling of the
binary logarithm, implemented without real logarithms. In particular,
`h(P)≤B` implies `H(x(P))≤2^B`.

One entirely explicit base enumeration is available. Put `M=2^B` and
`K=1+abs(a)+abs(b)`. Enumerate `O`, every reduced `x=n/d` with
`abs(n)≤M` and `1≤d≤M`, and every reduced `y=u/v` with
`abs(u)≤K*M^2` and `1≤v≤K*M^2`; retain exactly the pairs satisfying the curve
equation and `h(P)≤B`. The list may contain duplicates before final
normalization; this is harmless.

Why the y-bound is complete: the rational value
`(n^3+a*n*d^2+b*d^3)/d^3` is reduced because its numerator is coprime to `d`.
The square of a reduced `u/v` is reduced. Uniqueness of reduced fractions
therefore gives `v^2=d^3` and
`u^2=n^3+a*n*d^2+b*d^3`. Thus `u^2≤K*M^3` and `v^2≤M^3`, which imply the
stated deliberately generous bounds. The same argument covers `y=0`:
reducedness forces `d=1`. Each supporting gcd and denominator identity is
an elementary integer lemma needed in the arithmetic bridge.

This yields a primitive-recursive list `enum(B)` together with a theorem

```
valid(P) ∧ h(P)≤B → P ∈ enum(B).
```

Membership is a bounded Boolean disjunction. Its least matching index is
the `baseIndex` input to the generic core. Include `O` first so that the
total default index is always available.

## 4. From weak-cover data to a primitive-recursive child selector

### 4.1 Unconditional computation of all rational halves

First implement `Halves(T)`, returning exactly the finite list of rational
points `Q` with `2Q=T`. This construction does not require a weak-cover
hypothesis or any height estimate.

For a valid affine target `T=(u/v,w)` with `u/v` reduced and `v>0`, every
affine half `Q=(X,Y)` has `Y≠0`, and its x-coordinate satisfies

```
v*X^4 - 4*u*X^3 - 2*a*v*X^2
  - (8*b*v+4*a*u)*X + (a^2*v-4*b*u) = 0.
```

This follows from the rational duplication formula

```
x(2Q) = (X^4 - 2*a*X^2 - 8*b*X + a^2)
          / (4*(X^3+a*X+b)).
```

The polynomial's leading coefficient is the nonzero integer `v`. To list
its rational roots by bounded arithmetic, strip any initial power of `X`,
including zero separately if such a power was stripped. The remaining
nonconstant polynomial has nonzero constant coefficient `c0` and leading
coefficient `cd`. Its nonzero reduced rational roots `s/t` satisfy

```
abs(s) ≤ abs(c0),     1 ≤ t ≤ abs(cd),
s divides c0,        t divides cd.
```

Enumerate these finitely many signed numerators and positive denominators,
normalize, and test the polynomial equality exactly. A constant remaining
polynomial contributes no nonzero roots. The rational-root bound is proved
by clearing denominators and applying coprimality; it requires no procedure
for approximate algebraic roots.

For each candidate `X`, reduce `X^3+a*X+b` to a rational `c/d`, `d>0`.
It is a rational square precisely when `c≥0` and both `c` and `d` are
integer squares. Test these using square-root searches bounded by `c` and
`d`, or a bounded integer-square-root algorithm. Form both signs of the
rational square root, remove duplicates if desired, and retain only points
whose **exact** chord-and-tangent doubling equals the full target `T`,
including its y-coordinate. This final check removes denominator-degenerate
candidates and the wrong sign; an x-coordinate equality alone is inadequate.

For `T=O`, return `O` and the points `(X,0)` for rational roots of
`X^3+a*X+b`. The same bounded rational-root procedure applies to this cubic,
including its possible zero root. These are exactly the halves of `O`,
because in characteristic zero a finite point doubles to `O` precisely
when its y-coordinate vanishes. Each branch is total and primitive
recursive. Invalid targets may return the singleton list `[O]`; all
correctness theorems state the validity hypothesis.

The required formal lemma is

```
def Halves (T : PointCode) : List PointCode

theorem Halves_correct (hT : valid T) (Q : PointCode) :
  Q ∈ Halves T ↔ valid Q ∧ twice Q = T
```

This is a remaining arithmetic lemma, not a theorem already present in the
compiled kernel. Its proof is the finite rational-root argument just given,
the rational-square test, and the explicit duplication identity.

### 4.2 Using the supplied quotient representatives

For a fixed curve, supply a nonempty finite list `R_0,...,R_(r-1)` and a
proved coverage statement

```
valid(P) → ∃ i<r, ∃ Q, valid(Q) ∧ P=2Q+R_i.
```

For an input `P`, form the finite candidate list

```
[(Q,i) : i<r, Q ∈ Halves(P-R_i)].
```

The weak-cover hypothesis and `Halves_correct` show that this list contains
a pair satisfying `P=2Q+R_i`. Apply `FiniteSearch.select_correct` to the
Boolean point-equality test, with default `(O,0)` when the promise fails.
The algorithm is total for every input; the coverage theorem proves that
the default is not used on a valid promised input. This selector uses the
quartic root bounds, and does not search a potentially much larger height
box or need a height law to run.

The corresponding formal goal is

```
def ellipticCandidates (P : PointCode) : List (PointCode × Fin r)
def divisionTest (P : PointCode) (qi : PointCode × Fin r) : Bool
def divide (P : PointCode) : PointCode × Fin r

theorem Cover_implies_search_success (hP : valid P)
    (cover : ∀ P, valid P → ∃ Q i, valid Q ∧ twice Q + R i = P) :
  ∃ qi, qi ∈ ellipticCandidates P ∧ divisionTest P qi = true
```

For finite generation, separately prove the explicit height inequality

```
valid(P) ∧ valid(Q) ∧ i<r ∧ P=2Q+R_i
  → 2*h(Q) ≤ h(P)+C.
```

The exact height constants are the separate arithmetic-geometric lemmas
specified in the paper. This plan does not assume an unproved logarithmic
height theorem from an unrestricted real-analysis library.

The final native Lean bridge should have the following shape. These names
describe remaining declarations, and are not claimed as completed source:

```
theorem divide_spec (hP : valid P)
    (cover : ∀ P, valid P → ∃ Q i, valid Q ∧ twice Q + R i = P)
    (heightLaw : ∀ P Q i, valid P → valid Q → twice Q + R i = P →
       2*h Q ≤ h P+C) :
  valid (divide P).1 ∧
  twice (divide P).1 + R (divide P).2 = P ∧
  2*h (divide P).1 ≤ h P+C
```

The total ambient type can be canonical valid points, or all natural codes
with normalization. When using all codes, carry `valid` in every invariant
and have invalid inputs normalize to `O`.

### 4.3 Alternative height-box selector

The general finite-enumeration interface also supports a simpler but larger
search space: enumerate `Q` from `enum(h(P)+C)` and `i<r`, testing the
point equation and contraction inequality. Any covered point has a witness
in this list, since `2*h(Q)≤h(P)+C` implies `h(Q)≤h(P)+C`. The same compiled
finite-search lemmas prove correctness. This alternative is useful for
generic coded groups for which no convenient quartic halving polynomial
is available.

The missing coverage input is mathematically substantial. A finite Selmer
group, or a computable finite list of candidate coverings, does not supply
a rational point on every represented class. No file in this package
silently converts such candidates into actual representatives.

## 5. The object-level iPRA proof

Lean induction with `generalizing p` in `build_correct` is a metatheoretic
proof convenience; its induction formula has quantifiers. To comply with
quantifier-free induction in iPRA, implement the forward loop and prove
one fixed quantifier-free invariant instead.

For a fixed input point `P`, start with

```
Q_0=P, e_0=0, W_0=O.
```

At step `i`, if `h(Q_i)>C`, choose `j_i` and `Q_(i+1)` by the bounded
division function, then put

```
e_(i+1)=e_i+1
W_(i+1)=W_i + [2^e_i] R_(j_i).
```

If `h(Q_i)≤C`, freeze all three state components. Maintain

```
valid(Q_i)
e_i≤i
P = [2^e_i] Q_i + W_i
h(Q_i)≤C+(h(P) dotminus i).
```

Every component is a quantifier-free equality or inequality between fixed
primitive-recursive terms on natural codes. The selector, each iteration
state, scalar multiplication, and the sums defining `W_i` are named
primitive-recursive functions. Quantifier-free induction on `i`, with `P`
as a free parameter, proves the invariant. The contraction input gives
strict descent whenever the loop is active. At the predetermined time
`T=h(P)`, `h(Q_T)≤C`, so the bounded base search supplies a generator
`S_k=Q_T` and the identity

```
P = [2^e_T] S_k + sum_(i<T, active i) [2^e_i] R_(j_i).
```

Computing one coefficient counter per representative turns this identity
into a finite vector of natural coefficients. Their total is at most
`2^(T+1)-1`; the distinguished base coefficient is `2^e_T`, and the total
representative coefficient is `2^e_T-1`. Duplicates in the generator family
may be left in place or merged by bounded equality tests.

An object proof of finite search similarly uses a bounded Boolean prefix
invariant, not a principle of arbitrary countable choice. Quantifier-free
Boolean encodings replace bounded existential/disjunctive notation where
needed. The relation to the repository's exact `Prf`/`PRAAx` objects must be
implemented by constructing an explicit proof term for these invariants.
One must not assert a global reflection principle saying that any accepted
proof checker output is true inside the same theory.

There is also no single primitive-recursive universal evaluator for all
primitive-recursive function codes. Fix the operations for a particular
curve/certificate as terms at the metalevel, or use a bounded evaluator
with a supplied execution budget. The PR claims here concern this explicit
fixed family of algorithms, not an unrestricted evaluator over arbitrary
PR syntax.

## 6. Completing the explicit curve E: y²=x³−x

The four-point native table must be linked to the rational curve by the
following arithmetic modules:

1. Verify the implemented native rational and point codecs and operations,
   supplement them with the integer-square, gcd, and parity lemmas, and
   implement the corresponding fixed first-order primitive-recursive terms.
2. Implement primitive Pythagorean-triple normalization by bounded searches,
   together with the exact gcd/parity and factorization lemmas used in the
   human-readable square-area descent.
3. Define the descent map on a coded nonzero square-area right triangle.
   Supply a total default on invalid inputs; prove validity preservation and
   strict decrease of its positive integer measure.
4. Iterate it for its initial measure, and prove a quantifier-free invariant
   forcing that positive measure below zero. This supplies the required
   no-square-area theorem with a fixed primitive-recursive iteration bound.
5. From a rational point with `y≠0`, form the rational sides
   `(x^2-1)/y`, `2*x/y`, `(x^2+1)/y`; verify their square relation and that
   the absolute area is one. Clear denominators to obtain an integer right
   triangle of nonzero square area, contradicting the preceding theorem.
6. Consequently `y=0`; factor `x^3-x=x(x-1)(x+1)` over the rationals and
   use decidable equality to identify `x∈{-1,0,1}`.
7. Check the chord-and-tangent additions of these three points and `O`, then
   transport `E1FiniteTable.two_generators` through this bijection.

Steps 2--6 are not present as completed Lean proofs here. Their complete
human-readable arithmetic argument is in the accompanying paper; the
repository's existing finite-descent infrastructure can be reused after
checking its precise assumptions and object/metatheory status.

For a nonzero rational `d`, transport along
`(x,y) ↦ (d^2*x,d^3*y)` to get the corresponding result for
`y²=x³−d⁴*x`. A finite product is coded by a finite list of point codes;
addition and the generator construction act coordinatewise. This supplies
arbitrary finite dimensions over Q for that explicit product class, without
claiming the analogous classification over every number field.

## 7. Additional work for arbitrary number fields and abelian varieties

A number field can be represented by an irreducible monic polynomial over
Q and a fixed basis; elements are fixed-length rational vectors modulo the
polynomial. Irreducibility is a supplied certificate or a proved property
of the fixed polynomial. Field operations are rational linear algebra.
An abelian variety needs a finite projective atlas, defining equations,
certified group-law charts, and effective overlap/validity tests. Heights
need explicitly stated normalization and bounded coordinate enumeration.
The generic descent core remains unchanged after these interfaces are
provided.

However, a complete general constructive Mordell--Weil formalization still
needs the missing arithmetic-geometric data and, especially, certified
actual representatives of `A(K)/mA(K)`. This package proves the descent
consequence of such data; it does not present a universal construction of
the data. That is the exact scope of the formalization path.
