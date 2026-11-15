# Lean formalization plan and exact status

## Status and final boundary

`AperySpec.lean` is a complete executable specification of the finite
arithmetic quantities and the final checker. `FiniteAlgebraSpec.lean` gives
the finite polynomial and rational-function data and operations used in the
proof. `ObjectTheoryTarget.lean`
specifies its object-language compilation and contains only conditional
transport results. These files are **uncompiled specifications and a
formalization outline**, not a completed Lean proof of Apéry's theorem.
No Lean toolchain was available in the authoring environment. There are no
`sorry` terms or custom axioms; neither `FiniteProofObligations` nor
`CompiledAperyProgram` has a supplied inhabitant.

The paper supplies the human-readable arithmetic argument. Completing the
formalization requires both a PR compiler instance and an internal derivation
of the particular closed formula. An external proof of every field of
`FiniteProofObligations` is useful for debugging but does not by itself prove
the object-language result.

The required result is, schematically,

```lean
theorem apery_ipra : InternalAperyProof compiledAperyProgram := ...
```

Here the ellipsis is roadmap notation, not supplied Lean source. The actual
type expands to `Prf PRAAx [] (aperyFormula compiledAperyProgram)` in
namespace `LeanProofs.ConciseIPRA`. The repository's `pra_iff_native` then
transports the proof to its concise native presentation. This transfer is
already expressed, conditionally, in `native_of_internal`.

## 1. Exact finite target

All numerators are represented by a difference of two naturals. Let
`q = q0 + 1` and `p = pPositive - pNegative`. Define

```
c(n,k) = (-1)^(n-k) choose(n,k) choose(n+k,k)
A(n)   = sum(k=0,...,n) c(n,k)^2
H_s(k) = sum(j=1,...,k) 1/j^s
B(n)   = sum(k=0,...,n) c(n,k)^2 H_3(k)
       + sum(0<=k<l<=n) c(n,k)c(n,l)/(l-k) * (H_2(k)-H_2(l))
D(n)   = lcm(1,...,n), D(0)=1
n(q)   = 42^(q+1)
h(n)   = (n+1)^3 A(n+1)
N(q)   = A(n(q)) h(n(q))
Z(M)   = sum(j=1,...,M) 1/j^3.
```

The statement is the explicit disjunction

```
p/q + 1/N(q) < Z(N(q))
    or
Z(N(q)) + 1/(2N(q)^2) + 1/N(q) < p/q.
```

`checkApery pPositive pNegative q0` returns zero exactly when that disjunction
holds. It computes rational comparisons by cross multiplication, so its
result is a natural number. The eventual closed object sentence is literally
the universal closure of `checkApery(pPositive,pNegative,q0) = 0`.

The cutoff depends only on the denominator. Every signed integer occurs as
a difference of naturals; reduced fractions are unnecessary. The offset
`q0+1` removes the need for a separate zero-denominator case from the sentence.

For every `K>=M>=1`, finite telescoping proves

```
0 <= Z(K)-Z(M) <= 1/(2M^2).
```

Consequently the closed rational interval
`[Z(N), Z(N)+1/(2N^2)]` is a certified enclosure for the zeta name, and the
final disjunction gives a positive gap from every rational candidate. No
type of arbitrary real numbers is needed to state or prove this theorem.

## 2. Natural arithmetic and raw fractions

The specification deliberately avoids gcd normalization of rationals.
`Fraction` stores `(positive,negative,denominator)` and denotes their signed
numerator divided by the denominator. Addition, subtraction, multiplication,
scaling and division by a displayed natural all have explicit polynomial
coordinate formulas. Validity is the single inequality `denominator>0`.

The comparisons `eqv`, `le`, and `lt` are defined by natural-number cross
multiplication. Prove their order, congruence and arithmetic laws only under
validity hypotheses. An induction invariant for a sum carries both its
current signed numerator/denominator and the positivity of that denominator.

`divide a d` is a completely specified bounded search over candidates no
larger than `a`, totalized to zero when `d=0`. Prove that, for `d>0`, its
result `u` satisfies `du<=a<d(u+1)`. The invariant of `quotientScan a d k`
states that its answer is the greatest successful candidate among `0,...,k`.
Encode this bounded greatestness assertion by a finite Boolean conjunction;
do not apply induction to an unbounded quantifier.

`lcmScan a b k` retains the first positive common multiple found among
`1,...,k`. For positive `a,b`, the terminal search bound `a*b` contains a
success. Its invariant is either that no candidate has succeeded or that
the saved candidate is a positive common multiple no larger than every
candidate processed. Again, the quantifiers are bounded and can be replaced
by Boolean loops. This proves that `D` is the intended least common multiple
and that `r | D(n)` for `1<=r<=n`.

Binomial coefficients are computed as exact factorial quotients when
`k<=n`, and zero otherwise. Prove factorial positivity and the standard
factorial divisibility/Pascal identities by finite induction. The recurrence
definitions of addition, multiplication, exponentiation and truncated
subtraction are the usual PR ones. Every occurrence of a higher-order sum
helper is specialized to its fixed displayed body before compilation; the
object language never quantifies over an arbitrary function.

`scaledBInteger` first cancels the positive and negative raw numerator
coordinates using truncated subtraction, then divides each surviving scaled
magnitude by the denominator. This cancellation is essential: raw positive
and negative coordinates need not separately be divisible before cancellation.
The integrality lemma proves that the result represents exactly `D(n)^3B(n)`.

## 3. Compile the particular programs

Use `PR.zero`, `PR.succ`, `PR.proj`, `PR.comp` and `PR.prec` from
`ConciseIPRA.PR`. Keep a syntax tree for each arithmetic function and prove
its recursion equations internally using `PRA.comp`, `PRA.precZero`, and
`PRA.precSucc`. Compile conditionals from Boolean zero tests and a selector.

Finite loop states are tuples of natural numbers. The existing scalar
pairing/projection development (`TeqPair`) is one route; a direct PR encoding
is also possible. Compile fixed bounded searches and sums by primitive
recursion on the loop counter. Never implement this stage by an unrestricted
search for a witness, an assumed termination oracle, or a generic universal
PR evaluator.

For each concrete syntax tree prove its external interpretation agrees with
the specification. `evalPR` in `ObjectTheoryTarget.lean` gives that agreement
type. This only identifies the program: it does not prove that its value is
zero. The second obligation is to construct the corresponding internal
correctness derivations from `PRAAx`.

The compiler target has arity three. Under its three universal binders the
variables `pPositive,pNegative,q0` have de Bruijn indices `2,1,0`. The file
`ObjectTheoryTarget.lean` uses exactly that order.

## 4. Finite algebra and recurrence layer

`FiniteAlgebraSpec.lean` supplies the concrete definitions for this layer:

| Definition family | Representation and behavior |
| --- | --- |
| `Poly`, `padd`, `pmul`, `pdiff`, `peval`, `pcompose`, `pshift`, `pdivideLinear` | Finite raw-rational coefficient lists in increasing degree order; explicit synthetic division by a monic linear factor; trailing zeros are allowed. |
| `peqB` | Bounded coefficient comparison using raw-rational cross multiplication. |
| `RationalFunction`, `rfAdd`, `rfMul`, `rfDiff`, `rfCompose`, `rfEqB` | Pairs of polynomial lists; quotient-rule differentiation and equality after clearing denominators. |
| `rfEval?` | Returns `none` for invalid coefficients/input or a zero evaluated denominator; evaluation at a pole is never silently permitted. |
| `Q`, `R`, `s`, `V` | The paper's explicit product rational functions and quadratic telescoper multiplier. |
| `gamma`, `bGamma`, `qPartial`, `rPartial`, `pfAsRF` | Signed pole coefficients, both formulas for B, and explicit finite partial-fraction arrays. |
| `Theta`, `thetaShiftDifference`, `pfDerivativeAtOne`, `thetaShiftFormula` | The formal coefficient triple and both sides of its shift identity. |
| `vPartial`, `vLinearRemainder`, `vReconstruction` | Explicit multiplication of R's partial fractions by the quadratic s. The prospective linear term is retained until its zero value is proved. |
| `certificateLeft`, `certificateRight`, `telescoperLeft`, `telescoperRight` | Both sides of the exact polynomial and rational-function certificates. |
| `rPrimeAtSucc`, `finiteDerivativeSum`, `formalDerivativeSum?` | Derivatives from finite partial fractions and independently from the formal quotient rule, summed only at positive integer arguments. |
| `delta`, `epsilon`, `finitePFRight`, `E` | Shifted finite harmonic tails, the exact boundary remainder, and its integer majorant. |
| `auxiliaryM`, `auxiliaryT`, `squeezeChoice` | Exactly m=n+1+6K, T=M+m+2K(E(m)+1), and K=2*dx*dy for a rational gap. |
| `ratio`, `wronskian`, `finiteRatioTail`, `geometricSum` | The finite recurrence-ratio and geometric-sum quantities. |
| `multinomial`, `floorSum`, `floorDefect`, `valuation`, `factorialValuation` | Bounded integer computations used in the sparse denominator estimate. |

`AlgebraProofObligations` lists explicit identities between these objects.
It has no inhabitant. It is not an assumed partial-fraction or recurrence
library. All coefficient/denominator validity lemmas and the internal
derivations remain formalization work. The paired representations do not
quotient rational functions; semantic use of `rfEqB` requires nonzero
denominator polynomials. The actual product functions have those properties,
to be proved from their displayed factors.

The paper derives the Apéry recurrences by a rational-function certificate.
Implement polynomials as finite coefficient lists, with raw rational
coefficients or signed integer coefficients as appropriate. Required
operations are addition, multiplication, formal differentiation, degree
bounds, evaluation, and division by a monic linear factor. Each is a fixed
finite algorithm. Each equality is equality of explicit coefficient lists;
coefficientwise universal assertions are bounded loops.

For the product partial fractions, clear denominators and prove the
polynomial identity by evaluations at the finitely many distinct integer
nodes, with the factor theorem proved by coefficient recursion. The
root-count argument uses induction on the finite degree, with the root
list and all degree/divisibility assertions coded as bounded data.

The recurrence certificate is a fixed bivariate polynomial identity, so it
can be checked by coefficient normalization and then justified internally
from semiring/ring laws. Merely running a symbolic algebra package is a
diagnostic check; the Lean result must ultimately be a kernel-checked
coefficient identity, and its iPRA counterpart an internally derived one.

The formal functional used in the paper is a finite map from partial-fraction
coefficient arrays to triples of rational coefficients. Its shift identity
is proved by updating each pole index and using
`H_s(k+1)=H_s(k)+1/(k+1)^s`. Uniqueness of partial fractions can be proved
after clearing denominators and comparing the finite principal parts. There
is no need for analytic residues or the algebraic independence of zeta values.

The resulting recurrence is

```
(n+1)^3 y(n+1) + n^3 y(n-1)
    = (2n+1)(17n^2+17n+5) y(n),       n>=1,
```

for both `A` and `B`. The natural-number form for `A` uses addition rather
than truncated subtraction. The raw-fraction form for `B` uses `eqv`.

Use a quantifier-free induction invariant for the Casoratian:

```
(n+1)^3 [A(n) B(n+1) - A(n+1) B(n)] = 6.
```

This identity, its base values and the recurrences yield the finite
telescoping identity for `B(m)/A(m)-B(n)/A(n)`. All statements are equalities
of explicit rational computations with finite index parameters.

## 5. Integrality and growth

Termwise integrality of `D(n)^3B(n)` needs only the displayed formula for
`B`. A diagonal denominator is `r^3`; an off-diagonal denominator is
`(l-k)r^2`. Each divides `D(n)^3` because `r` and `l-k` lie between 1 and n.
One inner-loop invariant certifies the partial integer numerator for each
row, and an outer-loop invariant certifies the accumulated rows. This avoids
any unspecified cancellation theorem.

The lower bound `A(n)>=4^n` follows from the `k=n` term and
`choose(2n,n)>=2^n`. Monotonicity of `A` follows term by term from its binomial
definition. The recurrence then gives `A(n+1)>=32A(n)` for `n>=48`.
The last inequality reduces to

```
n^3 - 45n^2 - 69n - 27 >= 0.
```

At `n=48+t` its left side is
`t^3+99t^2+2523t+3573`, so coefficient positivity supplies a particularly
short internal proof. Iterate with the quantifier-free invariant
`32^j A(n) <= A(n+j)`. In particular,

```
32^n <= 32^48 A(n)            (n>=48).
```

For the denominator estimate formalize the paper's sparse factorial/
multinomial argument, with the exact target

```
D(42^k)^3 <= 28^(42^k).
```

All prime valuations, if used in that proof, are bounded counts of successive
divisibilities up to the displayed integer. The associated finite products
range only over integers up to that integer. Their primality tests and
factorization checks are bounded predicates. Induction on the outer scale
can use one Boolean conjunction encoding every divisor/valuation statement
required up to the current bound. The mathematical proof's actual recurrence
and exact numerical coefficient comparisons should be used verbatim; no
prime number theorem or unquantified asymptotic estimate belongs in this layer.

## 6. Finite estimates and error elimination

Prove finite harmonic tails by summing the cross-multiplied inequality

```
1/t^3 <= (1/2) [1/(t-1)^2 - 1/t^2]       (t>=2).
```

The signed finite partial-fraction identity from the paper gives a coarse
bound identifying the rational approximants. The Casoratian telescoping
identity, growth and finite geometric-sum bound sharpen it to

```
6/h(n) - A(n)/(2M^2)
    <= A(n) Z(M) - B(n)
    <= 1/A(n),                           n>=48, M>=1.
```

The paper proves a stronger upper constant; the specification records only
this weaker sufficient one. The proof must preserve one-sided signs when
comparing `Z(M)` with `Z(T)` for `T>=M`, so that a spurious positive tail term
is not retained on the upper bound.

The final manuscript removes every informal limit with the explicit
auxiliary choices

```
m = n+1+6K,
T = M+m+2K(E(m)+1).
```

For every positive integer K these make the coarse approximation error
smaller than 1/K. A rational squeeze then removes that final error: if
`x<=y+1/K` for every positive K and `x>y`, the difference is at least
`1/(dx*dy)`, where dx,dy are the positive raw denominators. Substitute
`K=2*dx*dy`, computed by `squeezeChoice`, for a contradiction. Negating the
inequality gives the corresponding lower-bound argument. This is decidable
rational order followed by one specified instantiation of a universal
hypothesis. It uses neither real completeness nor induction on an unbounded
quantified formula. The supplied finite-algebra definitions contain these
exact cutoffs, not an unspecified sufficiently-large parameter.

## 7. Explicit sparse witness budget

The final witness is `n(q)=42^(q+1)`, not a search for a sufficiently large n.
Combine the two growth bounds to obtain

```
q D(n)^3 / A(n) <= q * 2^240 * (7/8)^n.
```

The strict numerical certificate is

```
8^6 = 262144 > 235298 = 2*7^6.
```

For q>=1, prove `42^(q-1)>=q` and `q<=2^q` by quantifier-free induction.
It follows that

```
n(q) >= 1764q >= 6(q+243).
```

Raising the fixed strict certificate to the positive integer `q+243`, and
then using the displayed lower bound on n, gives

```
(8/7)^n > 2^(q+243).
```

After cross multiplication, the resulting budget is exactly

```
8*q*D(n(q))^3 < A(n(q)).
```

The proof also gives `n(q)>=48`. This is the `witnessBudget` field in the
specification. All exponent manipulations are integer identities, with no
logarithms or numerical floating-point comparisons.

## 8. Final decidable integer split

By integrality form

```
J = D(n)^3 [A(n)*p - q*B(n)] = Jpositive - Jnegative.
```

`integerFormPositive` and `integerFormNegative` compute these two coordinates.
Compare them using the decidable order of naturals. This produces either
`J<=0` or `J>=1`; no principle about deciding equality of real numbers is used.

If `J<=0`, then `A(n)*p/q<=B(n)`. With `N=A(n)h(n)`, the lower finite bound
gives

```
Z(N)-p/q >= 6/N - 1/(2N^2) > 1/N.
```

All denominators are positive. The last strict inequality follows from
`N>=1` after multiplication by `2N^2`.

If `J>=1`, then `A(n)*p/q-B(n)>=1/(qD(n)^3)`. The upper finite bound and
the witness budget give

```
p/q-Z(N) >= 1/(qD(n)^3 A(n)) - 1/A(n)^2
         > 7/A(n)^2.
```

Since `h(n)>=A(n)` and `A(n)>=1`, we have `N>=A(n)^2` and therefore

```
1/N + 1/(2N^2) <= 3/(2A(n)^2) < 7/A(n)^2.
```

This proves the second disjunct, including the zeta tail. Internal
disjunction introduction/elimination in `Prf` packages the two branches.
Boolean reflection then proves the checker equation. Three applications of
universal introduction yield `aperyFormula`.

## 9. Quantifier-free induction discipline

Every use of induction must display a finite invariant. Replace any bounded
quantifier over indices, coefficients, divisors or proof-array entries by a
primitive-recursive Boolean conjunction/disjunction. Bounds are explicit
parameters or computed PR terms. Multiple invariants can be combined by a
finite Boolean test. When a proof needs a statement for every smaller index,
carry that bounded collection in the induction state rather than invoking
strong induction on a formula with unrestricted quantifiers.

Rational expressions are encoded by their raw coordinates. Their equality
and order assertions are quantifier-free formulas after cross multiplication.
The case split in the final proof is likewise an arithmetic comparator.
Universal quantifiers occur in theorem statements and hypotheses and are
introduced or instantiated by intuitionistic logic; they are not induction
matrices.

One implementation route is direct `PTm` syntax and `PRA.qfInd`. Another is
the repository's scalar quotient `Q Γ`, extending its already certified
arithmetic and using `Q.exact` plus `pra_iff_teq`. In the second route any
semiring/ring instances used by normalization must have laws proved inside
the quotient; an instance borrowed from the standard natural numbers would
break the certification argument.

## 10. Build and audit

Use ProveIt commit `d72c8b24637e342816dc92d11bef337748683e51`, with Lean and
Mathlib 4.32.0. Add a small Lake library containing these modules and depending
on the existing `ConciseIPRA` library. First elaborate the specifications;
minor syntax or termination-proof adjustments may be needed because they
have not been compiled. Check small arithmetic instances separately from
the huge final witness, whose literal evaluation is not intended.

For a completed implementation, inspect the final theorem's full type and
`#print axioms` output. Its type must be a `Prf PRAAx` statement, with no
additional arithmetic theory appended to `PRAAx`. There must be no `sorryAx`
or custom axiom standing in for a polynomial, divisibility, growth, tail or
separation lemma. A metatheoretic use of quotient soundness in a verified
internal-derivation construction is distinct from adding a rule to iPRA.

Finally, an optional external Mathlib theorem can identify `Z(M)` with the
usual real zeta series at 3 and derive `Irrational ζ(3)`. That bridge explains
the conventional theorem but does not replace the internal finite theorem.
