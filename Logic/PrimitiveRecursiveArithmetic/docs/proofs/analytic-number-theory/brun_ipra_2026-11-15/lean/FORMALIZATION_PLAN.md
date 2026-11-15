# Lean formalization plan

## Status and scope

The accompanying `BrunSpecification.lean` gives executable bounded definitions,
a denominator-cleared arithmetic target, and candidate conditional assembly
proofs, uncompiled, from the finite dyadic tail bound to the explicit Cauchy
estimate. It introduces no `axiom` or `sorry`. It does **not** prove the sieve bound, the arithmetic
target, or their derivability in iPRA.

The file has **not been compiled** in the authoring environment: `lean` and
`lake` were unavailable on PATH, and the usual shallow installation locations
did not contain a toolchain. The intended compatibility target is Lean and
Mathlib v4.32.0, as pinned by the inspected ProveIt snapshot.

The human-readable paper supplies the mathematical proof. Completion of the
formalization requires both the semantic finite arithmetic layer and the
deeply embedded `PRAAx` derivation below. A Mathlib theorem about `Nat` or
`Rat`, by itself, is not a proof that the statement is provable in iPRA.

## 1. Fixed conventions and target

- A pair is indexed by its smaller prime $p$; both $1/p$ and $1/(p+2)$
  are included. Thus $1/5$ occurs twice.
- `brunPartial N` sums over $p<N$.
- $C=2^{11}=2048$.
- The finite counting target is
  $k^2 T(2^k)\le C2^k$ for $k\ge1$.
- The dyadic tail target is
  $0\le B(L)-B(2^m)\le4C/m$ for $m\ge1$, $L\ge2^m$.
- $e(q)=2^{q+13}$, $N(q)=2^{e(q)}$.
- The final Cauchy target is
  $M,L\ge N(q)\Longrightarrow |B(M)-B(L)|\le2^{-q}$.

For the object-language result, use one positive natural denominator:
$$
 D(B)=(B+1)!,\qquad
 \mathcal A(A,B)=\sum_{A\le p<B}\chi_{\rm twin}(p)
          \left(D(B)\mathbin{\rm div}p+D(B)\mathbin{\rm div}(p+2)\right).
$$
For each contributing term, $2\le p<B$, so $p,p+2\le B+1$ and both
divisions are exact. The final matrix is
$$
 N(q)\le A\le B\quad\Longrightarrow\quad2^q \mathcal A(A,B)\le D(B).
$$
This is `ArithmeticBrunClaim`. Replace all relations by primitive recursive
Boolean characteristics to obtain a quantifier-free equation with three
free variables $q,A,B$, then universally close it. No real-number datatype
occurs in this internal theorem.

## 2. Recommended semantic modules

| Module | Required result and implementation |
| --- | --- |
| `Brun/FiniteArithmetic` | Bounded trial division, squarefreeness, prime support, finite factorization, quotient/remainder, exact rational encodings. |
| `Brun/Residues` | For squarefree $d$, count roots of $x(x+2)=0\pmod d$ by an explicit Chinese remainder construction; each residue contributes $X/d$ with error at most 1. |
| `Brun/SelbergIdentity` | Expand the finite square majorant and diagonalize the quadratic form by divisor rearrangement. Prove the finite optimal weights and their size bound. |
| `Brun/DenominatorLower` | Formalize the paper's elementary lower bound for the sieve normalization $G(z)$, using finite harmonic sums and finite products only. |
| `Brun/DyadicCount` | Instantiate $t=\lfloor k/10\rfloor$ and $z=2^{2t}$, handle the small-prime exception uniformly, and prove $k^2T(2^k)\le2^{11}2^k$. |
| `Brun/Tail` | Partition the finite interval $2^m\le p<L$ into dyadic blocks, apply the count bound, and telescope $1/[j(j+1)]$. |
| `Brun/Cauchy` | Compile and check the candidate enclosure proof in `BrunSpecification.lean`, then apply it and prove the denominator-cleared formulation agrees with the rational one. |
| `Brun/IPRA/Codes` | Build actual `PR` syntax codes for every operation used above. |
| `Brun/IPRA/Derivation` | Construct a `Prf PRAAx` derivation of the universally closed arithmetic target. |
| `Brun/IPRA/Native` | Transfer the completed derivation to the scalar and native systems with the inspected faithful interpretation theorems. |

No module may import a classical analytic Brun theorem and call that the
iPRA proof. The finite rational sieve is what is to be formalized.

## 3. Finite arithmetic interfaces

### 3.1 Bounded primality and factorization

The supplied `primeB` scans `List.range n`. Prove

```lean
theorem primeB_correct (n : ℕ) :
    primeB n = true ↔ Nat.Prime n
```

Then prove that `twinB` matches the mathematical twin predicate.
For internalization, use a bounded least-divisor search and a quotient trace
with fuel $n$, rather than an unbounded factorization procedure. Each step
either stays at 1 or divides by a prime and strictly reduces the remaining
positive integer. Record its selected factors and reconstruction invariant
as bounded vectors of naturals. This gives squarefree support, prime
exponents, Möbius signs, and divisor enumeration as primitive recursive data.

### 3.2 Finite rationals

A simple internal representation is an integer numerator represented by
a pair of naturals and a positive natural denominator. Addition and
multiplication need no reduction to lowest terms. Equality and order are
cross-multiplied relations. Normalize signs, if desired, by comparison and
truncated subtraction; gcd reduction is optional.

Use a common denominator before every induction on a finite sum or product.
This makes nonnegativity and each invariant a primitive recursive equality
or inequality. The semantic `Rat` presentation is for readability; internal
proofs concern encoded pairs and cross products.

### 3.3 Divisors and Chinese remainders

Every divisor scan is bounded by its argument. Prove root counts for a
prime first: one forbidden class for $p=2$, two for odd $p$.
For coprime $a,b$, construct the CRT solution by a search below $ab$;
the search is bounded, and existence is proved by the finite permutation
of residues of multiplication by a unit. This avoids relying on a global
existential choice function.

The congruence-class interval count follows from quotient/remainder.
Keep the endpoint convention fixed, e.g. $1\le n\le X$, and prove a
single lemma of absolute error at most one. All later root-count errors
are finite sums of this lemma.

### 3.4 Sieve identity

Use a finite divisor set, not arbitrary `Set ℕ`. The two necessary identities
are finite rearrangements:

1. The square majorant expands to a sum over pairs $d,e\le z$.
2. The kernel $g(\operatorname{lcm}(d,e))$ factors through
   $g(d)g(e)/g(\gcd(d,e))$, whose last reciprocal has a finite divisor
   expansion.

Prove these algebraically before imposing order estimates. The optimal
weights are explicit finite rational sums; they are not selected by a
compactness or minimization theorem. Verify their $\lambda_1=1$
normalization by Möbius cancellation. The paper's crude polynomial error
bound avoids any analytic estimate for the individual weights.

The explicit uniform count calculation uses $t=\lfloor k/10\rfloor$,
$z=2^{2t}$ and the inequalities $G(z)\ge(t+2)^2/12$,
$(t+1)^2\le4^t$, $k<10(t+1)$, and $2^k\ge2^{10t}$.
These give a main term at most $1200\cdot2^k$ after multiplication
by $k^2$, and combined exceptional/error terms at most $200\cdot2^k$.
Thus $k^2 T(2^k)\le1400\cdot2^k\le2048\cdot2^k$;
there is no asymptotic threshold or unproved small-case assertion.

### 3.5 Dyadic tail

For $2^j\le p<2^{j+1}$, each pair contributes at most $2/2^j$, and
the number of pairs is at most $T(2^{j+1})$. Hence its block contribution
is at most $4C/(j+1)^2$. For $j\ge1$,

$$
 \frac1{(j+1)^2}\le\frac1{j(j+1)}
 =\frac1j-\frac1{j+1}.
$$

Prove the corresponding finite sum inequality by induction on the number
of blocks, not by invoking `Summable` or an infinite-series theorem.
Given a finite endpoint $L$, use the bounded binary length of $L$ as the
last block index. Prove all partial sums, including an incomplete last block,
are dominated by the full finite block sum.

## 4. Constructing the actual iPRA proof

### 4.1 Existing definitions to reuse

The inspected source
`Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/PR.lean`
defines:

```lean
inductive PR : ℕ → Type
  | zero : PR 0
  | succ : PR 1
  | proj {k : ℕ} (i : Fin k) : PR k
  | comp {m k : ℕ} (f : PR m) (gs : Fin m → PR k) : PR k
  | prec {k : ℕ} (f : PR k) (g : PR (k + 2)) : PR (k + 1)
```

The axiom family `PRAAx` contains defining equations, successor separation,
successor injectivity, and induction only for formulas carrying an
`Fm.QF` proof. The derived rule is `PRA.qfInd`.

Define additions, multiplication, division with a total zero convention,
bounded folds, powers, factorials, prime/twin tests, coded vectors,
the cutoff, and the integer tail numerator as explicit `PR` syntax trees.
For each, provide correctness of its defining equations in `PRAAx`.
An external proof that a Lean function is primitive recursive does not by
itself produce these object-language derivations.

### 4.2 The final formula and derivation

Build `brunMatrix : Fm PTm 3` as a Boolean equation whose free variables are
$q,A,B$. For example, the Boolean is 1 exactly when either an antecedent
$N(q)\le A\le B$ is false, or $2^q\mathcal A(A,B)\le D(B)$ is true.
Then `brunMatrix.QF` follows immediately from its syntactic construction.

The completion target is schematically:

```lean
def brunFormula : Fm PTm 0 := Fm.all (Fm.all (Fm.all brunMatrix))

theorem brunPRA :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] brunFormula := by
  -- Explicit derivation assembled from the finite arithmetic lemmas.
  -- The final delivered proof must have no placeholders.
```

This signature is a roadmap, not a declaration in the supplied file.

### 4.3 Induction audit

All induction invariants are finite arithmetic facts with explicit
parameters. Bounded quantifiers in the informal proof must be compiled
to bounded Boolean products/sums before applying `PRA.qfInd`.

| Mathematical step | Induction variable | Internal invariant |
| --- | --- | --- |
| Bounded division/factorization | Fuel or divisor index | Current remainder, selected factors, product reconstruction and bounded minimality checks |
| CRT | Residue index / finite prime list | Injective image of a bounded residue list and reconstruction modulo the product |
| Square and product expansions | List length | Equality of encoded finite sums |
| Möbius cancellation | Prime support length | Divisor-sum value (0) or (1) |
| Sieve bounds | Divisor or summation index | Cross-multiplied partial-sum bound |
| Harmonic comparison | Dyadic block index | Rational lower bound with positive denominator |
| Dyadic count | (k) or fixed bounded remainder classes | Integer polynomial/exponential inequalities |
| Tail | Number of dyadic blocks | Telescoping upper bound |
| Exact denominator | Summation index | Divisibility and common numerator equality |

Structural induction over external Lean syntax may occur in construction
of proof-producing macros. It must not be confused with unbounded
arithmetical induction in the object theory. Any use of semantic
`Nat.rec` with a formula containing unbounded number quantifiers needs a
separate reduction to a quantifier-free invariant before it is accepted
as part of the iPRA argument.

### 4.4 Faithful transfer already present

Once `brunPRA` exists, the inspected sources provide:

- `FromPRA.interp : Interp PRAAx TeqAx`, with every axiom translation proved;
- `pra_iff_teq`, the faithful converse and forward translation;
- `pra_iff_native`, the native scalar core translation.

The scalar proof is obtained by `FromPRA.interp.sound brunPRA`.
For the native proof, apply `pra_iff_native.mp` to `brunPRA`; the result
is a derivation of `NFm.ofPRA brunFormula` in the empty native context.
No new consistency or conservativity theorem is required.

## 5. Integration and completion checks

1. In the pinned ProveIt workspace add a `BrunIPRA` library with
   `srcDir = "NumberTheory/Brun/Lean"`, or put these modules under an agreed
   existing library; copy the specification after compiling it.
2. Build the finite semantic modules.
3. Build the `PR` encodings and syntactic derivations.
4. Build the scalar/native corollaries.
5. Audit absence of `sorryAx` in the final theorem with `#print axioms`.
6. Inspect every internal induction application for its `Fm.QF` witness.
7. Check that the final theorem's type is `Prf PRAAx ...`, not only
   `ArithmeticBrunClaim` interpreted in Lean.
8. Inspect any use of classical axioms in the metatheory separately from
   the object-language logic. Classical reasoning about proof syntax does
   not itself add excluded middle to iPRA, but it must not select
   nonconstructive numerical witnesses.

The existing README reports that its foundational modules build without
`sorry`, with the `T_eq\equiv\mathrm{iPRA}` part depending only on
`propext` and `Quot.sound`. This is an upstream report, not a rebuild
performed for the present package.

