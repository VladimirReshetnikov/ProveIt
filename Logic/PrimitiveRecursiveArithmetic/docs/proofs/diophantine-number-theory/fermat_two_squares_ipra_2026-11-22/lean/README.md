# Lean formalization plan and executable specification

## Exact status

This directory supplies an **uncompiled Lean 4 outline**, not a completed
formal proof. No Lean or Lake executable is installed in the preparation
environment. The locations `/root/.elan/bin` and `/home/agent/.elan/bin` are also
absent. `validation_status.json` records these observations.

The files contain no proof holes or global declarations of unproved facts.
Nevertheless, `ArithmeticContracts` is an **explicit, unimplemented hypothesis**
of the assembly theorems. Even a successful build of these files would establish
only that the contracts imply the advertised conclusion. It would not prove that
the contracts have been supplied, and it would not construct a derivation in
iPRA. The accompanying mathematical report proves the contracts informally and
explains why their proof methods fit iPRA.

The toolchain target is `leanprover/lean4:v4.32.0`, matching the inspected ProveIt
commit. This is a version pin for future checking, not a claim that this package
was checked with that version.

## Contents

| File | Purpose |
| --- | --- |
| `FermatIPRA/Program.lean` | Total bounded algorithms, their mathematical predicates, and a proof-carrying answer checker. |
| `FermatIPRA/Contracts.lean` | Exact unimplemented mathematical obligations and conditional theorem assembly. |
| `FermatIPRA/Examples.lean` | Reproducible evaluation commands; not executed here. |
| `FermatIPRA.lean` | Library entry point. |
| `lakefile.toml`, `lean-toolchain` | Dependency-free Lean 4 package configuration. |
| `validation_status.json` | Machine-readable distinction between outline and checked proof. |

After installing the pinned Lean toolchain, run from this directory:

```bash
lake build
lake env lean FermatIPRA/Examples.lean
```

For a later completed implementation, also inspect dependencies with
`#print axioms FermatIPRA.fermat_from_contracts`. That inspection does not remove
the explicit `ArithmeticContracts` argument. Completion requires implementing
that argument and, separately, obtaining the object-theory endpoint below.

## Definitions and program

All numerical definitions use natural numbers. Signed values are unnecessary in
the algorithm itself: the difference of two coordinates is converted to its
absolute value by `absDiff a b = (a-b)+(b-a)`, using truncated subtraction.

1. `allBelow test n` computes the conjunction of `test 0,...,test (n-1)`.
   `primeB p` tests `2 <= p` and the absence of a divisor `d` with `2 <= d < p`.
   `Prime p` abbreviates `primeB p = true`.
2. `factorialMod p n` computes `n! mod p`, reducing at each multiplication.
   `root p` is `factorialMod p ((p-1)/2)`.
3. `floorSqrt` uses the recurrence
   `h(0)=0` and
   `h(n+1)=h(n)+1` exactly when `(h(n)+1)^2=n+1`.
   It matches the recurrence of ProveIt's `isqrtF`.
4. `side p = floorSqrt p + 1`. Point `i` has coordinates
   `gridX p i = i % side p` and `gridY p i = i / side p`.
   `label p t i = (gridX p i + t*gridY p i) % p`.
5. `firstHit test N` searches precisely the indices below `N`, returning the
   first hit or `none`. `collisionIndices p t` applies it with the bound
   `(p+1)^2`. Code `k` represents the pair
   `(k/(p+1), k%(p+1))`. A hit satisfies `i<j<=p` and equal labels.
6. `differencePair` returns the absolute coordinate differences. `gridWitness`
   uses the computed root and the computed collision. `witness 2=(1,1)`;
   every other input uses `gridWitness`.

Every call is total, including inputs outside the theorem's hypotheses. Failed
collision search returns the default pair `(0,0)`; this does not interfere with
the theorem because the finite pigeonhole proof establishes successful search
under its assumptions. The algorithm is a straightforward specification. It
does not promise optimal running time or eliminate repeated evaluation of
helper functions.

`certify p` checks the returned answer and returns a subtype containing its
equality proof when the equality holds. This is a checker for an individual
candidate. A checker by itself does not establish that the algorithm succeeds
for all primes of the required congruence class.

## The seven remaining arithmetic contracts

The report supplies human-readable proofs. Their Lean implementations remain
to be written; the interfaces in `ArithmeticContracts` identify exactly what is
missing.

### 1. `wilsonRoot`

For `Prime p` and `p % 4 = 1`, prove
`(root p * root p + 1) % p = 0`.

Use bounded modular inverse search on `1,...,p-1`. Extended Euclid proves that
each search succeeds. Prime cancellation proves inverse uniqueness, so inverse
is an involution. Its only fixed points are `1` and `p-1`, because
`x^2-1=(x-1)(x+1)` and a prime dividing a product divides a factor. Pair all
other residues; each pair has product one. This proves Wilson's congruence.

Put `m=(p-1)/2`. The factors `m+1,...,p-1` are the negatives, in reverse order,
of `1,...,m`. Therefore `(p-1)! = (-1)^m(m!)^2 (mod p)`. Here `m` is even, so
Wilson gives the required root. The recursive modular factorial agrees with
the ordinary factorial modulo `p` by a quantifier-free induction.

The finite pairing argument needs its own product derivation. Importing a
finite involution theorem or Fermat's little theorem does not by itself fill
this contract.

### 2. `squareBounds`

Prove `h^2<p<(h+1)^2` for `h=floorSqrt p` and prime `p`.

The nonstrict lower bound and strict upper bound follow by induction on the
displayed recurrence. The lower bound is strict for a prime: if `h^2=p`, then
`h` divides `p`; primality forces `h=1` or `h=p`, both contradicting `p>=2`.
This is the only use of primality in the geometric grid stage.

### 3. `collisionFound`

For `p>=2`, prove that the search returns `i<j<=p` with equal labels.

There are `p+1` indices and only `p` possible residues. Establish the finite
pigeonhole principle by occurrence counts, or instantiate the existing
object-theory theorem cited below. The returned mathematical collision has
code `i*(p+1)+j < (p+1)^2`; bounded-search correctness then shows that
`firstHit` returns a hit, whether or not it returns that particular collision.

The finite search proof uses a primitive-recursive Boolean accumulator for
"no earlier hit". No least-number principle for arbitrary formulas is needed.

### 4. `differenceBounds`

From `SquareBounds p` and a collision, prove
`0 < differenceNorm p i j < 2*p`.

Since `i,j<=p<(h+1)^2`, each coordinate lies in `0,...,h`. Equality of both
coordinate pairs would imply `i=j` by the division equation, contrary to
`i<j`. Thus the norm is positive. Each absolute difference is at most `h`, so
the norm is at most `2*h^2`, which is strictly smaller than `2*p`.

### 5. `differenceDivisible`

Let `x` and `y` be the signed coordinate differences. Equal labels give
`p | (x+t*y)`. The polynomial identity

```text
x*x + y*y = (x+t*y)*(x-t*y) + (t*t+1)*y*y
```

and the root congruence imply `p | (x*x+y*y)`. Squaring removes signs, giving
exactly the natural `differenceNorm`.

In ordinary Lean, this can use integer casts and the ring identity. For an
object-theory derivation, use the repository's signed-pair arithmetic and
`Q.exact`, or split into the four decidable coordinate-order cases and prove
the corresponding natural-number identity. A use of Lean integers in the
metatheory is not an additional integer sort in iPRA.

### 6. `shortMultiple`

If `0<p`, `0<n<2*p`, and `n%p=0`, prove `n=p`.
The division equation gives `n=p*q`. Positivity forces `q>=1`; the upper bound
forces `q<2`; hence `q=1`. Only elementary ordered arithmetic is used.

### 7. `converse`

Squares are `0` or `1` modulo `4`. If the prime `p` is even, its divisor `2`
forces `p=2`. Otherwise `p` is odd, and a sum of two squares can be odd only
when exactly one square has residue `1`; the sum then has residue `1`.
All cases are decided by finite remainder calculations.

## Primitive-recursive encoding and iPRA induction audit

Lean's use of `Nat`, `Bool`, `Option Nat`, and pairs is presentation-level
notation. For a first-order iPRA program, use the following explicit encodings.

- Booleans are the natural numbers `0,1`, with primitive-recursive Boolean
  operations and characteristic functions for equality and order.
- `none` is `0`, and `some k` is `k+1`. Thus the search result and its default
  projection are primitive recursive.
- A fixed pair can be encoded by Cantor's polynomial pairing
  `(a+b)*(a+b+1)/2+b`. Its projections are bounded searches at most the code.
  Alternatively, define the two output components as separate PR functions;
  no numerical pair encoding is then needed for the witness theorem.
- Division and remainder are total primitive-recursive functions. The
  correctness lemmas use a positive divisor; the total definitions at divisor
  zero only specify behavior outside those hypotheses.
- The higher-order `test` parameter in `allBelow` and `firstHit` is specialized
  to each displayed primitive-recursive predicate. iPRA has no quantification
  over functions in this construction.

For signed intermediate algebra, one convenient natural-number encoding is
`enc(z)=2*z` for `z>=0`, and `enc(z)=2*abs(z)-1` for `z<0`.
For code `c`, the positive part is `c/2` if `c` is even and `0` otherwise; the
negative part is `(c+1)/2` if `c` is odd and `0` otherwise. Encode a difference
`u-v` by `2*(u-v)` when `v<=u`, and by `2*(v-u)-1` otherwise. Addition,
negation, and multiplication follow by these part formulas and are primitive
recursive. These codes are needed only if the signed proof route is chosen;
the executable grid program already uses natural operations alone.

The induction formulas for factorial congruence, root bounds, running products,
bounded search, and occurrence counts are equations or inequalities between PR
terms, combined by propositional connectives. A bounded universal assertion is
first compiled to an equation saying its PR conjunction bit is `1`. Calling a
formula "bounded" is not enough to make it syntactically quantifier free.
Prime assumptions can remain in the fixed proof context instead of being
inserted into an induction invariant.

The ordinary Lean inductive proofs and conditional theorem assembly are a useful
development layer. The final iPRA proof must still be produced explicitly in
the repository's proof datatype; arbitrary reflection from a true statement
about Lean's `Nat` is not part of the construction.

## Concrete ProveIt integration plan

The inspected reference is commit
[`65b76a5b8aa87ecad4103c2d287eff5660d3c84c`](https://github.com/VladimirReshetnikov/ProveIt/commit/65b76a5b8aa87ecad4103c2d287eff5660d3c84c).
The source tree is
[`Logic/PrimitiveRecursiveArithmetic/Derivations/Lean`](https://github.com/VladimirReshetnikov/ProveIt/tree/65b76a5b8aa87ecad4103c2d287eff5660d3c84c/Logic/PrimitiveRecursiveArithmetic/Derivations/Lean).
These interfaces were read from the pinned source, but their compilation was
not rerun in this task.

| Existing module | Exact relevant interface | Integration step |
| --- | --- | --- |
| `IPRADerivations.Core.Division` | `remF`, `quoF`, `div_mod`, `div_mod_unique` | Arithmetic of labels, coordinate encoding, and exact quotient. |
| `IPRADerivations.Core.Pairing` | `isqrtF`, `isqrt_le`, `lt_isqrt_succ_sq`, `isqrt_unique` | Replace the presentation-level `floorSqrt` by the same object PR recurrence. |
| `IPRADerivations.Core.Pigeonhole` | `Pigeonhole.phpI`, `phpJ`, `pigeonhole` | Obtain collision witnesses in the object theory. |
| `IPRADerivations.Core.Search` | `Search.mu`, `search_spec`, `search_found`, `search_minimal` | Compile the explicit first-hit search, or transfer the existence of the library collision to this search. |
| `IPRADerivations.Core.EuclidLemma` | `gcd_prime`, `bezout_at`, `euclid_lemma_at` | Modular inverses and fixed-point classification for Wilson. |
| `IPRADerivations.Core.Permutation` | `Permutation.prod_perm` | Reindex finite products in Wilson's argument. |
| `IPRADerivations.Core.ProdLemmas` | `prod_congr_bounded`, `prod_one`, `prod_const_of` | Product identities and modular-factorial comparison. |
| `IPRADerivations.Core.Quotient` | `Q.exact`, `Q.sound` | Produce object derivations of polynomial identities. |
| `IPRADerivations.Core.IntCertificates` | `nn_zsq` and inequality-certificate lemmas | Optional signed-pair proof of the norm identity and bounds. |
| `IPRADerivations.Foundations.BoundedFormulas` | `BF`, `bitAt`, `bf_reflect`, `bf_choice` | Replace bounded assertions by PR bits before quantifier-free induction. |

The actual pigeonhole interface takes a body `S : PTm 2` and the premise
`Permutation.rangeAll S K x`, meaning `S(i,x)<K` for every `i`. Put `K=p`,
encode the parameters `(p,t,h)` in `x`, and make the body the final remainder
of `u(i)+t*v(i)` modulo `p`. The final remainder makes the range premise true
for **all** indices, not only `i<=p`. The theorem returns
`phpI < phpJ <= p` and equal labels. Division by `h+1` is justified separately.

An explicit primality bridge is also required. The repository's `prime p`
formula quantifies over candidate divisors, whereas the presentation here uses
the equation `primeB p=true`. Use the division theorem to prove, for `d>0`,
`d | p` if and only if `p % d = 0`. Restrict the divisor test to `2<=d<p`,
compile its bounded conjunction to a PR bit, and derive both directions between
the repository formula and this bit equation. If a bounded divisibility witness
is needed, the quotient can be bounded by `p` when `d>=1`. Do not assume the
two primality presentations are definitionally identical.

For the simplest object proof, define new witness functions directly from
`phpI` and `phpJ`; they need not return exactly the same pair as this package's
lexicographic search. Both satisfy the same correctness specification. To
identify the exact executable pair, additionally instantiate `Search` with
the pair-code predicate and prove the first-hit specification.

The new files should live in `IPRADerivations`, for example a Wilson module and
a `TwoSquares` module. They must return `Prf PRAAx Γ φ` terms. In the existing
namespaces, the desired witnessed endpoint has this **schematic** form after
defining the new PR terms `A` and `B`:

```lean
-- Interface sketch, not a declaration included in the compiled package:
theorem twoSquares_at {p : PTm n}
    (hp : Γ ⊢[PRAAx] prime p)
    (hm : Γ ⊢[PRAAx] rem p (PTm.num 4) ≐ one) :
    Γ ⊢[PRAAx] (A p * A p + B p * B p ≐ p)
```

The `p=2` case is a separate one-line arithmetic derivation. Natural deduction
then introduces the disjunction, existential witnesses, and universal
quantifier to obtain the full prime equivalence with empty context and scope
zero. `IPRABridge.conciseToStandard` can transport the completed ordinary
ConciseIPRA derivation to the repository's standard iPRA foundation. The bridge
does not discharge any missing arithmetic lemma.

## Completion checklist

1. Elaborate these files with the pinned toolchain and fix any version-specific
   syntax or library-name issues.
2. Prove the seven contracts in the ordinary Lean development and instantiate
   `ArithmeticContracts`; confirm evaluations and dependency reports.
3. Implement the PR term constructors for the new Wilson and grid witness
   functions in `IPRADerivations`.
4. Construct each arithmetic derivation using the explicit existing interfaces,
   keeping the QF induction audit visible.
5. Export the closed object theorem and, if desired, transport it through
   `IPRABridge`.

Steps 2 and 4 are mathematical formalization work; a successful build of the
current conditional outline would not complete either of them.
