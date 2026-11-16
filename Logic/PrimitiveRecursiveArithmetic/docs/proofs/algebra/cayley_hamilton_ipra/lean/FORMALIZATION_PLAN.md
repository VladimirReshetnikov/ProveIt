# Lean and iPRA formalization plan

## Delivery status and separation of claims

The mathematical manuscript gives a finite constructive proof intended to be
formalizable in intuitionistic primitive recursive arithmetic (iPRA).
The accompanying Lean sources are outlines, not a completed machine-checked
formalization. No Lean executable was available in the delivery environment,
and neither the sources nor the upstream ProveIt project were compiled here.

There are two separate Lean tasks.

1. **Host mathematics.** Matrices, commutative rings and polynomials as Lean
   types. Mathlib already proves Cayley--Hamilton. The file
   `HostReference.lean` gives small reference targets using that theorem.
2. **Object arithmetic.** An explicit term of
   `LeanProofs.ConciseIPRA.Prf PRAAx [] phi`, where `phi` is a first-order
   formula over primitive recursive numerical operations.
   `ObjectLanguageTargets.lean` specifies the final interface. The development
   must construct the checker program and the derivation; it does not receive
   either from Mathlib.

A host theorem that a numerical predicate is true is not, by itself, a proof
that iPRA derives that predicate. Likewise, the existing bi-interpretability
theorems transfer an existing iPRA derivation, not arbitrary Lean truth.

## Exact upstream interface inspected

Repository: VladimirReshetnikov/ProveIt.

Inspected commit:
`73e6a339db7c72c6b13259059a8345b24385f6e3`.

Root `lean-toolchain`: `leanprover/lean4:v4.32.0`.
Root `lakefile.toml` requires Mathlib `v4.32.0` and declares:

```toml
[[lean_lib]]
name = "ConciseIPRA"
srcDir = "Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean"
```

The following files were read directly. Their blob hashes and source URLs are
recorded in `proveit_sources_audit.json`.

| File under ConciseIPRA/Lean/ConciseIPRA/ | Interface used |
| --- | --- |
| `Syntax.lean` | `Syn`, `Fm`, substitution, `Fm.QF` |
| `Deduction.lean` | `Prf`, intuitionistic natural deduction, equality, substitution and weakening |
| `PR.lean` | `PR`, `PTm`, `PRAAx`, `PRA.qfInd` |
| `BiInterpretation.lean` | `pra_iff_teq`, `teq_iff_pra` |
| `NativeBiInterpretation.lean` | `NFm.ofPRA`, `pra_iff_native` |

All these names belong to the namespace
`LeanProofs.ConciseIPRA`.

The syntax `PR k` has precisely the constructors:

```lean
inductive PR : ℕ → Type
  | zero : PR 0
  | succ : PR 1
  | proj {k : ℕ} (i : Fin k) : PR k
  | comp {m k : ℕ} (f : PR m) (gs : Fin m → PR k) : PR k
  | prec {k : ℕ} (f : PR k) (g : PR (k + 2)) : PR (k + 1)
```

Recursion uses its first argument:

- `prec f g (0, xs) = f xs`;
- `prec f g (S y, xs) = g (y, prec f g (y, xs), xs)`.

Terms have constructors `PTm.var` and `PTm.app`. The axioms `PRAAx`
are defining equations for these PR symbols, successor nonzeroness and
injectivity, and induction for quantifier-free formulas.

The actual induction wrapper is `PRA.qfInd`:

```lean
theorem PRA.qfInd
    (phi : Fm PTm (n + 1)) (hphi : phi.QF)
    (h0 : Prf PRAAx Gamma (phi.subst (Syn.inst PTm.zero)))
    (hS : Prf PRAAx (phi :: Gamma.map Fm.shift)
             (phi.subst (Syn.repl (PTm.succ (Syn.var 0))))) :
    Prf PRAAx Gamma (Fm.all phi)
```

Thus induction does not silently permit quantified matrix invariants.
The invariants below must first be represented by a Boolean PR computation
and the quantifier-free equation that its value is 1.

The bridge, after the proof is supplied, is:

```lean
pra_iff_native :
  Prf PRAAx Gamma phi ↔
    NPrf (Gamma.map NFm.ofPRA) (NFm.ofPRA phi)
```

The repository's `docs/proofs/README.md` explicitly describes incoming
research packets as delivered and unchecked. This packet does not use those
claims as a verified mathematical library. The much smaller syntactic
interface above is sufficient for the planned internal proof.

## Exact numerical objects

### Lists and signed integers

Use 0 for the empty list and

    cons(a,b) = 2^a (2b+1)

for a nonempty list with head `a` and tail `b`.
For a positive code `z`, the head is the exponent of 2 dividing `z`,
found by searching only exponents at most `z`; the tail is
`(z / 2^head - 1)/2`. Define head and tail of 0 to be 0. All searches are
bounded. An array is a length plus such a list code, or, where its dimensions
determine its length, just the list code. Reading slot `i` means iterating
tail `i` times and reading head; writing slot `i` reconstructs at most the
given array length.

Encode an integer `z` by `2z` if `z ≥ 0`, and by `2(-z)-1` if `z < 0`.
The value 0 has code 0. Implement addition, negation and multiplication by
cases on parity and comparisons of magnitudes. All branch conditions are
decidable numerical predicates. Equivalently one can first use pairs of
naturals and then a PR normalization; the canonical signed code makes
equality literal equality of natural numbers.

Needed internal lemmas: head/tail of cons, bounded lookup/update, extensional
array equality, associativity/commutativity/distributivity of the signed
operations, additive inverses, and the finite sum/product recursion rules.
Each proof is ordinary induction on a natural counter with a quantifier-free
invariant. Multi-entry assertions are packed as described below.

### Generic polynomial coefficients

For the main theorem of dimension `n`, use

    v = n²,
    d = n,
    L = (d+1)^v.

The variable `x_ij` has index `i*n+j`.
A monomial exponent vector `e=(e_0,...,e_(v-1))`, with `0 ≤ e_i ≤ d`,
has index `sum_i e_i*(d+1)^i`. A polynomial is a dense array of `L`
signed integer coefficients. The coefficient at exponent vector `e` is
read at that index. All digits, indices, array accesses and coefficient
arithmetic are PR.

Polynomial addition and negation are coordinatewise. Polynomial
multiplication is bounded convolution over pairs of indices less than
`L`; a pair contributes only if every component of the sum of its two
exponent vectors is at most `d`. This is multiplication in the truncated
ring `Z[x_0,...,x_(v-1)]/(x_i^(d+1))`.

To recover a genuine polynomial identity, prove the degree support lemma:
every polynomial occurring in the characteristic residual and in the
adjugate telescoping argument has total degree at most `n`.
Consequently no genuine coefficient is lost by truncation. In particular,

- a generic matrix entry has degree 1;
- a coefficient `c_k` of `det(tI-X)` has degree `n-k`;
- a coefficient `B_k` of `adj(tI-X)` has degree `n-1-k`;
- an entry of `X^r` has degree at most `r`;
- a term `c_k X^k` or `X^(k+1) B_k` has degree at most `n`.

The characteristic variable `t` is handled as a second finite array of
`n+1` generic polynomials, so its coefficient extraction is literal lookup.
A cofactor has length at most `n`. There is no use of an infinite power
series object.

### Matrices and determinant

A square matrix of size `n` is a row-major array of `n²` entries.
The identity has entry 1 when `i=j` and entry 0 otherwise.
Matrix product is

    mul(A,B)[i,j] = sum_(k<n) A[i,k] * B[k,j].

A candidate map of `{0,...,n-1}` to itself is a length-`n` base-`n`
digit vector. For `n>0), enumerate the `n^n` candidate maps and accept
exactly those with pairwise distinct digits. The `n=0` case has one empty
permutation, so the determinant is 1. This convention avoids treating
`0^0` or an empty enumeration informally.

The parity is the parity of

    sum_(i<j<n) [sigma(i) > sigma(j)].

Define the determinant by the signed sum of the products
`prod_(i<n) A[i,sigma(i)]`.
No unbounded search, finite-set choice, or arbitrary enumeration oracle is
used. Enumerating `n!` permutations is an optimization, not a logical
requirement.

Define a cofactor by deleting the specified row and column using the
increasing index maps skipping them; define `adj(A)[i,j]` as the cofactor
with row `j` and column `i`.

Define matrix powers by primitive recursion on the exponent. Define
`charCoeffs(n,A)` by the determinant of the finite polynomial matrix
`tI-A`. Define scalar polynomial evaluation by the sum of scalar
coefficients times the corresponding powers, or by Horner recursion,
proving the two definitions equal.

### The uniform arithmetic target

For the generic matrix `X_n`, let

    residual(n) = X_n^n + sum_(k<n) c_k X_n^k.

Define `chCheck(n)` to return 1 exactly when every coefficient of every
entry of this residual is zero. It inspects `n² L` coefficients.
For `n=0` this is the empty conjunction, hence 1.

The central internal theorem is the first-order sentence

    forall n, chCheck(n) = 1.

This is the precise formula produced by `checkStatement` when its input is
the particular syntactically assembled code `chCheckCode : PR 1`.
The accompanying `NatKernelSpec.lean` already defines the concrete numerical
function `CayleyHamiltonNatSpec.chCheck : Nat → Nat`, along with every helper.
It remains to construct its PR syntax and prove its internal correctness.

The universal polynomial identity implies every fixed-ring instance by
evaluation of the generic variables at matrix entries. Within iPRA, for
each fixed PR presentation of a commutative ring whose laws have internal
proofs, this evaluation and the specialization proof are also PR and
internalizable. This is a schema over fixed presentations. It is not a
claim that first-order arithmetic quantifies over all mathematical rings,
or that all PR programs have one total PR evaluator.

Mathematically, evaluation in an arbitrary commutative ring is an external
interpretation of an integer polynomial identity and requires no decidable
equality on that ring. Arithmetic checking is performed on the formal
integer coefficients, where equality is decidable.

## Explicit finite bounds and quantifier-free invariants

The large bounds below are deliberately loose. iPRA requires primitive
recursiveness, not feasible running time.

The sum of the absolute coefficients of an entry of `tI-X` is at most 2.
Thus a determinant has coefficient norm at most `n! 2^n`.
An entry of `X^r`, for `r ≤ n`, has coefficient norm at most
`max(1,n)^r`. Every partial sum used for the main residual is consequently
bounded by

    H0(n) = (n+1) n! 2^n max(1,n)^n.

This estimate bounds the stated residual sums, not arbitrary implementation
intermediates. For a complete implementation use a structural majorant:
associate to each polynomial expression its sum of absolute coefficients,
bound a sum by the sum of its bounds and a product by their product,
and bound a finite fold by a recursion on its explicit loop count.
The corresponding bounds on coefficient codes are twice these magnitudes.
Apply the same construction to each fixed helper program, including its
temporary accumulators. This produces an explicit PR majorant by composition
and primitive recursion; it avoids an unexplained blanket constant.

A collection of polynomial matrices can be stored in one flattened coefficient
array. For the arrays of `c_k`, `B_k`, powers through `n`, residuals,
and their partial sums, an overestimate for its length is

    K(n) = (n+2)^4 (L+1).

The permutation enumeration counter is bounded by `T(n)=max(1,n)^n`.
Let `C(n)` be the maximum of the coefficient-code bounds from this structural
majorant, `K(n)`, and `T(n)`, plus one. A flat state with entries at most
`C(n)` and length at most `K(n)` has code bounded by `B(K(n),C(n))`, where

    B(0,C)=0,
    B(r+1,C)=2^C (2B(r,C)+1).

This gives a PR majorant for packed states of the main computation.
`NatKernelSpec.lean` uses nested list codes for readability: a polynomial
with coefficient-code bound `C` has code at most `B(L,C)`, and a matrix of
such polynomials has code at most `B(n*n,B(L,C))`. Use these composed bounds
for that version, or flatten the storage as above. Neither representation
is a claim about machine-word memory or a complexity optimization.

A bounded universal condition is compiled to a PR Boolean fold. For example,

    allEqZero(a,b)=prod_(i<b) isZero(lookup(a,i))

returns 1 precisely when all the first `b` entries vanish.
An invariant that says 'for every entry and every coefficient the partial
sum has the prescribed value' is therefore a literal equation between
PR terms, or an implication between such equations.
Its induction uses `PRA.qfInd` with a proof of `Fm.QF`.

The adequacy of this Boolean reading must be proved once by induction;
it is not an invocation of bounded-quantifier induction as an extra axiom.
Parameters such as `n`, a matrix code, and a coefficient index remain free
parameters of the induction. The bounded folds collect only the finite
families needed at that step.

## Modules and proof obligations

### 00. Coding

Implement the list, signed integer, Boolean, bounded sum/product, base-digit
and iteration operations as explicit values of `PR k`.
For every helper provide both its host executable definition and its PR
syntax tree, with defining-equation lemmas. Avoid a universal interpreter.
Only the finite collection of fixed programs used in this development
requires a semantics theorem.

Internal lemmas: list decoding, access after update, finite sum reindexing
under an explicitly given bounded bijection, and paired cancellation under
an explicitly given fixed-point-free involution.

### 01. Dense polynomial arithmetic

Build coordinatewise operations and bounded convolution. Prove the
commutative-ring laws internally, then prove the degree-support rules and
the specialization/evaluation equations. The coefficient proofs use
associativity and distributivity of the signed operations plus bounded
reindexings.

The generic polynomial ring construction permits one uniform numerical
statement of the main identity without choosing any particular numerical
model of every ring.

### 02. Determinants

Prove the following finite identities, with all maps explicitly defined:

1. Transposing a permutation preserves its sign and reindexes the Leibniz
   sum, giving `det(A^T)=det(A)`.
2. Swapping two equal rows pairs summands by a sign-reversing involution;
   each pair sums to zero.
3. Group the Leibniz sum by the chosen column in a fixed row to get Laplace
   expansion. The row/column deletion maps account for the sign.
4. Apply expansion to a matrix with one row replaced by another to obtain
   `A adj(A)=det(A)I`. Transpose gives the other order.
5. If needed for corollaries, expand `det(AB)` and group terms by the
   intermediate tuple; repeated indices cancel, and distinct indices
   reindex to yield `det(A)det(B)`.

Neither a basis theorem nor Gaussian elimination is needed for the main
theorem.

### 03. Characteristic coefficients and adjugate

Compute `B(t)=adj(tI-A)` as a coefficient array of length `n`.
Prove leading and constant coefficient statements by explicit expansion.
Coefficient extraction from

    (tI-A)B(t)=p_A(t)I

gives, for `n>0`,

    B_(n-1)=I,
    B_(k-1)-A B_k=c_k I  (1 ≤ k<n),
    -A B_0=c_0 I.

These are finite coefficient identities in the coded polynomial ring.
In this orientation, powers multiply on the left throughout.
Do not appeal to multiplicativity of evaluation of matrix-coefficient
polynomials; it is false without commutation hypotheses.

### 04. Telescoping

For each `r ≤ n`, prove the partial-sum identity by induction on `r`.
Multiplying the displayed coefficient equations on the left by the
appropriate power of `A` makes adjacent terms cancel.
At `r=n` the residual is zero.

An alternative implementation defines the left-oriented Horner chain
`B_(n-1)=I`, `B_(k-1)=A B_k+c_k I`; the terminal equation is
`A B_0+c_0 I=0`. This makes the induction state small.

Construct the closed derivation of `checkStatement chCheckCode`. Only then
apply `nativeMain_of_derivation`.

### 05. Algebraic corollaries

Use explicit PR recurrence vectors for the reduction of `A^k`.
Prove a monic polynomial division algorithm by a countdown on the input
degree or length; no division by coefficients is used.
The monic remainder has degree less than `n` and yields the matrix
evaluation reduction.

For inversion, use an explicitly supplied inverse `u` to the determinant,
and verify the proposed matrix inverse in both orders. A mere proof that
the determinant is nonzero is insufficient over a general commutative ring.

Newton identities are coefficient identities with natural-number
multipliers. Retain the multiplied form over general rings. Division by
`k` or `k!` requires an appropriate unit or a rational algebra.

Minimal-polynomial existence, if formalized over a fixed computable field,
requires a separate bounded linear-algebra algorithm. The search is over
degrees `0,...,n`, not over arbitrary field elements: decide linear
dependence of the finite list `I,A,...,A^n` by Gaussian elimination with
decidable equality and a supplied field inverse. Record the primitive
recursive bound for this fixed algorithm.

### 06. Analytic interfaces, if included

Formal-series identities are interpreted coefficientwise at arbitrary
finite truncation order. Analytic identities require explicit rational
approximants and tail moduli. A Lean proof about arbitrary real or complex
analytic functions is a host theorem; it must not be presented as a direct
sentence of first-order iPRA.

For the concrete exponential/sine example in the article, exact finite
power formulas plus rational-series error bounds suffice. For general
Hermite interpolation, hypotheses must include the finite eigenvalue data
and inverses of the needed differences. An unspecified splitting-field
existence theorem is not silently part of the arithmetic kernel.

## Suggested proof dependency map

| Module | Numerical inputs | Depends on | Deliverable |
| --- | --- | --- | --- |
| Coding | natural codes | PR defining equations | typed PR helpers and internal equations |
| SignedArithmetic | signed codes | Coding | internal commutative-ring equations |
| DensePolynomial | dimensions, degree cap, arrays | SignedArithmetic | convolution, degree support, specialization |
| FiniteMatrix | dimension and arrays | DensePolynomial | products, powers, scalar matrices |
| Determinant | dimension and matrix | FiniteMatrix, permutation coding | Laplace and adjugate identities |
| Charpoly | dimension and generic matrix | Determinant | coefficient relations |
| Telescoping | dimension and finite coefficient data | Charpoly | internal CHCheck theorem |
| Applications | power/degree/unit certificates | Telescoping | reduction, inverse, recurrence |
| NativeBridge | completed iPRA derivation | NativeBiInterpretation | native-calculus derivation |

No module may close its central obligation by postulating the statement it
is intended to prove. Temporary `sorry` declarations in a working branch
must be isolated from the verified target and clearly recorded; the
delivered outline instead leaves missing implementation in prose.

## Completion criteria

A finished formalization should report all of the following separately.

- The exact constructed `chCheckCode : PR 1`, with its connection to the
  numerical checker proved.
- The exact closed object-language formula.
- A term of `Prf PRAAx [] (checkStatement chCheckCode)`.
- A successful build against pinned Lean and Mathlib versions.
- An axiom audit of the host artifact, with a separate explanation that
  host axioms used to manipulate derivation syntax are distinct from
  object-language arithmetic axioms.
- A successful application of `pra_iff_native`, if native output is desired.
- Executable regression tests used only as implementation checks, not as a
  substitute for the uniform derivation.

The current packet provides the mathematical proof and this path; it does
not claim those completion criteria have already been met.

