# Independent mathematical review of the cyclic-carry proposal

**Verdict:** the formulas, complete fixed-point classification, budget
consequence, and strict-transport uniqueness claim are correct under the
stated cyclic assumptions. No counterexample or missing mathematical
premise was found. The strict-transport corollary must explicitly retain
the congruence between the raw packed word and `F`. This is an ordinary
mathematical verification, not a Lean formalization.

Reviewed: `algebra_notes.md`, `algebra_prototypes/check_cyclic_carries.py`,
its saved JSON receipt, and the actual source modules
`NativeCyclicCarry.lean` and `NativeCyclicCarryWord.lean` at
`8e8b5dcb954969621c484588f0b902be1cfea7b3`.

## Assumptions and notation

Let `rho` and `n` be natural numbers with `rho > 1` and `n > 0`.
Indices are in the **single actual cycle** `ZMod n`, and the predecessor
is `i-1`. Let `a : ZMod n -> Nat` be an arbitrary raw word; no digit
bound is initially required. Put

\[
M=\rho^n-1>0,\qquad
A_i=\sum_{j=0}^{n-1}\rho^{n-1-j}a_{i-j},
\]
\[
k_i^-=\left\lfloor\frac{A_i\mathbin{\dot-}1}{M}\right\rfloor,
\qquad
k_i^+=\left\lfloor\frac{A_i}{M}\right\rfloor.
\]

The subtraction `dot-` is truncated natural subtraction. The recurrence
under study is `k_i = floor((a_i+k_(i-1))/rho)` for natural carry values.

## Full verification

### 1. Exact rotated-sum identity

Reindexing the `n` terms, including the wraparound term, gives

\[
\rho A_i=M a_i+A_{i-1}. \tag{1}
\]

All powers are strictly positive, and every `A_i` uses each raw coordinate
once. Thus either `a` is identically zero and every `A_i=0`, or every
`A_i>0`.

Also, if `M` divides one `A_i`, (1) shows that it divides `A_(i-1)`.
Repeating predecessor steps around the finite cycle proves divisibility
for every coordinate. No separate coprimality argument is necessary.

### 2. Both formulas are fixed points

For the greatest formula, use the ordinary remainders
`A_i = M*k_i^+ + e_i`, with `0 <= e_i < M`. Substitution in (1) gives
the integer identity

\[
M(a_i+k_{i-1}^+-\rho k_i^+)=\rho e_i-e_{i-1}. \tag{2}
\]

The right side is strictly between `-M` and `rho*M`. Since it is an
integer multiple of positive `M`, its quotient lies in `0,...,rho-1`.
Consequently `a_i+k_(i-1)^+ = rho*k_i^+ + d_i`, where `0<=d_i<rho`,
which is exactly the quotient recurrence.

For the least formula, the all-zero raw word is immediate. Otherwise,
division of `A_i-1` gives the positive-remainder convention
`A_i = M*k_i^- + e_i`, with `1<=e_i<=M`. Equation (2) holds with
minus superscripts. Its right side is at least `rho-M`, hence greater
than `-M`, and at most `rho*M-1`, hence less than `rho*M`. The same
integer-multiple argument proves the quotient recurrence.

The integer calculation is intentional. A Lean proof must establish the
nonnegativity of the resulting digit before replacing integer subtraction
by natural subtraction. Defining digits through the existing remainder
function avoids any ambiguity at this boundary.

### 3. Exhaustiveness and exact ambiguity

For an arbitrary natural fixed point, define its Euclidean digits by
`d_i = (a_i+k_(i-1)) % rho`. Then

\[
a_i+k_{i-1}=d_i+\rho k_i,\quad 0\le d_i\le\rho-1.
\]

Multiply the equalities by the rotated geometric weights and sum. The
carry terms cancel, giving

\[
A_i=Mk_i+D_i,\qquad
D_i=\sum_{j=0}^{n-1}\rho^{n-1-j}d_{i-j},\qquad
0\le D_i\le M. \tag{3}
\]

This immediately yields `k_i^- <= k_i <= k_i^+` (with the zero case
handled explicitly).

If some `A_i` is not divisible by `M`, (3) forces that carry coordinate
to be `floor(A_i/M)`. The deterministic recurrence then determines all
successive coordinates, so the entire carry assignment is unique.
Equivalently, every coordinate has nonzero residue and the two formulas
coincide.

If the raw word is nonzero and `M` divides `A_i`, (3) forces `D_i` to
be either 0 or `M`. In the first case all digits are zero, because the
weights are positive. In the second case all digits are `rho-1`, because
the nonnegative weighted deficits from the maximum sum to zero. These
are global conclusions: this one rotated sum includes the whole cycle.
Equation (3) then fixes all carries to `k^+` or `k^-`, respectively.
The two arrays differ by one at every coordinate, so there are exactly
two solutions, not a collection of independently selectable signs or
choices at the different coordinates.

If the raw word is zero, (3) forces both `k_i=0` and `D_i=0`, so zero
is the only natural solution. This exception is why the nonzero raw
premise must accompany the divisibility criterion.

### 4. Budget theorem

For `D : Nat`, the source budget

\[
a_i+D<(D+1)\rho
\]

is equivalent to `a_i <= (D+1)(rho-1)`. The geometric sum gives
`A_i <= (D+1)M`. If `A_i>0`, then `A_i-1<(D+1)M`, and division by
positive `M` gives `k_i^-<=D`. The zero case gives the same conclusion.

The greatest solution need not lie in that box. If every raw digit is
`(D+1)(rho-1)`, the least carries are all `D` and the greatest carries
are all `D+1`. Thus the correct bounded-existence adapter uses `k^-`.

Because `k^-` is globally least and belongs to the source carry box,
it also equals the existing bounded-box least fixed point. This gives
a theorem relating the formula to the current implementation without
changing the implementation.

### 5. Strict transport uniqueness

The source packed-word convention is `word rho a = sum_i a_i*rho^i`.
The proposed indexing satisfies

\[
A_{n-1}=\operatorname{word}(\rho,a).
\]

Assume the existing transport hypothesis
`word rho a ≡ F (mod M)` together with `0<F<M`. Then `M` does not
divide `A_(n-1)`, so the normalization is unique. Every corresponding
digit array is also unique because the quotient recurrence fixes its
Euclidean remainders. Under the budget, the existing existence theorem
therefore upgrades to unique bounded normalization.

The inequalities on `F` **without** the raw-word transport congruence
would not imply uniqueness. The report and proposed theorem must retain
that congruence. The existing source already does.

## Edge cases

| Case | Result |
| --- | --- |
| `n=1`, arbitrary `rho>1` | `A=a`, `M=rho-1`; the same proof and formulas work. |
| `rho=2`, `n=1`, hence `M=1` | For `a=0`, only carry 0. For `a>0`, exactly carries `a-1` and `a`, with digits 1 and 0. |
| `M=1`, strict transport | `0<F<1` is impossible, so the uniqueness corollary is vacuous, not false. |
| All raw digits zero | Truncated subtraction makes both formulas zero; uniqueness holds. |
| All raw digits `rho-1` | Least carry 0 and greatest carry 1; digits all `rho-1` and all 0. This refutes unconditional uniqueness. |
| Budget endpoint | Constant raw `(D+1)(rho-1)` meets the strict budget; only the least of the two carries necessarily fits `0..D`. |
| `rho=1` | Excluded: `M=0`; the original general theorem still covers positive radix 1 under its own budget. |
| `n=0` or arbitrary predecessor | Excluded from the formula: the finite single-cycle reindexing is essential. |

## Relation to the existing general theorem

`NativeCyclicCarry.exists_bounded_carries` works on an arbitrary index
type and arbitrary predecessor function, using a complete bounded carry
box. It does not assume finiteness, a single cycle, or `rho>1`; it only
requires positive radix and its stated budget. **Keep it.** The new
theorem is a specialized characterization for `ZMod n` and predecessor
`i-1`, intended to simplify canonicality and witness-identification
arguments. It is not a replacement preserving the general theorem's
full strength, nor an immediate line saving for its already short proof.

## Evidence status

The existing Python script checks 57,540 bounded raw instances and
enumerates every candidate carry in `0..D+1` in 2,323 smaller instances.
The script's ranges and inclusive bounds match its JSON description.
Those finite checks are useful diagnostics; the universal classification
above rests on the mathematical proof, and has not been checked in Lean.
