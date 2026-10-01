# Nine-dimensional mortality with paid selected-word certificates

The [ten-dimensional affine mortality construction](group_affine_guarded_mortality10.md)
needs only three guard coordinates, reducing its dimension to **nine**
with the same two-operation ordinary-input matrix loader. More importantly,
its mortality predicate can be projected exactly onto the existing paid
paired-vector compiler: the guard and growth coordinates need not become
additional arithmetic histories.

This packet also gives a literal positive certificate for a **selected**
word of fixed duration n over s fixed paired matrices. Selection, integer
range, signed intermediate states and endpoints are paid. For n>=2 its
certificate costs `(16n-8)s+9n-11`, and its one SOS polynomial costs
`(16n-8)s+24n-20`, with `6n-3` positive witnesses and degree at most2s.
This duration-dependent circuit is separate from the uniform compiler.

The unbounded existential mortality predicate inherits a complete uniform
certificate from the named compiler in Section5. This is an exact reduction
of existence predicates. It does not certify an arbitrary supplied
mortality word, preserve all its reset positions, or bound its duration.
No new numerical universal alphabet or improvement to75/88 is claimed.

## 1. Three guard coordinates and the unchanged scalar separation

Retain the six-dimensional physical letters, weighted bound and affine
input of the parent. In particular

    t=alpha*x+beta+1>=3,
    T3(t)=[0,0,1; t,1,0; 1,t,0],
    T6(t)=diag(T3(t),T3(t)),
    z=(1,0,0,1,0,0)^T, a=(1,0,0,1,0,0).

For each fixed physical letter F_i, the parent supplies a fixed positive
weighted row bound lambda_i. Its proof uses the weights `(1,2,3)` in both
blocks and `T3(t)(1,2,3)^T<=t(1,2,3)^T`. Thus, on any chronological word w,

    rho=t^(number of T letters)*product(lambda_i),
    |a A(w)z|<=2rho.                              (1)

Chronological order means that later letters multiply on the left.
Let n_T be the number of input letters, f the number of fixed letters,
and I the number of fixed-letter-before-input ordered pairs. Directly
track the state

    (1,3f,G)^T, G=n_T-2+3I,

starting at `(1,0,-2)^T`, with matrices

    C_T=[1,0,0; 0,1,0; 1,1,1],
    C_F=[1,0,0; 3,1,0; 0,0,1].                  (2)

An input letter increases G by1+3f; a fixed letter increases3f by3.
This is exactly the former guard, without storing n_T separately.
Both matrices have determinant one. Crucially C_T has only0/1 entries:
the coefficient3 occurs only in fixed-letter data.

Use the nine-dimensional letters and constant boundaries

    D_T(t)=diag(T6(t),t C_T),
    D_i=diag(F_i,lambda_i C_F),
    v=(z,1,0,-2)^T, u=(a,0,0,4), R=vu.          (3)

Every non-reset letter is invertible. The input determinant is
`t^3(t^2-1)^2`; its entries are only0,1,t. Thus the complete81-entry
matrix is still loaded by `alpha*x`, followed by addition of the fixed
numeral beta+1: **2=1M+1A**, with no witness or equation.

The exact scalar identity remains

    uD(w)v=aA(w)z+4rho*G(w).                     (4)

The parent proves `G=0` exactly for chronological words `T T F*`.
If G is nonzero, its integrality and (1) make the second term in (4)
strictly dominate the first in absolute value. This includes negative
G and words with zero, one or too many input letters. If G=0, then
`T6(t)^2 z=(1,t,t^2,1,t,t^2)^T`, so (4) is the sum of the two original
projective-coordinate squares.

The fixed reset satisfies `uv=-6` and `R^2=-6R`. In any product with
arbitrarily many resets, rank-one factorization and invertible outside
words give zero exactly when one internal scalar (4) is zero. Therefore
the parent's unrestricted mortality theorem transfers unchanged to9D:
one input matrix varies, and s+1 matrices are fixed if the original signed
alphabet has s letters. The negative component of v is fixed data; no
positivity assumption on a mortality witness is being added.

For this specific guard series three linear state coordinates are also
necessary over Q. Its Hankel matrix on prefixes `(empty,F,T)` and suffixes
`(empty,T,FT)` is

    [-2,-1,2; -2,2,5; -1,0,3],

of determinant-9. Any d-dimensional linear representation of the scalar
series factors this matrix through dimension d, so d>=3. This is not
a lower bound for other guards or for total mortality dimension.

## 2. A paid positive certificate for a selected duration

Fix s>=2 integral paired SL2 matrices `(P_j,Q_j)`, indexed by1,...,s,
and a duration n>=1. The following circuit chooses the word; its letters
are not fixed in advance. The ordinary input is x>0 and
`v_x=(-1,t)^T`, with the same two-gate t loader.

At step k supply positive integers j_k,b_k and compare

    j_k+b_k=s+1.                                 (5)

This costs one addition and one equation. Positivity and integrality
make j_k exactly one of1,...,s, with b_k=s+1-j_k. No Boolean selector,
division, or membership predicate is assumed for free.

Let D=s!, a fixed positive numeral. For each of the eight paired matrix
entries, compile the polynomial l_r(J) of degree at most s-1 with

    l_r(j)=D*(entry r of letter j), j=1,...,s.     (6)

These polynomials have integer coefficients: every denominator of a
Lagrange basis polynomial divides `(s-1)!`, which divides D. Computing
these fixed coefficients is program compilation. Every subsequent
Horner multiplication and addition, including multiplication by fixed
coefficients or D, is charged by the literal source.

For n>=2 supply one positive common shift H and four positive fields
`X_(k,r)` after each of the first n-1 steps. They represent the signed
coordinates `X_(k,r)-H`. Initial coordinates are `(-1,t,-1,t)`.
Intermediate transitions compare, for each paired row,

    D*X_new = l_left(j_k)*v_left+l_right(j_k)*v_right+D*H. (7)

The source computes D*H once and obtains each previous signed coordinate
with one subtraction. At the first step, the action is evaluated as
`l_right(j_0)*t-l_left(j_0)`, costing only one multiplication and one
subtraction per row. At the final step, only the first row in each block
is needed; compare its scaled output directly to zero. There is no final
state witness or second-coordinate requirement.

At a positive zero, (5) gives actual table letters. Since D>0, induction
through (7) recovers their exact integer trajectory, followed by

    (P_word v_x)_1=(Q_word v_x)_1=0.              (8)

Conversely, take any selected length-n word satisfying (8). Choose
H greater than the absolute value of every intermediate coordinate, and
put X=H+v there. All supplied coordinates are positive and (5)-(7) hold.
For n=1 no intermediate state or H is supplied. This proves both
directions of the duration-bounded certificate for arbitrary integral
SL2 table entries; no Gamma-specific stabilizer is used in this section.

The chosen word gives a canonical9D mortality word with two resets,
two input letters and n fixed letters. Conversely any zero mortality
word has some internal canonical scalar witness by (4), whose suffix
has a finite duration and therefore has one of these certificates.
The empty suffix has scalar2, so every zero uses duration n>=1.
This does not constrain that duration to the original total word length.

## 3. The exact literal ledger

For n>=2 there are eight lookup columns at each of the first n-1 steps,
and four at the last. Each column costs s-1 multiplications and s-1
additions. The remaining instructions include both input-loader gates,
one shared D*H, every branch bound, every intermediate state subtraction,
all row actions, and both sides of each intermediate comparison.
The resulting counts are

    M=(8n-4)s+4n-6,
    A=(8n-4)s+5n-5,
    graph=(16n-8)s+9n-11,
    positive witnesses=2n+4(n-1)+1=6n-3,
    equations=n+4(n-1)+2=5n-2.                   (9)

For n=1 the source has four lookup columns, two final row actions and
one branch bound:

    M=4s-1, A=4s, graph=8s-1,
    positive witnesses=2, equations=3.           (10)

All subtractions count as additions. Fixed signed integer numerals and
register copies are allowed by the same arithmetic convention as the
parent packets. No multiplication by a nontrivial fixed numeral is free.

Both final comparisons have right side zero, so their action registers
are already their residuals. Reusing them avoids two subtractions by zero.
Squaring and summing all comparison residuals therefore costs3e-3 operations:

    n=1:  polynomial=8s+5,
    n>=2: polynomial=(16n-8)s+24n-20.             (11)

Every supplied field and x has degree one; fixed data has degree zero.
Lookup degree is at most s-1, and each row action multiplies it by an
affine state or t. Thus every residual has degree at most s and the
SOS has degree at most2s. This is an upper bound, not an exact-degree
claim for degenerate or repeated table entries.

The counts grow with n. One cannot turn (9)-(11) into a uniform fixed
Diophantine equation merely by declaring n existential: the number of
variables and instructions would still depend on n. Section5 uses an
existing genuinely uniform compiler instead.

## 4. Why only four vector histories are needed uniformly

For the universal fixed alphabet and its compatible input,
`t=12*2^p(2x+1)+1`, every paired block lies in the parent's Gamma.
In particular its diagonal entries are1 modulo4 and its lower-left
entry is0 modulo4. These congruences are closed under multiplication.

Here is a direct endpoint check. Write a block as `[a,b;c,d]` with
determinant one and suppose its first output at `(-1,t)` vanishes.
Then a=bt, and its determinant gives

    b*(td-c)=1.

Thus b=1 or-1. Since a and t are1 modulo4, b=1 modulo4 and hence b=1.
Therefore td-c=1, and the full output is exactly e2. Applied to both
blocks, this proves

    both projective coordinates vanish
       iff both entire vectors equal e2.         (12)

The input congruence matters. For example with t=3 and
`P=[-3,-1;4,1]`, determinant one and diagonals1 modulo4 hold, but
`P*(-1,3)^T=-e2`. This packet does not transfer arbitrary positive
alpha,beta to the full-vector compiler without the stated compatibility.

Combining (4), rank-one reset factorization and (12), unrestricted9D
mortality is equivalent to the existence of an original paired macro
word acting on `(-1,t)` and ending at `(e2,e2)`. This proof eliminates
the guard, growth and arbitrary reset coordinates from the **existence
predicate**. It does not omit their verification for an arbitrary word:
the scalar domination theorem first proves that some accepted word must
contain a correctly ordered, common projective witness.

## 5. An explicit complete uniform compiler for that predicate

The [range-typed paired-vector compiler](group_range_projective_compiler.md)
already certifies exactly the endpoint in (12) for any fixed macro table.
For padded edge count m=2^h, physical port cost p and sparse flow cost f,
write

    C0=3m+3h+p+185+f-3min(h,3).

Its source gives a complete certificate with C0 operations,26 comparisons
and m+40 positive witnesses, or one SOS with C0+77 operations and exact
degree12m+232. It applies to the compatible mortality input without any
fixed margin condition. All word selection, finite control, digit typing,
history arithmetic and variable duration are already paid by that theorem.
The9D guard adds no further runtime gates to this equivalent predicate.

A smaller named implementation is the
[factored native-index compiler](group_projective_factored_native_index.md).
First reflect each macro by swapping signed shear labels1/2,3/4,5/6,7/8,
preserving their order. This conjugates both matrix blocks by
`diag(-1,1)` and changes the initial vector from `(-1,t)` to `(1,t)`,
leaving e2 fixed. The source builder does not perform that reflection
implicitly: the checker passes the reflected table explicitly.

With the fixed margin `alpha+beta+1>=m`, mask reuse epsilon (m>=8 when
epsilon=1), computed-P option chi, L=m+18 or2m+10, and nu=1+chi, this
named certificate has

    C=C0-epsilon,
    graph=C-1, comparisons=10-chi,
    positive witnesses=m+28-chi,
    polynomial=C+28-3chi,
    exact degree=nu(27L+m+15)+46.                 (13)

These are imported literal counts, not a newly optimized compiler.
The illustrative ten-letter table with both options gives257 certificate
operations or283 polynomial operations,9 comparisons,43 positive
witnesses and degree2376. The universal numerical matrix table is still
uninstantiated; its m,p,f are fixed but not numerically claimed here.

For a family representing every r.e. set, the margin is supplied by the
existing [padded universal enumeration](group_projective_padded_program_margin.md).
Build its one fixed alphabet first, determine m, then choose a repeated
program index large enough for the margin. The same compatible affine
input is used for both the9D mortality matrices and (13). There is no
circular choice of alphabet and no free input-conversion witness.

Thus a complete **existential mortality certificate** is available through
the four-history endpoint theorem. What remains open in this packet is
a cheaper compiler exploiting9D mortality itself, or a compact certificate
for a separately supplied arbitrary mortality word and all its reset
positions. Neither the finite-duration schedules nor the two-gate loader
claim such an improvement.

## 6. Executable evidence

The [source](group_affine_guarded_mortality9.py) and
[receipt](group_affine_guarded_mortality9.json) check2,047 control words,
the rank-three Hankel minor,768 scalar agreements with the10D construction,
64 dense reset identities, and the full81-entry affine input template.

Twenty selected-duration circuits cover s=2,...,5 and n=1,...,5. Each
checks exact graph/SOS ledgers, interpolation at every branch, and a
syntactic degree upper bound. There are640 arbitrary positive or signed
full residual/SOS checks and640 independently constructed selected
trajectories. Eight actual accepting traces are tested with wrong inputs,
out-of-range selectors, incorrect selector slacks and altered state fields.
Those mutations are rejected by the paid equations.

Finally, two fixed macro tables instantiate both named uniform compilers,
check the literal reflection and verify their actual source counts. These
finite tables are illustrative, not universal alphabets or numerical
materializations of full native Pell zeros. The imported theorems prove
the uniform reduction; the executable builds ensure the claimed arithmetic
interfaces are the paid sources actually named.

Run with the research Python environment; `--write-receipt` regenerates
the deterministic receipt, and default execution compares it.

An independent proof/source/default review passed. It additionally checked
192 direct Lagrange/full-SOS evaluations and192 positive selected traces
on independently generated signed SL2 tables of sizes3,6,9. Those checks
extend the finite algebraic evidence; they do not instantiate a universal
numerical alphabet.

Root proof/source review passed. The final SOS schedule then removed
the two subtractions by zero at the terminal comparisons; regenerated
and fresh default checks passed with the two-gate saving recorded in
(11). Certificate counts, positive maps and degree bounds are unchanged.
