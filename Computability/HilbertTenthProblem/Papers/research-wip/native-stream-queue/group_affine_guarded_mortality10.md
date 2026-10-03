# An affine two-operation input for unrestricted mortality in dimension ten

The universal projective construction has an **unrestricted matrix-mortality
interface with one affine input matrix loaded in 2=1M+1A operations**.
The dimension is ten. All other matrices, including its rank-one
reset, are fixed once for all programs. The input matrix has entries only
zero, one and the positive affine register `t=alpha*x+(beta+1)`.

This is a dimension/loader tradeoff with the existing
[six-dimensional construction](group_projective_zero_mortality6.md),
which loads its quadratic reset in three operations. It also repairs the
specific obstruction in the [four-dimensional two-reset construction](group_two_reset_mortality4.md):
arbitrarily many reset occurrences are allowed here, and separate words
cannot erase its two tests independently.

The construction enforces a loading prefix by a scalar guard. Invalid
words have a nonzero scalar by a strict magnitude bound. In particular,
an invalid automaton transition is never treated as a zero matrix.
This packet supplies no uniform Diophantine certificate for the selected
word, its duration, or its matrix trajectory. The two-operation figure
counts only the entire ordinary-input matrix loader.

## 1. The inherited fixed alphabet and the new contract

Sections 1–3 of the [projective endpoint theorem](group_projective_zero_mortality6.md)
give one fixed finite signed alphabet of matrix pairs `(P_i,Q_i)` generating
a subgroup `K_U` of `Gamma x Gamma`. For a fixed program p and positive x,
put

    alpha=12*2^(p+1), beta=12*2^p, t=alpha*x+beta+1.

Its exact theorem is

    x in S_p iff some (P,Q) in K_U satisfies
                 (P*(-1,t)^T)_1=(Q*(-1,t)^T)_1=0.       (1)

The same fixed alphabet works for every p. This theorem depends on the
specified free-group representation, conjugated fibre subgroup and
injective embedding of the original graph group; no general claim about
arbitrary SL2 matrices is substituted for it.

Let `F_i=diag(S(P_i),S(Q_i))` be its integral six-dimensional symmetric-square
letters. They are invertible. With

    a=(1,0,0,1,0,0), z=(1,0,0,1,0,0)^T,
    v(t)=(1,t,t^2,1,t,t^2)^T,

the existing symmetric-square identity is

    a F v(t)=((P*(-1,t)^T)_1)^2+((Q*(-1,t)^T)_1)^2       (2)

for a product F representing `(P,Q)`. Consequently it is nonnegative and
vanishes exactly when both projective tests vanish.

The construction below gives fixed integral 10x10 matrices `D_i` and R,
and one affine integral matrix `D_T(t)`, such that

    x in S_p iff the alphabet {D_i} union {R,D_T(t)}
                 generates the zero matrix.                       (3)

If the original signed alphabet has s letters, this alphabet has s+1
fixed matrices and one input-dependent matrix, hence s+2 total. The
universal finite presentation and the numerical value of s remain
inherited abstractly. Finite toy presentations in the checker do not
instantiate them. No new external universality claim is needed.

## 2. Two occurrences of one affine letter load the quadratic column

Define

    T3(t)=[0,0,1; t,1,0; 1,t,0],
    T6(t)=diag(T3(t),T3(t)).                         (4)

Direct multiplication gives

    det(T3(t))=t^2-1,
    T3(t)e1=(0,t,1)^T,
    T3(t)^2 e1=(1,t,t^2)^T.

Thus T6 is invertible when t>1, and `T6(t)^2 z=v(t)`. All its entries are copies of 0,1,t;
no t-square is evaluated in the input loader. The quadratic expression
is produced by two occurrences of the input matrix in a witness word.
Both occurrences will be enforced by the guard, rather than assumed.

Words in the rest of this proof are **chronological**: for letters
`w_1,...,w_l`, the represented action is `A(w_l)...A(w_1)` on a column.
The desired chronological words have form `T T F*`. Their physical
action is therefore `F T6(t)^2`, giving exactly (2). Reversing the
convention reverses all word spellings, with no change to mortality.

## 3. An invertible four-coordinate guard for the exact prefix

For a chronological word w on T and the fixed-letter alphabet, let

    n=number of T letters,
    f=number of fixed letters,
    I=number of pairs i<j with w_i fixed and w_j=T.

These are nonnegative integers. Track the column `(1,n,f,I)^T`, starting
at `(1,0,0,0)^T`. The letter matrices are

    C_T=[1,0,0,0; 1,1,0,0; 0,0,1,0; 0,0,1,1],
    C_F=[1,0,0,0; 0,1,0,0; 1,0,1,0; 0,0,0,1].     (5)

The first increments n and adds the current f to I; the second increments
f. All fixed letters use the same C_F, including letters representing
inverses in the original group. Both matrices have determinant one and
entries only zero and one. Their products count the literal supplied
word; they need not respect cancellations in the original group.

Use the fixed row `g=(-2,1,0,3)`. Its scalar value is

    G(w)=n-2+3I.                                   (6)

This vanishes exactly on `T T F*`. Indeed n=0 forces I=0 and G=-2.
For n=1, G=-1+3I is never zero. For n>=3, G>=1. For n=2, G=3I,
so zero requires I=0: no fixed letter precedes either T, and the two
T occurrences are exactly the first two letters. Conversely that prefix
has n=2,I=0. Negative guard values are allowed and will be handled by
the magnitude argument, not discarded by an assumed positivity condition.

## 4. Weighted growth prevents every invalid-word cancellation

Use the positive weights `b=(1,2,3,1,2,3)^T`, with the same three
weights in each physical block. For t>=3,

    T3(t)*(1,2,3)^T=(3,t+2,2t+1)^T
                    <=t*(1,2,3)^T.                (7)

All entries of T3 are nonnegative. For each fixed physical matrix F_i,
precompute the positive integer

    lambda_i=max_row ceil((sum_column |F_i[row,column]|*b[column])
                          /b[row]).

This gives `|F_i|b<=lambda_i b`. The integer is at least one because
F_i is invertible, so every row has some nonzero entry. Multiplying
these componentwise inequalities, or using the corresponding weighted
supremum norm, proves

    |A(w)z| <= Rho(w)b,
    Rho(w)=t^n product_(fixed occurrences i) lambda_i >0,
    |s(w)|=|a A(w)z|<=2Rho(w).                    (8)

Here `|z|<=b`, and a observes two coordinates whose weights are one.
The estimate is valid for arbitrary chronological words, even when their
physical states cease to encode positive semidefinite matrices. Rho and
its powers are used only in the proof; they are not assumed to be a free
arithmetic witness encoding.

Define the full non-reset letters by

    D_T(t)=diag(T6(t), t C_T),
    D_i=diag(F_i, lambda_i C_F).                  (9)

Their dimension is `6+4=10`. Every D_i is invertible, and
`det(D_T(t))=t^4(t^2-1)^2`, so D_T is invertible for t>=3. These are
integer matrices; rational inverses are sufficient for the nonvanishing
argument below, and are not added to the alphabet.

Set the constant column and row

    v=(z,e0)^T, u=(a,4g), e0=(1,0,0,0)^T.        (10)

Since scalar factors commute with the control matrices, the exact scalar
identity is

    u D(w)v=s(w)+4Rho(w)G(w).                    (11)

If w is invalid, (6) gives a nonzero integer G. Thus
`|4Rho G|>=4Rho>2Rho>=|s|`, so (11) cannot vanish. This covers n=0,
n=1, incorrect order, extra input letters, and negative G uniformly.

If w is valid, its guard is zero and its physical column is `F v(t)`.
Equations (2) and (11) then show

    u D(w)v=0 iff w has chronological form T T F*
                       and its fixed suffix passes both tests in (1).  (12)

The guard is not an ordinary automaton whose missing transitions create
zero products. All non-reset letters remain invertible, and every invalid
middle word has an explicitly nonzero scalar. The constants lambda_i
are fixed matrix entries computed with the fixed program alphabet; no
run-time multiplication by lambda_i is hidden inside the input loader.
Such multiplications would still have to be paid by an arithmetic
certificate for an arbitrary matrix history.

## 5. One constant rank-one reset gives unrestricted mortality

Let

    R=v u.                                        (13)

Both boundary vectors are nonzero, so R has rank one and is integral.
They are constant, independent of t,x and the program p. In fact

    u v=2-8=-6, R^2=-6R.

Thus adjacent reset copies alone never give a zero. The fixed reset has
signed entries; no all-nonnegative mortality assertion is being made.

Any product with k>=1 resets can be written

    A0 R A1 R ... R Ak
      =(A0 v) [product_(j=1,...,k-1) u Aj v] (u Ak),      (14)

where the Aj are possibly empty products of non-reset letters. All Aj
are invertible, so both outer vectors are nonzero. Their outer product
is nonzero over the rationals and integers. Therefore (14) is zero
exactly when one internal scalar is zero. Products with no reset are
invertible; products with one reset are nonzero.

By (12), an internal scalar zero supplies one common fixed suffix word
passing both projective tests. Conversely such a word gives a zero
product `R D(w) R`. This proves (3), with no restriction on how many
times either R or D_T occurs in a mortality witness.

In particular the two different one-sided zero bridges that made the
four-dimensional reset unsound remain nonzero scalars here: they yield
the squares of their respective nonzero projective coordinates. Their
product cannot vanish. General synchronization follows from (14), not
just from these two examples.

## 6. Exact input ledger and remaining arithmetic interfaces

For each fixed program, precompute the positive numeral gamma=beta+1.
The complete input source is

    scaled=alpha*x,
    input_t=scaled+gamma.                         (15)

Every entry of D_T(t) in (9) is 0,1,t. This includes the scaled control
block because C_T has only zero/one entries. Accordingly (15) loads the whole
10x10 input matrix in **two literal operations: one multiplication and
one addition**, degree one, with no auxiliary witnesses or equations.
Fixed entries and copies cost no arithmetic. The source records the
full 100-entry copy template and checks it against the constructed matrix.

For the universal constants of Section 1, x>0 gives t>=37. More generally
any fixed alpha,beta>0 gives t>=3, sufficient for all invertibility
and weighted-domination claims. Only the compatible universal constants and the
specified K_U make the all-r.e.-sets claim (3).

The two quadratic-loading matrix occurrences are part of a finite
mortality witness; they are not two additional input-source gates. Their
multiplication, all fixed-letter actions, unbounded word selection and
the final zero test are **not** yet compiled into a uniform positive
Diophantine certificate here. The larger dimension and the growth/control
coordinates could make that compilation more expensive than the existing
paired-vector route. No improvement of a complete universal operation
bound, or optimality of dimension ten, is asserted.

This construction changes the alphabet and reset architecture. It is
not a functorial lift of the already-unsound four-dimensional semigroup
with its old variable reset retained.

## 7. Executable checks and scope

The [checker](group_affine_guarded_mortality10.py) and
[receipt](group_affine_guarded_mortality10.json) verify:

* every binary control word of length at most eleven, including empty
  words, one input occurrence, wrong order and repeated inputs;
* 512 ordinary program/input loader cases, the full affine matrix template,
  determinant factor, quadratic column identity and reset square;
* 1,024 independently evaluated physical/control/growth scalar identities
  and strict domination bounds, including negative guards, plus 96 dense
  matrix products and rank-one identities;
* twelve accepting words in actual finite one-relator fibre alphabets,
  with each word also tested at a wrong input, with a missing input
  occurrence, and with an invalid prefix order;
* 24 pairs of the old incompatible one-sided zero bridges, whose
  synchronized reset scalars and product remain nonzero.

The finite one-relator alphabets are illustrative. The parametric proof
and the inherited projective theorem establish the universal contract;
finite enumeration is not used to prove undecidability or absence of
arbitrarily long zero products. No new primary-source universality premise
is imported beyond the already proved parent construction.

Run the checker normally to compare the deterministic receipt. Use
`--write-receipt` only to regenerate it.

Independent proof/source/default review passed with no findings. Another
768 dense scalar cases on arbitrary signed unimodular fixed letters
(including 756 invalid-word nonzeros) and 384 three-reset factorizations
passed. Root review and a separate fresh default replay also passed.
