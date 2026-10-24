# Integer signs inferred from the actual arithmetic equations

All variables of the parent equation range over the nonnegative integers.
The integer equation retains that entire finite residual system, supplies
selected sign guards, and then applies exact monic coordinate elimination.
Its proof does not discard the sign of a coordinate merely because that
coordinate is called a wire or a quotient. Every original coordinate receives
a finite sign derivation checked against literal rows.

## The guard polynomial

For unrestricted integers a,b,c put

    H(a,b,c) = a^2 + b^2 + c(c+1).

This is always nonnegative, and represents every nonnegative integer.
For completeness apply Legendre's three-square theorem to 4n+1. Exactly
one representing square is odd and two are even; write their roots as
2c+1,2a,2b and divide the resulting identity by four. This includes n=0.
Thus x=H(a,b,c) is an exact existential nonnegativity guard. The result is
also formalized in the Archive of Formal Proofs entry Three_Squares.

The construction appends guards; it does not substitute squares into an
already quadratic parent row. All residuals therefore remain quadratic.

## Four exact sign rules

### 1. Nonnegative polynomial evaluation

If a literal parent row is x-f=0, up to its overall sign, and f has
nonnegative integer coefficients, then x is nonnegative whenever every
variable occurring to an odd exponent in a monomial of f is nonnegative.
Even powers require no sign assumption. The certificate supplies the row,
the complete f, and precisely those dependencies. The checker compares
every coefficient. This works for semantic witnesses as well as stored
arithmetic values.

### 2. A centered product controls two signs

For integers x,y with x+y>=-1,

    x>=0 and y>=0  <=>  2xy+x+y>=0.

Indeed (2x+1)(2y+1)=2(2xy+x+y)+1. If the right side is positive, the two
odd factors have the same sign. If both were negative, x,y<=-1 and
x+y<=-2, a contradiction. The reverse implication is immediate.

When a literal row gives x+y=f with f>=-1, replace two separate guards
by the single quadratic row

    2xy+x+y = H(a,b,c).

The certificate checks the exact sum row and proves its lower bound from
earlier nonnegative coordinates. It does not assume that two separately
chosen existential square representations can share witnesses. This
construction represents the single product value directly.

### 3. A shifted quotient is nonnegative

If A>=0, B>=1 and A(q+1)=B with q an integer, then q>=0. If q<=-1,
the left side would be nonpositive. The finite certificate supplies the
integer-polynomial identity expressing this equation as a combination of
literal parent rows and their defining arithmetic equations.

For a binomial digit certificate, write the rows as

    N = d(Qh+o)+r,
    d = r+s+1,
    Q = o+t+1.

They imply the exact identity

    d Q(h+1) = N+d t+s+1.

This proves h>=0 from nonnegativity of the displayed factors and summands;
it needs no separately appended guard on h. Explicitly, if the three
residuals are R1=N-d(Qh+o)-r, R2=d-r-s-1, R3=Q-o-t-1, then

    d Q(h+1) - (N+d t+s+1) = -R1+d R3+R2.

The analogous Euclidean division rows N=dq+r and d=r+s+1 give
d(q+1)=N+s+1. The checker expands only the finite local arithmetic
definitions needed for these identities, not the entire large source
polynomial.

### 4. The common Pell frame orients an existing root

The literal common frame is

    W = 2 + sum(nonnegative arithmetic atoms),
    A^2 = 1 + W^3(W+2)(z+1)^2.

Once A,z and the sum's inputs are nonnegative, W>=2 and A>W^2. For each
relevant base n, the certificate gives an exact nonnegative polynomial
for W-n, so A>=n. The power-congruence row is

    X+Yn = YA+m+Tq.

If Y,m,T,q are already nonnegative, then

    X = Y(A-n)+m+Tq >= 0.

This argument precedes Pell classification and requires no assumption
about the sign of X. It is therefore a valid way to remove an X guard,
and does not reason in a circle through the power theorem. The checker
authenticates the complete common norm, the frame sum, the base-modulus
row 2An=T+n^2+1, the power row, and the W-n coefficient certificate.
All required signs must occur earlier in the recorded proof schedule.

## Exact existence equivalence before projection

Starting from an arbitrary integer zero of the guarded system, each seed
guard establishes its sign. Apply the finite sign proof in its supplied
order. Every rule's dependencies have already been established; ultimately
every original coordinate is nonnegative. The complete parent prefix is
unchanged, so restriction is a natural zero of the parent.

Conversely, take any natural parent zero. Every selected coordinate and
every selected centered product is nonnegative. The ternary representation
H supplies the fresh guards independently. This extends the parent zero
to an integer zero of the guarded system. The forward map is restriction;
the converse need not be unique because three-square representations need
not be unique.

## Exact monic projection

Over unrestricted integers, a row v-f(y)=0 may be deleted while replacing
v by f in every other row. Projection is a bijection on the two integer
zero sets, with inverse v=f(y). The restoration polynomial can have either
sign of coefficient. At every step the checker verifies the exact monic
row, the absence of self-dependence, and the degree of *every* substituted
row. All rows remain quadratic. Restore deleted coordinates in reverse
chronological order. The retained sign guards are transformed along with
all other rows; none is dropped.

The final polynomial is the sum of squares of the final residuals. Over
integers it vanishes exactly when they all vanish. Its collected dictionary
contains degree-four terms, proving exact degree four. The independent
checker reconstructs the full dictionary, verifies every coefficient, and
checks that every counted coordinate occurs.

Composing these elementary theorems with the direct parent's arithmetic
and calibrated C222/refutation equivalence gives, by ordinary mathematics
formalizable in ZFC, the required no-integer-zero/Con(ZFC) equivalence.
No consistency hypothesis is used. No new end-to-end Lean/Rocq or encoded
object-ZFC proof is claimed.

## Reproducibility

`build_integer.py` proposes sign rules and a deterministic proof schedule.
`projection.py` is retained from the incoming batched-certificate optimizer.
`verify_integer.py` imports neither of them. It independently checks all
sign-rule identities, guard coverage, the entire projection, and the
expanded polynomial. Its checks remain enabled under Python `-O`.

Four negative controls reject a missing pair guard, a false frame margin,
an altered restoration, and an altered final coefficient. These are finite
transcription and algebra checks. The universal correctness arguments are
the mathematical proofs above, not bounded witness searches.
