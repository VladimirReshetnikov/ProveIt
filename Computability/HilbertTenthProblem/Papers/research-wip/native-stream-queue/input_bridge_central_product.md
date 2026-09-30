# A paid central-product test and its native carry obstruction

A central **radix digit** of a product can be required to vanish in five
operations, with all new witnesses strictly positive under explicit endpoint
guards. If lower convolution coefficients do not carry into that digit and
the desired dot product is smaller than the radix, this is an exact zero
dot-product test. Reflected equality also has a concrete conditional
nine-operation test once a repunit is supplied.

The existing Boolean55/60 module does not supply those carry hypotheses.
In fact the literal five-operation test added to the complete positive
Boolean60 FIFO has an exact false positive at ordinary input x=37, and a
false negative at x=10. These examples already satisfy the native rail
typing, parity, joint bound, FIFO transport and the full positive kernel
converse. Reversing the intended data coordinates does not remove this
arithmetic carry issue.

This note supplies conditional arithmetic components and a scoped rejected
interpretation. It is not a universal certificate or a lower bound on all
reversal/routing methods. The established complete universal bound remains76.

## 1. Five paid operations really extract a central digit

Suppose a radix beta>=2, q=beta^N, and positive integer words A,B are
already supplied. Add positive coordinates ell,H,alpha and impose

    A*B = ell + q*beta*H,
    ell+alpha=q.                                      (1)

The literal instructions are

    product=A*B; upper=beta*H; shifted=q*upper;
    rhs=ell+shifted; bound=ell+alpha,

with free comparisons product=rhs and bound=q. This costs **5=3M+2A**,
with two equations and three positive witnesses. Even multiplication by a
fixed beta is counted. These equations state exactly that

    0 < A*B mod q < q,
    floor(A*B/q) is a positive multiple of beta.        (2)

Thus they select a zero native radix-beta digit at position N, with
positive low remainder and high quotient. No digit extraction or division
is a paid primitive in the source.

Let the mathematical polynomial product be

    A*B = sum_k c_k*beta^k, c_k>=0,
    L=sum_(k<N) c_k*beta^k.

The actual tested digit is

    (c_N + floor(L/q)) modulo beta.                    (3)

Consequently c_N=0 follows from(1) only after proving both L<q and
0<=c_N<beta. It is enough, though not necessary, to prove every product
coefficient is below beta. Formula(3) identifies precisely what is lost
if one reasons directly from a central polynomial coefficient to an
ordinary integer digit.

## 2. A complete conditional dot-product lemma

Let N>=4 and beta>N. Supply two Boolean digit arrays of length N satisfying

    a_0=b_0=a_(N-1)=b_(N-1)=1,
    a_1=b_1=0,
    A=sum_i a_i*beta^i, B=sum_i b_i*beta^i.

The index-N polynomial coefficient is exactly

    c_N=sum_(i=2)^(N-2) a_i*b_(N-i).                   (4)

It is a dot product between the forward data a_i and the data intentionally
stored in reverse order as b_(N-i). The upper and lower sentinel digits
contribute nothing to(4). Every coefficient of A*B is at most N<beta,
so no carries occur. The constant coefficient1 makes ell>0, and the top
coefficient1 at degree2N-2 makes H>0 because2N-2>=N+1. Therefore(1) has
positive witnesses **if and only if** every product in(4) is zero. The
positive construction is

    ell=A*B modulo q,
    H=floor(A*B/(q*beta)), alpha=q-ell.

This is an exact lemma at the mathematical interface stated above. It does
not assert that the five operations recover q=beta^N, type the digit
arrays, enforce the sentinels, or reverse another supplied field. For an
unbounded computation, choosing beta>N makes beta variable; no such
variable-radix typing has been supplied by either existing module.

## 3. Reflected wiring can be expressed, but its bounds remain obligations

There is a useful conditional equation for reflected equality itself.
Let J=1+beta+...+beta^(N-1), and let A,B have Boolean digits a_i,b_i.
Define

    E=J*(A+B)-2*A*B.                                  (5)

Although written as a subtraction, every polynomial coefficient of E is
nonnegative:

    [beta^k] E = sum_(i+j=k) (a_i-b_j)^2.               (6)

Here the bracket denotes a coefficient of the formal product, not native
integer digit extraction. In particular the coefficient at N vanishes
exactly when a_i=b_(N-i) for every1<=i<N. Assume beta>N and the explicit
endpoint guards

    a_0=1, b_0=0, a_(N-1)=0, b_(N-1)=1.

They make the constant and highest coefficients of E equal1. For N>=3
all coefficients are at most N<beta, and the same positive low/high
argument applies. Replacing A*B by E in(1) then enforces this reflected
equality exactly.

Compute A*B, A+B, J*(A+B), 2*A*B and their difference in5=3M+2A.
The remaining four extraction instructions cost2M+2A. The total is
**9=5M+4A**, with two final equations, conditional on the already-supplied
J and the stated typing and guards. For fixed beta, the exact repunit
equation `(beta-1)*J=q-1` costs a further1M+1A. If beta itself is a
variable, computing beta-1 costs one more operation unless already shared.

This is a possible arithmetic interface for reflected wiring, not a claim
that wiring is free. The endpoint guards and beta>N also need a proved,
paid interface. The existing one-field51 module supplies one masked word,
not two independent extracted words A,B. The independent Boolean55 module
supplies four words in radix3, not Boolean words in an arbitrarily large
radix beta. Neither fact changes merely because(5) uses only a few
multiplications.

## 4. Exact native counterexamples, including ordinary input

Add(1) with beta=3, A=F2 and B=F3 to the reviewed
[Boolean60 FIFO](input_bridge_boolean_ternary60.md). The literal resulting
source costs **65=34M+31A**, with18 equations and30 positive witnesses
besides ordinary x. The [checker](input_bridge_central_product.py) expands
all18 independent polynomials against the full instruction schedule,
including the inherited auxiliary-norm correction.

Both examples use q=243=3^5, W=81=3^4, append fields F0=F1=1, and equal
read fields F2=F3=A. In each case A has Boolean ternary digits and

    F2+F3=2x+W*(F0+F1),
    0<2x<W, sum(Fi)<q, sum(Fi) even.

Thus every original60 source coordinate is strictly positive by its full
converse. The run starts at the ordinary input2x and empties after five
steps; the common width/time quotient is L=3.

| x | A=B | Low-first ternary digits | True central coefficient c_5 | Incoming carry | Tested ternary digit |
|---:|---:|---|---:|---:|---:|
| 10 | 91 | 1,0,1,0,1 | 0 | 1 | 1 |
| 37 | 118 | 1,0,1,1,1 | 2 | 1 | 0 |

These digits have the same low/high sentinel pattern as Section2. Their
interior digits can therefore be read in exactly that forward/reverse
orientation. The failure is present even when that orientation is granted.

For A=91 the product polynomial has coefficients

    1,0,2,0,3,0,2,0,1.

Its lower polynomial portion is262, exceeding q by19. The incoming carry
makes the tested digit1 although the desired dot product is0. No choice of
positive witnesses in(1) can repair it: the bound fixes ell=19, while the
quotient floor(91^2/243)=34 is not divisible by3.

For A=118 the coefficients are

    1,0,2,2,3,2,3,2,1.

Its lower portion is316, giving an incoming carry1. The central value2
and that carry sum to3, so the native digit vanishes. Explicitly,

    118^2 = 73 + 243*3*19,
    ell=73, H=19, alpha=170.

Every added witness is positive. The original joint slack is5 and width
slack is7. This is a **full positive65 false witness for the zero-dot
interpretation**, not an untyped convolution example or a tuple missing
the ordinary-input/Pell extension. The65 source itself remains an exact
digit-zero relation; it is the proposed local-violation interpretation
that fails.

## 5. Remaining constructive obligations and evidence

Central-coefficient selection removes the particular ambiguity between
different cell pairs only when the data really have the specified reflected
placement. It still needs control of carries from lower coefficients and
of the size of the central nonnegative sum. One possible direction is a
larger variable radix or a growing guard window with proved empty adjacent
bands. Both require native typing and routing equations; neither is
provided by the fixed51 mask or the four radix3 Boolean fields. This note
does not exclude a design that pays those obligations within the remaining
budget or uses a different arithmetic identity.

The checker verifies1364 conditional dot-product pairs,340 guarded
reflection pairs, both native FIFO examples, and the full65 source map.
The conditional tests use beta=N+1 and do not purport to implement its
geometry. The positive large Pell extensions are those of the reviewed60
theorem, not materialized astronomical integers. The
[saved receipt](input_bridge_central_product.json) is reproduced by running
the checker without `--write`.

Independent full proof, source, and default-replay review passed. The
conditional typing, guard, and carry assumptions remain explicit.
