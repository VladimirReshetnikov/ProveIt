# Seven exact integer projections and a protected residual basis

This note proves the finite algebraic transformations in the current iteration.
The semantic input is the literal 225-variable quartic of ProveIt package 158,
whose canonical JSON SHA-256 is
`fee84c408828aba3e7ceebe9a37f58509327063aa7fd078fd49c80adf3af4e56`.
All coordinates throughout this note range over the unrestricted integers.
No consistency assumption is used.

## 1. Graph projection in a common Hessian direction

Let R_0,...,R_{m-1} be quadratic integer polynomials in n variables. Write
H_i for the Hessian of R_i and l_i for its linear coefficient vector. Suppose
an integer direction d has d_p=1 and H_i d=0 for every i. Put a_i=l_i dot d.
Then the polynomial identity

    R_i(x+u*d)=R_i(x)+u*a_i

holds exactly, because both the mixed directional quadratic term and the
pure directional quadratic term vanish. Set y_p=0 and write x=y+u*d.
If one slope a_r is +1 or -1, the equation R_r=0 has the unique integral
solution u=-a_r*R_r(y). The other equations become

    R_i(y)-a_i*a_r*R_r(y)=0, i != r.

They still have degree at most two. This is an exact bijection of integer
zero sets: lift y to x=y-a_r*R_r(y)*d; project x to y=x-x_p*d. The deleted
row is zero on every lifted point, and the retained residual identities
hold as polynomial identities, not merely after numerical tests.

The method is inherited from package 159. The new work applies it to the
different package-158 arithmetic source and supplies fresh exact certificates.
The five chosen steps are below. Indices are zero based in each successive
input system, so they are not common coordinates across rows of this table.

| Input dimension | Pivot p | Deleted row r | Nonzero coordinates of d | Slope a_r |
|---:|---:|---:|---|---:|
|225|44|29|d44=1, d45=-1|1|
|224|60|46|d60=1, d61=-1, d62=-2|-1|
|223|64|49|d62=-1, d64=1|1|
|222|31|16|d31=1, d32=-1, d33=-2|1|
|221|25|10|d25=1, d27=-1, d28=-2|1|

The frozen certificate records the full quadratic restoration polynomial,
ordered retained-coordinate list, row identities, and input/output hashes
at each step. The result has 220 variables and 157 residuals. Its square sum
has degree four, 7,790 collected monomials, and coefficient height 142,238.

## 2. An integral affine chart with small coefficients

For the resulting 220-variable system, let a=x9, b=x10, c=x20, d=x21, e=x34.
The exact row identity is

    R19-R6 = 4+12a+16b+4c-d+e =: L.

A direct substitution for e would introduce coefficients as large as 16
into frequently used quadratic coordinates. Instead use four unrestricted
integer parameters u0,u1,u2,u3 and the affine chart

    a = u1+2u2,
    b = -u1-u2,
    c = -1+u1-2u2+u3,
    d = u0+2u3,
    e = u0-2u3.

It satisfies L=0 identically. Its inverse on L=0 is entirely integral:

    u0 = -6a-8b-2(c+1)+d,
    u1 = -a-2b,
    u2 = a+b,
    u3 = 3a+4b+c+1.

Substitution verifies both inverse identities. These formulas parametrize
every integer point of L=0; there is no parity or divisibility condition
left unstated. In particular, although L implies d-e is divisible by four,
the displayed inverse never divides an arbitrary integer coordinate by four.

All other coordinates are retained. Pull back every residual and omit R6.
The omitted row follows from the retained R19 because their difference is
L, which vanishes identically under the chart. The result is a bijection of
integer zero sets in 219 variables and 156 residuals. All residuals remain
quadratic.

The chart was found by exact lattice reduction of the four-row basis

    (1,0,0,0,-12), (0,1,0,0,-16),
    (0,0,1,0,-4), (0,0,0,1,1)

of the kernel of (12,16,4,-1,1). The discovery procedure is not required
for correctness: the full maps and their exact inverse certificates suffice.

## 3. A second affine graph projection

In the 219-coordinate chart the existing residual R80 is

    4 -4x10 -x20 -4x21 -2x23 -2x27 -2x29 -2x31 -2x33
      -4x35 -2x36 -2x39 -2x42 -4x61 -2x62 +x94.

Solve for x94 and substitute its integer affine expression into every other
residual. Omit R80 and coordinate 94. This is another exact integer graph
projection with unique restoration, and it preserves degree two of every
residual. There are now 218 coordinates and 155 residuals. The raw square
sum has 25,497 collected monomials and height 4,720,128.

## 4. Protected integer row operations

An elementary replacement R_i <- R_i+k R_j, for an integer k and i != j,
has the inverse R_i <- R_i-k R_j. Therefore it preserves the simultaneous
zero set exactly. It changes the square-sum polynomial but preserves its
integer zeros, since a sum of integer squares is zero precisely when every
residual is zero.

The final certificate gives 669 such elementary row operations. Four rows
are protected: indices 151,152,153,154 of the raw 218-variable system.
They are the two quadratic constraints for each of the q and q+1 power
blocks. They remain byte-for-byte identical, and none is used as the source
of any retained row operation. Their four private coordinates are 214-217.
This lets the distinct-base reciprocal-pooling theorem be composed directly
with the finished quartic without reversing any row transformation.

The protected final quartic P218 has the following exact metrics:

| Domain | Variables | Quadratic residuals | Degree | Collected monomials | Coefficient height | Residual height |
|---|---:|---:|---:|---:|---:|---:|
|Z|218|155|4|34,984|113,304|240|

Coefficient height is the maximum absolute coefficient after fully collecting
the square sum; residual height is the corresponding maximum before squaring.
Relative to P225 this removes seven coordinates and seven residuals, lowers
both coefficient heights, and increases the expanded support. These are
explicit tradeoffs, not a claim of a global simplicity optimum.

## 5. Consequence for consistency and evidence boundary

The composition of all seven exact integer projections is a bijection of
integer zero sets. The 669 residual operations preserve those zero sets
without changing coordinates. Thus P218 has an integer zero if and only if
the pinned P225 has one. Composing with the parent's ordinary arithmetic
calibration gives, in ZFC, that absence of an integer zero is equivalent to
Con(ZFC). This is not a proof of either side of that equivalence.

The finite checker independently verifies every coefficient identity, map,
inverse, row operation, and expanded polynomial coefficient. It imports no
producer modules. Its adversarial controls reject intentionally corrupted
maps, omitted rows, coefficients, and operation lists. These checks prove
finite algebra facts; they do not replace the parent's unbounded arithmetic
proofs or its finite-calculus-to-ZFC translation.

The complete ordinary parent proof files and the identified Lean interface
sources are retained. The transitive Lean/Rocq developments were not rebuilt,
and no new encoded object-language derivation or end-to-end proof-assistant
certificate is claimed.
