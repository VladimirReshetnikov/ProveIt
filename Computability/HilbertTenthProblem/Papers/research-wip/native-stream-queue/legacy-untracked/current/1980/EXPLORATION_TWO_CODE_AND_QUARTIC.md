# Structural alternatives to the single square code

This is a bounded exploration beyond the proved 97-operation system
in `COMPOSED_97_PROOF.md`. It investigates two independent code
polynomials and quartic sum-of-squares bundling. It records exact
identities, instruction budgets for specific prototypes, and the
remaining proof barriers. Neither prototype below is a proved
universal representation or a smaller certificate. The counts are
not lower bounds on other constructions. Fixed numerals are free.

## What the current square-code construction pays for

The current code arithmetic includes

    C=x+g, C2=C*C,
    eq=e*q, S2=ell+eq,
    Omega=lambda-e,
    P1=Omega*C2,
    P2=(theta*lambda)*q,
    sigma=P2-P1.

The second mask and the congruence S2=V+t*theta recover a fixed
coefficient polynomial and an indicator polynomial. Their temporary
quotient alias is eliminated by the HIGH part of the third mask.
Its LOW part tests the quadratic residuals. Thus the third mask
does two jobs: replacing its many low targets by a single target
does not automatically preserve coefficient decoding.

The same positive Omega and sigma also give the preliminary bound
C^2<P2 before the Pell exponents are known. That bound is needed to
bound the packed index. An alternative product must replace this
range argument as well as encode the desired equations.

## Two independently coded factors

A finite quadratic system can be bilinearized exactly: take left
coordinates X_i and right coordinates Y_i, impose equality between
the two copies, and replace every quadratic monomial by X_i Y_j.
Once the two unit coordinates equal one, a multiplication gate is
X_iY_j-X_k*delta_R=0, an addition is
(X_i+X_j-X_k)*delta_R=0, and a copy is
X_i*delta_R-delta_L*Y_i=0. This is a valid algebraic representation;
the difficulty is expressing its many rows as selected coefficients
of just one product P(T)Q(T), with inexpensive code tests.

### A concrete obstruction to the simplest routing

Suppose each logical variable occurs once per factor, with left
weight a_i and right weight b_i, and each factor has one unit
coordinate. To put the two terms of every copy equation at the
same coefficient requires

    a_i+b_delta=a_delta+b_i,
    hence b_i-a_i=b_delta-a_delta for every i.

An addition row using the same right unit coordinate then requires

    a_i+b_delta=a_j+b_delta=a_k+b_delta,

so its three variable weights coincide. Their values become a sum
in one code digit and cannot be decoded independently. Fresh
occurrences alone do not fix this particular scheme: the same
single-unit copy equations force equal weights for the occurrences
of a given variable. This obstruction concerns this direct routing,
not bilinear encoding in general.

### A translated-unit construction that does avoid that obstruction

Let the two fixed support polynomials be

    L(T)=sum_i T^a_i, M(T)=sum_j T^b_j,

and let X(T),Y(T) have the respective variable values at those
positions. For a shift h define

    P(T)=X(T)+T^h L(T),
    Q(T)=Y(T)-T^h M(T).

There is the exact identity

    P Q = X Y + T^h(LY-XM) - T^(2h) L M.        (1)

If a_i+b_j is unique among the relevant pairs, the coefficient in
the middle term at a_i+b_j+h is Y_j-X_i. Thus arbitrary left/right
copies can be tested without imposing equality of the two weights.
The shifted indicator polynomials supply known unit coordinates at
many locations. This is a concrete route around the preceding
obstruction, not merely a restatement of bilinearization.

To realize a multiplication gate in this product one would arrange
a collision of a lower product term X_iY_j with a selected middle
term that subtracts its output. Addition constraints can use
collisions among middle terms. This requires a support theorem:
all intended collisions must be realized while every undesired
lower, middle, and upper term misses every tested target. The
original Sidon support cannot do this unchanged, because it was
designed to prevent precisely these collisions.

### An optimistic arithmetic budget for this concrete prototype

For a first budget, suppose T^h evaluates to the existing q, and
reinterpret the two fixed decoded codes as L(B)=ell and M(B)=e.
Let the two variable-code integers be X=x+g and Y=h_code. The
existing e*q register may then be reused. The additional arithmetic
needed to form the translated factors and combine the variable
codes is

    ellq=ell*q,
    P=X+ellq,
    Q=h_code-eq,
    hq=h_code*q,
    G=g+hq.                                   (5 instructions)

The first mask could use G and the already calculated S2=ell+e*q:
its indicator is now the packed union of the two variable supports.
At the level of the displayed polynomial arithmetic, delete

    C2=C*C, Omega=lambda-e, P1=Omega*C2

and insert P1=P*Q. Keep the positive offset and use an appropriate
sign in sigma. This deletes three instructions and inserts one.
Together with the five instructions above, the prototype has

    97-3+1+5=100 instructions,

before any additional range constraint or routing correction. This
is an exact local instruction comparison, conditional on the stated
reuse; it is not a correctness or feasibility claim for a complete
100-operation system. Even this optimistic version costs three more
operations than the current certificate.

There are two further obstacles that the optimistic budget omits.

* With the present degree separation, all variable weights lie far
  below L, while h=L when T^h=q. The lower product band and middle
  copy band are disjoint. They cannot realize a gate that subtracts
  a linear output from a quadratic product. A different band layout
  or an additional, smaller shift value must be encoded. Enlarging
  the layout may require longer packed blocks and another power.
* Q is a signed quantity. Positivity of offset+P*Q, or offset-P*Q,
  does not separately bound the two positive input codes. In
  particular, cancellation or a factor of the favorable sign can
  permit an arbitrarily large factor. The previous inference
  C^2<offset from positive Omega is unavailable. Separate code
  bounds and possible quotient aliases must be addressed before
  applying the Pell or binary no-carry arguments.

The translated-unit identity nevertheless gives a more promising
research target than the naive product: find a uniform local circuit
layout whose copy and gate terms share these three bands, then seek
a way to absorb the fixed translations into the code equations.
Saving an entire fixed-code test, rather than only replacing the
square by a product, would be needed to offset the present overhead.

## Quartic sum-of-squares bundling

For integer residuals F_1,...,F_s, the equation

    R=sum_j w_j F_j^2=0, with all w_j>0,

is exactly equivalent to their simultaneous vanishing. If the F_j
are quadratic, R is quartic. A complementary coefficient polynomial
can therefore encode a SINGLE zero test as one coefficient of
D_code(T) C(T)^4. The outer circuit then needs only one target
position, rather than the union of all equation rows.

This route must handle the constant-one coordinate explicitly. One
possibility is to put a literal one at weight one:

    C=x+B+g.

It costs one addition more than C=x+g and avoids a homogeneous
all-zero unit assignment. An unused dummy coordinate can make g
positive when all represented witnesses are zero. The variable
indicator must exclude the literal-one position.

### Keeping quartic coefficients bounded by primitive normalization

There is a useful exact normalization that avoids a blanket factor
24 in some rows. For a multiplication residual with four distinct
coordinates,

    12(XY-W*delta)^2,

division of its coefficients by the corresponding coefficients in
C^4 gives the values 2,-1,2: the square-pair monomials have
multinomial coefficient 6, and the four-distinct monomial has
coefficient 24. For a linear residual homogenized by delta,

    6((X+Y-W)*delta)^2,

the divided coefficients are plus or minus one, provided X,Y,W and
delta are distinct. Copied operands and bounded fan-out can prevent
unbounded accumulation of identical monomials across rows.

Unit and constant rows need separate treatment. For example,
6(XY-delta^2)^2 has divided coefficients 1,-1,6. A single such
equation forces positive integer X,Y to be one when delta=1; its
copies can distribute that unit through a circuit. This offers a
concrete bounded-coefficient quartic normalization, but a complete
fan-out and monomial-overlap proof would still be required. The
target also needs a carry-tolerant centering term. None of these
observations establishes the desired final mask test by itself.

### The instruction tradeoff before coefficient decoding

With fixed numerals free, an elementary quartic version costs:

* one extra multiplication for C4=C2*C2;
* one extra multiplication for B=H*b^4 instead of H*b^2, to bound
  the quartic coefficient sums;
* one extra addition for the literal-one code C=x+B+g;
* one fewer multiplication if the third mask is a single already
  available power times its mask coefficient, instead of
  theta*(ell*q^4).

Thus even if the target mask coefficient were shared for free,
this concrete substitution starts at 97+1+1+1-1=99 operations.
A separate narrow target coefficient, such as B-2, costs another
addition when the coefficient-code modulus is B-Z with Z different
from two, bringing this local prototype to 100.

The wider coefficient alphabet and the target zero test cannot be
identified without proof. A mask B-Z permits all digits below Z.
For a constant contradictory residual, the SOS constant coefficient
is itself part of the fixed coefficient code. A permitted nonzero
target can therefore remain below Z. Scaling all residuals also
scales the coefficient alphabet; it does not automatically make
every nonzero SOS value exceed the mask's allowed range. A narrower
third mask avoids this particular issue but has the stated cost.

### The coefficient-alias obstacle survives SOS bundling

More significantly, the current combined coefficient equation gives

    ell=ell_0(B)+a_alias*q,
    e=e_0(B)-a_alias.

The high part of theta*ell is what forces a_alias=0. If the third
mask is replaced by one fixed target, that high part disappears.
Keeping just the former low target proof is therefore unsound: it
has not proved that the supplied coefficient code is e_0(B).

A new range constraint that recovers both codes separately, or a
new mechanism that tests the alias, is required. Restoring such a
constraint costs additional arithmetic in the straightforward
versions. In particular, the documented universal-collapse example
rules out obtaining it by simply deleting the packed upper bound.

## Result of this pass

The translated-unit identity (1) is a concrete new way to place
copy equations inside a two-code product. It removes the elementary
single-unit routing obstruction, but its explicit current budget is
100 before the missing layout and range work. The quartic route
does reduce the number of target positions, and primitive
normalization gives useful small divided coefficients, but its
present arithmetic budget is at least 99 for the specified literal-
unit version, before resolving the alias; the separate narrow-mask
version starts at 100.

These are proof barriers and budgets for particular constructions,
not impossibility results. No new certificate below 97 is asserted.
The structural opportunity is to eliminate or intrinsically decode a
whole fixed code while retaining a single bounded carry test; a bare
replacement of C^2 by two factors, or of many rows by an SOS, does
not yet accomplish that.
