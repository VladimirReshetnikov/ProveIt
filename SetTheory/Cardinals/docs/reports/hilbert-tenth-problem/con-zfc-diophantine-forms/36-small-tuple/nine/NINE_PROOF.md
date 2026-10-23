# The nu=31 synthesis and its fixed coefficients

## 1. Precise result

Write L=5^32. The pinned package-30 polynomial F_30 has degree

    D = 120724 L + 366
      = 2810824662446975708007812866

in nine nonnegative integer unknowns. Its source degree certificate has
positive diagonal leading coefficient `2^274*z_index^2`. We construct an
exactly equal integer polynomial evaluator using 1,587 binary additions,
subtractions and multiplications: 708 additions, 22 subtractions, 857
multiplications. Multiplications by fixed numerals are charged.

Replacing every nonnegative coordinate n by p-1 gives a polynomial in nine
strictly positive coordinates with 1,582 gates. It has the same degree and
the same existence condition. The old internal +1 shifts cancel at six
coordinates and at the base b; the two remaining shifts cost two subtractions.

The new complete coefficient tuple supplied by this package can be used in
the same construction. It changes the polynomial's fixed coefficients,
including z and y, while preserving the dimension, degree and gate counts.
The recommendation is that coherent new instance. The original instance is
retained separately so that exact optimization and coefficient rebinding
are not conflated.

## 2. The source quartic and the index

Let Q be the sum of squares of the 22 quadratic residuals in
`source/quartic31.json`, with its 31 positive variables shifted by +1.
It is a nonnegative quartic over the natural numbers. Introduce a dummy
input x, which does not occur. Write the ordinary coefficients as p_alpha,
where alpha has 32 entries and |alpha|<=4. Put

    c_alpha = (4-|alpha|)! product_j(alpha_j!) p_alpha,
    expo(alpha) = sum_{j=0}^{31} alpha_j 5^j.

The finite list has 402 nonzero coefficient records, each an explicit
integer polynomial in the four compiler ports; the others are exactly zero.
This includes all degree-zero data and the dummy input coordinate. The
shifted quartic has nonzero constant term: at the positive all-one tuple,
its fifth source residual E-X(a-E) equals 1.

For the new port bit lengths b=(1012115,1016946,1012115,1012116), define

    H_alpha = sum_t |a_t| 2^(sum_j b_j e_tj)

when the record c_alpha has fixed-port terms
`a_t product_j port_j^(e_tj)`. Every actual port is strictly below its
corresponding power of two. Consequently |c_alpha|<=H_alpha. Exact finite
integer arithmetic verifies, for every record,

    H_alpha+1 < 2^4058127.

Set z=2^4058127 and

    y = sum_{alpha in N^32, |alpha|<=4}
          (z+c_alpha) (2z)^(L-expo(alpha)),
    u = sum_{j=1}^{31}(2z)^(5^j).

The y sum has exactly binomial(36,4)=58,905 terms. Every digit z+c_alpha
lies strictly between 1 and 2z, and all exponent positions are distinct.
This is the complete Jones index prescription; y is a fixed positive
integer. There is no oracle, unspecified index, variable exponent or new
existential parameter. A conservative binary-length bound for y is

    (4058128) (5^32+1).

The actual z payload is included. Materializing y is not required to define
the polynomial, and its recipe is not counted as additional variables.

## 3. Exact homogeneous evaluation

The hard part of evaluating the Jones equation is the fixed digit
polynomial

    e(B) = sum_{|alpha|<=4} (z+c_alpha) B^(L-expo(alpha)).

Put T=5^31 and form circuit registers, not new Diophantine coordinates,

    t_j=B^(5^j), 0<=j<=32,
    v_j=B^(T-5^j), 0<=j<=31.

Compute t_(j+1)=t_j^4 t_j, v_31=1,
and v_j=t_j^4 v_(j+1). These use shared fixed-power multiplication chains.
For every alpha with |alpha|<=4, the elementary exponent identity

    B^(L-expo(alpha))
      = t_31 * t_31^(4-|alpha|) * product_j v_j^(alpha_j)

holds. It remains an identity at B=0 because all exponents are nonnegative;
there is no division hidden in the displayed registers.

Let h_4 be the complete homogeneous polynomial of degree four in its
arguments. With w=(t_31,v_0,...,v_31),

    e(B)=t_31 [ z h_4(w)
                 + sum_alpha c_alpha t_31^(4-|alpha|)
                                      product_j v_j^(alpha_j) ].

The h_4 recurrence updates h_r <- h_r+w_j h_(r-1), r=1,...,4 in ascending
order, starting with h_0=1 and h_1=...=h_4=0. Ascending order is essential:
it gives repeated use of the current argument and hence complete homogeneous
polynomials rather than elementary symmetric polynomials.

The sparse correction is evaluated by recursive multivariate Horner:
choose a coordinate, split terms according to whether its exponent is zero,
factor one copy of that coordinate from the positive-exponent part, and
recurse. Every step is distributivity. The chosen deterministic heuristic
changes the evaluator only. Literal coefficient recipes become literals;
identical recipes share one fixed leaf. Both transformations are identities
in the four compiler ports.

The exact correction audit expands the constructed subcircuit over
Z[B,beta,K,MC,MF_source] and compares it with the prescribed coefficient
records term by term. It checks 675 symbolic terms, not merely evaluations
at random points. The complete-homogeneous recurrence and exponent identity
give the omitted zero-coefficient baseline exactly.

Finally, q=B^L and the geometric polynomial lambda are evaluated by

    lambda = product_{j=0}^{31}(1+t_j+t_j^2+t_j^3+t_j^4)
             * (1+q)*(1+q^2),
    1+t+t^2+t^3+t^4 = 1+t(1+t)(1+t^2).

This is sum_{r=0}^{4L-1} B^r by repeated geometric factorization. All
remaining Jones and tight-finalizer nodes are copied as inert polynomial
data and left unchanged. Thus this evaluator computes exactly F_30.

## 4. Existence equivalence and rebinding boundary

Package 30's fixed finalizer is the two-root norm

    F = (Theta^2-Omega^2(a0+V0^2 a1))^2
          -4 Omega^4 V0^2 a0 a1.

The source proof establishes V0,V1>=2 and
sqrt(|a0|)<=V0-1, sqrt(|a1|)<=V1-1 on every natural input assignment,
without assuming that the desired square or positivity tests already hold.
It proves F=0 equivalent to the two square tests, one divisibility test
and the positive Jones ratio margin. The four-factor complex-root
factorization covers negative candidate radicands and repeated square
classes; no independence of square roots is assumed. Every defining node
of this finalizer and every preceding Jones expression is preserved here.

The normalized quartic and the explicitly bounded index satisfy the
parameterized nu=31 Jones theorem. The quartic's compiler interface is
uniform in a complete authentic four-port tuple. Consequently, after the
new compiler adapter has established that interface for its tuple, the
same argument gives

    ZFC |- (there is no natural zero of F) <-> Con(ZFC).

The affine positive-coordinate version gives the corresponding theorem
over positive integers. Neither polynomial is asserted to have the same
existence condition over unrestricted integers. This imports the ordinary
Pell/compiler argument and literal K215 calibration; it does not claim that
the equivalence has been rebuilt in Lean or Rocq.

The exact degree is inherited for the original instance by polynomial
identity. For the new instance, the source leading-degree proof is uniform
in the valid index and its diagonal leader is 2^274 z^2>0. Therefore the
degree remains exactly D. No coefficient-height bound is silently substituted
for the actual fixed coefficient definitions.

## 5. Scope of the improvement

This result reduces the evaluator of the lowest-degree delivered
nine-variable polynomial by 253 gates and greatly decreases its fixed
index z when combined with the new compiler tuple. It does not establish
a new general nine-variable representation theorem, a smaller number of
variables, an optimal circuit, or the truth of Con(ZFC).
