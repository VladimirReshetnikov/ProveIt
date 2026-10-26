# Independent audit of the unrestricted-integer companion

The domain conversion proposed for the fourteen-positive-variable polynomial is valid:

    v = 1 + a_v^2 + b_v^2 + c_v(c_v+1),

with three independently quantified unrestricted integers for each of the fourteen parent variables v.

## Exact image of the substitution

For every integer c, c(c+1)>=0. Thus every substituted v is a positive integer.

Conversely, let v>=1 and n=v-1. The integer 4n+1 is not of the excluded form 4^a(8b+7) in Legendre's three-square theorem. It is therefore a sum of three integer squares. Reduction modulo4 shows that exactly one of the three square roots is odd. Permuting the roots, write the even ones as2a,2b and the odd one as2c+1. Then

    4n+1 = (2a)^2+(2b)^2+(2c+1)^2
          = 4[a^2+b^2+c(c+1)]+1.

Hence n=a^2+b^2+c(c+1). The substitution maps Z^3 onto Z_{>0}. Applying it independently in every coordinate proves equivalence between a positive zero of the parent and an integer zero of the companion. The construction is a surjection and is not claimed to be a bijection of witnesses.

## Variable and operation counts

There are exactly14*3=42 independent integer variables. Every coordinate replacement uses seven binary integer operations:

1. Square a.
2. Square b.
3. Form c+1.
4. Multiply c(c+1).
5. Add the two squares.
6. Add the pronic term.
7. Add1.

This is three multiplications and four additions per replaced variable. The full graph therefore has

    multiplications:37+14*3=79,
    additions:16+14*4=72,
    subtractions:12,
    total:163.

All fixed coefficients remain the parent tuple.

## Exact degree

Let P_150 be the nonzero leading homogeneous form of the parent, of degree150. The leading form of the substituted polynomial is

    P_150((a_v^2+b_v^2+c_v^2)_v).

This form is nonzero. Indeed, setting every b_v=c_v=0 gives P_150((a_v^2)_v); distinct monomials of P_150 acquire distinct doubled exponent vectors, so this polynomial cannot vanish identically. Consequently the degree is exactly300.

More concretely, the parent coefficient -8*beta^88 at

    J^88*z*gamma*i^4*eta^13*w^12*s^25*T^2*f^4

produces the same nonzero coefficient at

    a_J^176*a_z^2*a_gamma^2*a_i^8*a_eta^26*a_w^24*a_s^50*a_T^4*a_f^8

after setting the other two groups of coordinates to zero. Its total degree is300.

## Scope

This adds the classical three-square theorem to the already identified ordinary mathematical foundations. It does not improve the existing unrestricted-integer variable-count records and should be described as an explicit domain companion. The equivalence is formalizable in ZFC and uses no consistency assumption.

Independent reviewer: /root/direct_construction.

