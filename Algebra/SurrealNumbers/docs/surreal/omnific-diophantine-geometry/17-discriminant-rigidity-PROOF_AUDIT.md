# Proof and hypothesis audit

This is an internal audit, not independent refereeing or formal verification.

## 1. Universal root-velocity certificate

For a monic separable P and coefficient velocity Q, the divided difference
S(X,Y) = (Q(Y)P'(X)-Q(X)P'(Y))/(X-Y) is a polynomial, symmetric in X,Y and
linear in Q's coefficients. The identity
w_ij = S(r_i,r_j)/(P'(r_i)P'(r_j)) has the stated sign.
The product of all P'(r_i) is (-1)^(n(n-1)/2) Disc(P). Thus Disc(P)^2 clears
each denominator. Elementary symmetric functions in all unordered pairs are
symmetric in the roots and homogeneous in the velocity coefficients. The
fundamental theorem on symmetric polynomials gives the universal certificate.
No inference from integrality to membership in A is used.

## 2. The decisive ideal intersection

All nonleading coefficients of the velocity polynomial are in I because each
has positive degree in the coefficient derivatives, which lie in I. Division
by a nonzero constant discriminant is legal in the coefficient field. Each
velocity has nonnegative valuation. Hence these coefficients are also in the
opposite valuation ring and are zero. Merely differentiating the discriminant
would give only a vanishing sum and would not suffice.

## 3. Constants and translation

Every nonzero exponent is detected by some rational linear functional on the
divisible hull. Killing all Euler derivations therefore makes every root gap
constant. Subtracting the mean of the roots gives a constant centered
polynomial. Constant extraction recovers exactly P0, not an unspecified
polynomial over an enlarged coefficient field. The unique shift is
-(a1-ct(a1))/n. It lies in I even when 1/n is not in the arithmetic subring D.

## 4. Finite étale units

The Euler derivation extends to B by the square-zero formal étale lifting
property. Its reduction is a k-derivation of a finite separable k-algebra and
therefore vanishes. For a unit u, y=u^(-1)D(u) is in I B. The multiplication
characteristic polynomial reduces to T^N; all nonleading coefficients lie in I.
Every generic conjugate of y is a logarithmic derivative in the Hahn splitting
field, so those same coefficients lie in the opposite valuation ring. They
vanish, y is nilpotent, and B is reduced because it injects into its separable
generic fiber. Hence D(u)=0.

Finite projectivity, not global freeness, is used for this characteristic
polynomial. Local bases, base-change compatibility, and Cayley-Hamilton are
spelled out. No global primitive-element assertion is assumed.

## 5. Algebraic constant subalgebra

The algebraic constants form a subalgebra. Their generic images lie in the
algebraic closure of k. This identifies them with the joint Euler kernel.
Their characteristic-polynomial coefficients are ordinary constants. A
constant element vanishing in B/I B consequently has characteristic polynomial
T^N and is zero. Thus C_B embeds in the N-dimensional fiber. It is finite
reduced over a characteristic-zero field, hence finite étale. Coefficientwise
linear independence proves the injection A tensor_k C_B -> B.

The proof does NOT make this injection surjective without the explicit
unit-generation or monogenic hypotheses.

## 6. Normal matrices

The polynomial theorem gives eigenvalues h+c_i. Distinct constant gaps make
the Lagrange projectors one-sided Hahn matrices. Normality makes each projector
normal. A normal idempotent is self-adjoint for the positive Hermitian form;
its entries have bounded squared modulus. Bounded one-sided Hahn entries are
constants. This is the additional step needed to pass from fixed eigenvalues
to fixed eigenspaces and entries.

## 7. Class boundary

The polynomial and finite-matrix statements for full surreal/surcomplex
classes are proved after collecting their finite input supports into a
set-sized divisible exponent group. All supports remain sets. The abstract
finite étale algebra theorem is stated for set-sized rings/modules. There is
no invented proper-class finite-projective formalism or hidden large-cardinal
hypothesis.

## 8. Sharpness examples checked

- Full two-sided Hahn coefficients admit roots 0,x,r with r(x-r)=1/x and
  discriminant 1, while an infinite root gap persists.
- In characteristic p, X^(p^2)+u X^p+X has constant nonzero discriminant but
  is not a translate of its constant-term polynomial.
- X^2(X-s) shows failure with zero discriminant.
- An upper-triangular nonnormal matrix has constant spectrum but varying entry.
- The finite free reduced algebra k[s,Y]/(Y^2-s^2-1) has a nonconstant unit
  s+Y, inverse Y-s, and nonunit discriminant. Étaleness cannot be omitted.
- Over arithmetic coefficient rings, nonzero discriminant is distinguished
  from unit discriminant throughout.

## 9. Computational boundary

The recorded run passed 1,126 exact assertions. They check finite algebraic
identities, normalizations, and examples. They do not verify the all-degree
certificate, infinite Hahn support theory, formal étale arguments, or priority.
