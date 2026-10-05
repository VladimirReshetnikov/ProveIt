# Pascal review of the opposite-shear doubling obstruction

**PASS within the stated finite-trigonometric full-action scope.** I read the complete root-authored proof and metadata receipt, independently checked the direct fixed-point calculation, and checked the dilation-three construction. No mathematical correction is requested.

The frozen author files are:

| File | SHA-256 |
|---|---|
| /tmp/markov_opposite_shear_doubling_obstruction.md | 9815304fec5f0ad4e5534ad7044ba275454e6bcf766e0d6121c583ef3fbe4f09 |
| /tmp/markov_opposite_shear_doubling_obstruction.json | 2437a57f6fd1367c330d6dd8e7f4f2be93449652aba6a4dd09212457fba8a7a7 |

I supplied the convex-combination argument during drafting. This review additionally checks the root's independent determinant/threshold proof, the exact matrix conventions, the family consequence, and the sharp upper construction. The contribution history is correctly disclosed in the author note.

## Exact actions and both proofs

The assumptions are independent real finite-trigonometric f,g, continuous strictly positive normalized doubling masks a,b, positive scales lambda,mu, and opposite real shear parameters s<0<t:

    T_a f=lambda*f, T_a g=lambda*(g+s*f),
    T_b f=mu*f,     T_b g=mu*(g+t*f).

The convex weight theta=mu*t/(mu*t-lambda*s) lies strictly between zero and one. The mask c=theta*a+(1-theta)*b retains all mask hypotheses, and its full action is nu*I with nu=theta*lambda+(1-theta)*mu>0. The change of basis F=-s*f,G=g is invertible and makes a act as lambda*D. Thus the previously proved all-positive-scale identity/decrement obstruction applies, including equal scales. The family consequence for opposite shear signs, or for zero and nonzero shear, follows under this same full-action convention.

For lambda!=mu, I independently obtained the author's identity with delta=mu-lambda and kappa=(lambda*s-mu*t)/delta:

    F*G(z^2)-G*F(z^2)
      =kappa*F*F(z^2)-lambda*(kappa+s)*F(z^2)^2.

Here kappa+s=mu*(s-t)/delta. At z=1 the finite order r of F makes F(z^2)/F(z) regular with value 2^r. A pole of G/F cannot disappear in its doubling difference, since its principal multiplier is 2^(-ell)-1, which is nonzero. The resulting equality is precisely

    2^r = [t/(t-s)]/lambda + [-s/(t-s)]/mu.

These are strictly positive weights summing to one. For distinct positive scales, lambda and mu therefore lie on opposite sides of 2^(-r).

The normalized common-eigenfunction equations independently force

    (lambda*2^r-1)/a(1/2)
      = (mu*2^r-1)/b(1/2) = (B/A-1)/2,

where f(x)=A*x^r+O(x^(r+1)), A!=0, and the shifted expansion is f(x+1/2)=B*x^r+O(x^(r+1)), with B allowed to vanish. The shifted order bound follows from the original equation and the locally nonzero mask coefficient; no mask derivative is assumed. Positive denominators make opposite signs impossible. This covers r=0, repeated zeros, and every common Laurent factor.

The alternative equal-scale argument is also sound. Away from eigenvalue one, finite-eigenfunction mask uniqueness applies. At eigenvalue one, the nontrivial Jordan action would give T_a^n g=g+n*s*f, contradicting the uniform-norm contraction of a normalized positive operator.

## Sharp dilation and computational limits

I checked the displayed dilation-three masks using the exact coefficients a_(3k-m)-a_(3k+m). They yield D/5 and U/5 on (sin(theta),sin(2theta)); frequencies outside the span are excluded by the support bound, and sine oddness removes the constant mode. The plus mask is the half-period translate of the minus mask. Their numerator polynomials are (4u^2-1)^2+2(1-u) and its u -> -u reflection, with the stated strict lower bound.

Thus, among integer dilations b>=2, the minimum for this full opposite-shear pair is three even when positive scales may be chosen independently. Equal scales in the upper example are allowed in that larger class. This proves no denominator minimum over other encodings and no arithmetic-operation, witness, polynomial-degree, guarded-program or universal-history improvement.

The scope excludes arbitrary continuous or smooth-flat coordinates, nonnegative masks with zeros, unnormalized operators, changing charts, and actions required only on selected lines. The separate guarded ZERO/DEC construction is consistent with the theorem because its zero operator is rank one on the whole coordinate space.

## Read evidence and execution boundary

The all-scale fixed-point note was read in full, SHA-256 4d3393be942ad20441f49c4846f9eba7e328d9b065fc88c2d2c73e2bfa36f1fb; the common-scale note was read in full, SHA-256 baf4667547145049a6e2a842f6c337e25b4a075a7ea18c81bfa22ebd07b7e063. For the upper construction I read markov_sine_lift.md lines 14–34 and 118–162 directly and checked its formulas, SHA-256 7b30acebde3c5576773e92030242e4e8db1d00530fa9d7733b4ac8796270d1b2. This is not a fresh certification of every claim in that 192-line predecessor.

No author, predecessor, archived, supplied, frozen or copied program, helper, source array or builder was executed or imported. No numerical search or repository/Git mutation occurred. The only execution supporting this review was ordinary read-only byte metadata. The final note contains no identified false claim requiring a retained correction; the requested clarification that oddness removes the constant mode was applied before freeze.
