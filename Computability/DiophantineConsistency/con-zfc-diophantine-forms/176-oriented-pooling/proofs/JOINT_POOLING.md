# Joint signed-index authentication and exact-power recovery

This is a further theorem beyond the all-five-base pool in
`ORIENTED_POOLING.md`. It combines a separate signed-index
authentication quotient with the power quotients. The simultaneous proof
uses bounded *classified* Pell indices before they have been identified
with the requested indices. It does not assume the orientation that it
is intended to prove.

## 1. What the retained squared-anchor theorem supplies first

At the actual signed Pell parameter A, let (X_i,Y_i) be the fourteen raw
principal norm-one pairs. The unchanged frame yields

    W>=258, |A|>W^W, and k_i^2, n_j^2, m_i^2, h^2 < W.

Put b=floor(sqrt(W-1))>=16. The squared semantic anchor and its auxiliary
comparison equations, BEFORE the global signed-orientation pool is used,
prove that every pair's positive classified index is at most |h|<=b.
This exact order appears in source135's `ORIENTATION_FIRST_PROOF.md`,
section `A signed nominal index in the squared anchor`. That argument
first proves the anchor index i=|h| from comparison residues; the squared
ordinate guard bounds the other classified indices by i.

Therefore each raw pair has a representation

    (X_i,Y_i) = epsilon_i * (X_{nu_i}(A),Y_{nu_i}(A)),
    epsilon_i in {+1,-1},   nu_i in Z,   |nu_i|<=b.              (1)

Here X_k,Y_k on the right are the canonical Pell recurrences, not the
unknown raw coordinates. This is ordinary classification at |A|, rewritten
at the signed parameter. At index zero one can use nu_i=0 and either
epsilon_i; it still represents both points (+1,0),(-1,0).

## 2. One polynomial residual

Retain the five base groups and all request ports from the preceding note.
The raw pair for a request is one of these fourteen principal pairs.
Put

    D = A-1,
    Omega = sum_over_principal_pairs [(X_i-1)^2+(Y_i-k_i)^2],
    T_j = 2*A*n_j-n_j^2-1,
    H_j = sum_over_requests_in_j Y_i*(m_i-X_i),
    S_j = sum_over_requests_in_j ((m_i-X_i+Z_i)^2-Y_i^2),
    E_j = S_j-2*n_j*H_j,       Z_i=A*Y_i.

Require only the following residual, with one integer z:

    Omega*product_j T_j
      + D*sum_j n_j*E_j*product_{l != j} T_l
      - z*D*product_j T_j = 0.                               (J)

All denominators named in the proof below are nonzero. D has sign(A),
and |D|>=W^W. A zero base has T_j=-1. A nonzero base has
|T_j|>W^W and n_j/T_j has sign(A).

Under the retained frame, anchor-classification, and norm/gate hypotheses,
(J) is equivalent to BOTH:

1. Every raw principal pair is exactly (X_{k_i}(A),Y_{k_i}(A)).
2. Every request at a nonzero base is the exact integer signed-index
   power m_i=n_j^{k_i}; bases with |n_j|>=2 force k_i>=0.

As before, zero bases impose no power condition. The existing semantic
bootstrap subsequently proves that all actual application bases are nonzero.

## 3. Soundness without a circular canonicality assumption

Modulo D=A-1, the signed recurrence satisfies

    X_nu(A)=1,   Y_nu(A)=nu.

Thus by (1), Omega is congruent modulo D to the nonnegative integer

    o = sum_i [(epsilon_i-1)^2+(epsilon_i*nu_i-k_i)^2].        (2)

For a nonzero base n_j, the raw pair gives the modular identity

    X_i+(n_j-A)*Y_i = epsilon_i*n_j^{nu_i} modulo T_j.       (3)

The exponent nu_i in (3) is a bounded classified index, NOT the requested
index k_i. Both signs are allowed; negative powers make sense because
gcd(n_j,T_j)=1.

Let delta_i=m_i-X_i+(A-n_j)*Y_i. The same polynomial identity as before is

    sum_i delta_i^2 = E_j-T_j*sum_i Y_i^2.                  (4)

Dividing (J) by D*product(T_j), and then using (4), says that

    Omega/D + sum_j sum_i n_j*delta_i^2/T_j

is an integer. Let C be the product of n_j^b over the NONZERO base blocks.
For request i in such a block, define the integer

    d_i=C*m_i-epsilon_i*(C/n_j^b)*n_j^(b+nu_i).

All exponents are nonnegative, C is nonzero, and (3) gives
C*delta_i=d_i modulo T_j. Combining this with (2), multiplication by C^2
shows that

    V=C^2*o/D + sum_{j:n_j != 0} sum_i n_j*d_i^2/T_j         (5)

is an integer.

Every term in (5) has the same sign, sign(A), or is zero. No pairwise
coprimality of D,T_j is used. In particular C may share factors with D.

The fourteen pairs can be bounded conservatively by fifteen. Since both
|nu_i| and |k_i| are at most b,

    0<=o<=60*(1+b^2)<=120*b^2.

There are at most five nonzero bases, so |C|<=b^(5*b). As in the preceding
theorem, with at most seventeen requests,

    sum |n_j|*d_i^2 <= 68*b^(12*b+1).

Consequently

    C^2*o+sum |n_j|*d_i^2
      <=120*b^(10*b+2)+68*b^(12*b+1)
      <=188*b^(12*b+2)
      <W^(6*b+2)
      <=W^W.

The strict inequality uses 188<W and b^2<W; the last uses
6*b+2<=b^2+1<=W for b>=16. Since every active denominator has magnitude
at least W^W, |V|<1. Hence V=0, and the common-sign property gives o=0
and d_i=0 for every active power request.

Equation (2) now forces epsilon_i=1 and nu_i=k_i for every principal
pair, authenticating all signed indices and both coordinate signs.
The equations d_i=0 recover every nonzero-base power at those indices.
Negative indices at bases with absolute value at least two are excluded by integrality as before.
This proves both assertions simultaneously.

## 4. Completeness and original quotient restoration

Canonical pairs make each X_i-1 and Y_i-k_i divisible by D, so D divides
Omega. Exact nonzero-base powers make T_j divide delta_i and therefore
E_j. Thus

    z=Omega/D + sum_{j:n_j != 0} n_j*E_j/T_j

is an integer satisfying (J). At zero bases the corresponding summand is
zero. This proves the reverse direction of the general theorem.

For an application zero, the same source bootstrap as for P207 recovers
F=t^t, nonzero B and BH, x>=1, large q and q+1, and all exact arithmetic.
Restore the old orientation quotient as Omega/D; restore the original
three individual power quotients and two K,L pairs as in the previous
note. If the centered source orientation row has been changed by integer
row operations, restore its quotient using the explicit recorded row
combination; the other retained rows vanish, so the same divisibility
and restored zero follow.

## 5. Exact P216 instance and cost

Delete the same ten coordinates/rows as in P207, AND delete coordinate201
(`cap.pooled_quotient`) and row142 (`cap.pooled_index_residue`). Retain all
other142 quadratic rows. Add one new z and residual(J). The result has

    206 unrestricted integer coordinates;
    143 residuals;
    one sum-of-squares polynomial of exact degree26.

For Omega use the literal sum over the fourteen UNIQUE pairs in the
previous request table, taking only requests0,3,5,7,8,9,10,11,12,13,14,
15,16,17. These cover respectively the requested indices
t,F+t,a,b,c,d,S,y+1,Sp,u,x,vq,C,h exactly once. Use X=D_i+Z_i in the
literal centered coordinates. This makes Omega an explicit degree2
polynomial, with no need to treat a transformed row as a sum of squares.

The frozen parent row-identity certificate must check that this Omega
agrees with its orientation numerator modulo the retained norm/frame
rows. This is an exact finite verification obligation; it must not be
assumed merely from the row label.

The new residual has degree13. In original P216 IDs, the degree13 monomial

    x0^2*x4^2*x94^4*x130*x134*x184*x186^2

has coefficient -2. This is D times the earlier degree12 coefficient;
Omega*product(T_j) and z*D*product(T_j) have degree at most12 and cannot
cancel it. Hence its square has exact degree26. All other residual squares
have degree4, so the complete polynomial has exact degree26.

This construction combines the previously separate orientation and power
authentications; a claim of literature-wide priority would require further
review. Its proof relies on the inherited, noncircular raw-index bound
and calibrated source semantics, with those exact dependencies stated.
