# A linear sign penalty for simultaneous Pell orientation

This note is an ordinary arithmetic proof. It supplies a replacement
certificate under the same retained hypotheses as source package 176 and
the incoming Direct_Integer_Elimination composition. It does not assert
an unconditional polynomial identity between the old and new equations.

## Lemma

Let A be an integer, |A| > W^W, W >= 258, D=A-1, and
b=floor(sqrt(W-1)). Suppose p<=15 norm-one Pell pairs have already been
classified, without using the orientation certificate, as

    (X_i,Y_i)=epsilon_i (X_{nu_i}(A),Y_{nu_i}(A)),
    epsilon_i in {1,-1}, |nu_i|<=b, |k_i|<=b.

The signed-index Pell polynomials satisfy
X_n(A)=1 and Y_n(A)=n modulo D. For any positive integer alpha put

    Omega_alpha = sum_i [alpha*(1-X_i)+(Y_i-k_i)^2].

Then modulo D this is congruent to the nonnegative integer

    o_alpha = sum_i [alpha*(1-epsilon_i)
                            +(epsilon_i*nu_i-k_i)^2].

For alpha=1, o_alpha=0 if and only if every epsilon_i=1 and nu_i=k_i.
Moreover 0<=o_1<=p*(2+4*b^2)<=90*b^2. Since D is nonzero and
|D|>=W^W>90*b^2, the single divisibility condition D | Omega_1
is therefore equivalent to canonical signs and requested indices.
Completeness follows directly from the canonical congruences.

The standalone divisibility equation is Omega_1-D*z=0. It is quadratic
in the raw X,Y,k coordinates and uses exactly the same one quotient z
as the earlier squared-sign certificate.

## Joint power certificate

Retain the at most five bases n_j and at most seventeen requests from
package 176. For each group let

    T_j=2*A*n_j-n_j^2-1,
    E_j=sum_i((m_i-X_i+A*Y_i)^2-Y_i^2)
                      -2*n_j*sum_i Y_i*(m_i-X_i).

All requested bases, indices and outputs have square less than W. Use
exactly the old joint residual with its orientation numerator replaced:

    Omega_1*product_j T_j
      +D*sum_j n_j*E_j*product_{l!=j} T_l
      -z*D*product_j T_j=0.                         (L)

All denominators are nonzero. At zero bases T_j=-1; at nonzero bases
|T_j|>W^W and n_j/T_j has sign(A). Also D has sign(A).

As in the source proof, choose the mathematical clearing integer
C=product_{j:n_j!=0} n_j^b and let

    d_i=C*m_i-epsilon_i*(C/n_j^b)*n_j^(b+nu_i).

The power congruence and (L) imply that

    C^2*o_1/D + sum_{j:n_j!=0} sum_i n_j*d_i^2/T_j

is an integer. Its nonzero summands all have sign(A). The existing
bound |C|<=b^(5*b), |d_i|<=2*b^(6*b), gives

    C^2*o_1 + sum |n_j|*d_i^2
      <=90*b^(10*b+2)+68*b^(12*b+1)
      <=158*b^(12*b+2)
      <W^(6*b+2)<=W^W.

Thus the displayed integer has absolute value below one, so it is zero.
Its same-sign summands vanish separately. Hence all epsilon_i=1 and
nu_i=k_i, and every nonzero-base request is the exact signed power.
This uses the bounded classified indices before canonicality, as required.
The old zero-base bootstrap and quotient restoration then apply unchanged.

For completeness, canonical pairs make D divide Omega_1, while exact
nonzero-base powers make T_j divide E_j. Their integer quotient sum
supplies z in (L). No pairwise coprimality of the denominators is used.

## Exact algebraic relationship and limitation

For each pair the old numerator was

    (X-1)^2+(Y-k)^2.

The new one is 1-X+(Y-k)^2; new minus old is X-X^2.
There is no reason for that difference to vanish as a polynomial or on
arbitrary norm-one tuples. On canonical Pell tuples it is divisible by
D, and the quotient variable changes accordingly. The proof is an
existential zero-set equivalence under the retained frame and raw-index
classification hypotheses, not equality of the two polynomials.

The source's norm-reduced old orientation has a Z^2 term for Z=A*Y.
The new direct expression has no X^2 or Z^2 term. It retains the same
variables and degree before further projection but removes one square
per principal pair. Those changes can improve circuit size and may
improve projected degree depending on the chosen elimination schedule.

The coefficient alpha=1 is the least positive integral weight within
this affine-sign/squared-index family. Alpha=0 loses sign authentication:
epsilon=-1 and nu=-k then has zero squared-index penalty.

## Provenance

Raw-index classification and bounds: package
176-oriented-pooling/proofs/JOINT_POOLING.md, drawing on the squared
semantic anchor from source 135. The exact prototype uses
ConZFC_Direct_Integer_Elimination_2026-10-25/joint209.json and its frozen
anchor219.json at repository snapshot
b42c796d1f5de9912a576bc2fd77b778ae7402bf. The unbounded new lemma above is
independent of finite circuit checks; inherited C222/ZF/ZFC calibration
is unchanged.
