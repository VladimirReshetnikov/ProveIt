# Independent review of the three-root recovery argument

This note reviews the new arithmetic projection only. It does not independently
reprove the inherited machine/compiler/ZFC-refutation calibration.

## 1. Valuation separation lemma

Let p be a prime. Let a_1,...,a_n and c_1,...,c_n be nonzero rational
numbers. Choose algebraic square roots alpha_i of a_i. Suppose the rational
numbers

    v_p(c_i) + v_p(a_i)/2

are pairwise distinct. If sum_i c_i alpha_i is rational, then every alpha_i
is rational. No assumption that the a_i are positive is needed; no
assumption that their valuations are even is needed.

Proof. The field K=Q(alpha_1,...,alpha_n) is a finite Galois extension of Q,
because it is the splitting field of a product of separable quadratic
polynomials. Choose a prime ideal P of its ring of integers above p. If e
is the ramification index, w=ord_P/e is an additive valuation on K which
restricts to v_p on Q. Thus

    w(c_i alpha_i)=v_p(c_i)+v_p(a_i)/2.

Every nonempty signed subset of these terms has a unique term of least
w-value. Such a sum is nonzero: divide by its least-valued term; the
remaining terms lie in the maximal ideal of the valuation ring, whereas
the divided sum is 1 plus an element of that maximal ideal.

For any sigma in Gal(K/Q), sigma(alpha_i)=epsilon_i alpha_i for
epsilon_i in {1,-1}. Since the sum is rational,

    0=sigma(sum_i c_i alpha_i)-sum_i c_i alpha_i
     =-2 sum_{epsilon_i=-1} c_i alpha_i.

The no-cancellation statement makes the changed set empty. Consequently
every alpha_i is fixed by every element of Gal(K/Q), hence lies in Q.

For standard background one may cite J. S. Milne, Algebraic Number Theory,
version 3.08 (2020), Theorem 3.29, Theorem 3.34, and section 7.9:
https://www.jmilne.org/math/CourseNotes/ANT.pdf . These are finite algebraic
number theory arguments formalizable in ZFC. The proof does not require
an effective construction of the prime ideal.

## 2. Verification of the required valuations

Use the intended literal normalization

    beta=2^1064921-1, J=3J3+1, q=beta J+1, W=4(3w3+1),
    X=qW, Y=(2v+1)q^3, a=(X+1)Y, H=4a+3,
    Delta=a^2+H, u=XY^2 k, A=u(u+k)+1,
    I=(2r+1)c^2, Q=I^2, delta=Q-1,
    B=(QV^2-1)/delta, Dm=1+Delta c^2.

Assume only the strong row Q=Delta(f^2-1) and the joint-guard conclusions
Q>1 and A>=1. The guard conclusions are proved without any deleted root
equation in the predecessor's integer/PROOF.md, section 4.

The coefficient port is beta=B-1, not B: B=2^1064921. Modulo 3, beta,
J and W are 1, whereas q and X are 2. Thus X+1 and a are 0 modulo 3.
Put b=XY^2. Then b is 0 or 2 modulo 3, so
A=b(b+1)k^2+1=1 modulo 3. Also H=0 modulo 3; H cannot be zero because
4a+3 is odd. Delta=0 modulo 3, and the strong row makes 3 divide I and
therefore 9 divide Q. Hence delta and QV^2-1 are both -1 modulo 9.
The rational B is a 3-adic unit. Dm is 1 modulo 3.

In every extension of the 3-adic valuation, the three terms

    3 sqrt(A), sqrt(B), sqrt(Dm)/H

therefore have valuations

    1, 0, -v_3(H),

which are pairwise distinct. All three radicands are nonzero. The lemma
applies before deciding whether B is positive.

## 3. Adjacent-coefficient descent is sufficient

The predecessor's lemma says: if Q>1 and V are integers and y is rational
with QV^2-(Q-1)y^2=1, then y is an integer. Its proof was independently
checked as follows. Write y=a/m in lowest terms, m>0. Then m^2 divides
Q-1. After taking absolute values, V>1 and y>0 give

    V'=(2Q-1)V-2(Q-1)y,
    y'=(2Q-1)y-2QV.

V' is integral; the same norm equation holds; y>V and QV>(Q-1)y give
-V<V'<V, and V'=0 is impossible. The reduced denominator of y' is m,
because 2Q-1=1 modulo m. Induction on |V| reaches |V|=1, where |y|=1.
This proves the claim. It needs no additional coprimality assertion.

Thus rational root recovery gives tau integral from tau^2=A, d integral
from d^2=Dm, and y integral from the adjacent-coefficient descent.

## 4. Carrier parity must be stated

Write D0=X+ac and

    s=(xi+3(2u+k)+2V)/2.

The intended common-root identity gives

    s+D0/H = 3 tau+y+d/H,

after choosing signs of the three roots. It follows that
gamma=(d-D0)/H=s-3tau-y is a half-integer. It is not valid to call it
integral at this point merely because xi is integral.

However, 2gamma is integral, Hgamma=d-D0 is integral, and H is odd.
Because gcd(2,H)=1, gamma is an integer. This supplies the omitted parity
step without imposing any new congruence condition on xi.

## 5. Resultant specialization

The main polynomial in gamma has leading coefficient H^2, which is
nonzero on every integer assignment. The substituted two-root polynomial
N16(xi-2gamma) has leading coefficient 16 delta^2, also nonzero after the
guard gives Q>1. Consequently vanishing of the resultant gives a genuine
common algebraic root, without a leading-coefficient-zero branch.

At that common root, the two-root norm factors over the field generated
by sqrt(A) and sqrt(B), yielding a signed sum of the three displayed
radicals equal to the rational s+D0/H. Sections 1--4 recover integral
tau,y,gamma and the original three root equations.

## 6. Exact boundary of this review

The argument above validates the additional projection from the proposed
16-variable system to 15 variables, assuming the exact intended
resultant polynomial is supplied. The algebraic resultant expansion,
the complete degree/count certificate, and the implementation are not
reviewed in this note.

The remaining reduction to the original integer interface also needs
the preliminary strong-rank fact c divides f^2-1 to restore the CRT
coordinates

    o=cT-fR, j=fT-1-(f^2-1)R/c.

That fact must be invoked only after the ordinary and main Pell roots
have been restored, and its proof must not use the deleted congruence
row cj-V-R=0. This dependency is explicitly outside the present
independent review.

## 7. Elementary square-class proof: no extended valuations required

The separation lemma has the following alternative proof, useful for the
final exposition. It uses the ordinary rational valuation v_p only; no
completion or extension of a valuation to a number field is needed.

**Lemma.** Let t_1,...,t_n be nonzero algebraic numbers with t_i^2 in
Q. If the numbers v_p(t_i^2)/2 are pairwise distinct and their sum is
rational, then every t_i is rational. Signs may be included in the t_i.
Zero terms may be discarded.

Partition the t_i by the square class of t_i^2 in Q*/Q*^2. In one class,
choose a root alpha with alpha^2=d in Q*. Then every member is
t_i=r_i alpha for some r_i in Q*, and

    v_p(r_i)=v_p(t_i^2)/2-v_p(d)/2.

These valuations are distinct. Therefore the rational coefficient
sum r_i is nonzero: its summand of least valuation is unique. This last
claim is elementary arithmetic in Q, proved by scaling the least
valuation to zero and reducing modulo p.

Roots representing distinct rational square classes are Q-linearly
independent. Here is a finite Galois proof of that fact, including the
class of 1. Let K be their common splitting field and G=Gal(K/Q).
For a root alpha define chi_alpha(sigma) by
sigma(alpha)=chi_alpha(sigma) alpha; these are characters G->{1,-1}.
If two characters agree, their root ratio is fixed by every sigma and
is rational, so their square classes agree. Thus distinct square
classes give distinct characters. A minimal nonzero Q-linear relation
among such roots can be acted on by an automorphism distinguishing two
characters; subtracting a suitable sign times the original relation
eliminates one term but not the other, contradicting minimality.

The proposed rational sum is a Q-linear relation among the class of 1
and the nontrivial square classes. Independence forces the coefficient
of every nontrivial class to vanish. But the preceding unique-minimum
argument showed each nonempty class coefficient is nonzero. Therefore
no nontrivial class occurs, and every t_i is rational.

For the five-root construction apply this lemma to

    18 sqrt(F2), 6 sqrt(A), 2 sqrt(B), 2 sqrt(Dm)/H, 54w.

The first four half-valuations are 2,1,0,-v_3(H), respectively; the
last is at least 3 if w is nonzero because w^2 is an integer. These are
pairwise distinct. If w=0, discard it. This gives exactly the same
root-recovery conclusion as the number-field valuation argument, with
a shorter list of prerequisites.
