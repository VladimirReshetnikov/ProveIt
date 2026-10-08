# Residue characteristic polynomials over truncated polynomial rings

Research notes for the current UnknotRecognition continuation. This is a
self-contained elementary specialization of Cayley--Hamilton and Frobenius;
no literature-wide priority claim is made. The sharpness construction and the
algorithmic applications should be stated with that attribution.

## Audit of earlier work

The pinned repository's synthesis/research_updates.tex and report 12 README
contain radical geometric-series inversion with a width-dependent cutoff, but
not the residue characteristic-polynomial annihilator below. Report 08 already
has canonical multiplicities and a finite radical perturbation formula; neither
should be advertised as new. The immediately prior continuation's
paper/splitting.tex restricts candidate endomorphisms to scalar F2 matrices and
uses stabilized binary kernels/images. Its ring-valued extension below is
distinct, though searching for such endomorphisms is not solved by this lemma.

## Ring and scalar Frobenius

Fix a prime p and positive integers b,r. Set

    R = F_p[x_1,...,x_b]/(x_1^p,...,x_b^p),
    J = (x_1,...,x_b), B = b(p-1).

Write rho:R -> F_p for the constant-coefficient map. The monomial basis is
x^alpha with 0 <= alpha_i < p. Consequently J^(B+1)=0, J^B != 0, and

    f^p = rho(f)

for every f in R: Frobenius kills every nonconstant monomial and fixes F_p.
These are statements about scalar elements of a commutative ring. The map
A -> A^p on matrices is NOT entrywise Frobenius and need not be additive.

## Theorem 1: a small annihilator from residue data

For A in M_r(R), put A_0=rho(A) entrywise and

    chi_0(t)=det(t I-A_0) in F_p[t].

Then

    (chi_0(t)^p)(A) = chi_0(A)^p = 0.

In particular A admits an explicitly computable annihilating polynomial of
degree pr with coefficients in F_p, independent of b.

Proof. Write chi_A(t)=sum_{i=0}^r c_i t^i, c_r=1. Determinants commute with
rho, so chi_0(t)=sum rho(c_i)t^i. Cayley--Hamilton over commutative rings gives
sum c_i A^i=0. Its summands commute with one another because each is a scalar
multiple of a power of the SAME matrix. Raising this equality to the pth power
therefore gives

    0 = sum c_i^p A^(pi) = sum rho(c_i) A^(pi)
      = (chi_0(t)^p)(A).

This argument does not assert Frobenius for arbitrary sums of noncommuting
matrices. It is valid even when entries of A have nonlinear monomials.

For an arbitrary field k of characteristic p with the same truncated ring, the
same proof gives chi_0(A)^p=0: c_i^p=rho(c_i)^p, and chi_0(t)^p has those
Frobenius-twisted coefficients. The displayed simplification of coefficients
to unchanged values uses F_p specifically.

## Theorem 2: a sharp radical nilpotence bound

Every N in M_r(J) satisfies

    N^L=0, L=min(B+1,pr).

For every b,r>=1 and prime p, there is such an N with N^(L-1)!=0. Thus the
universal nilpotence cutoff cannot be lowered for this class.

Upper bounds. A product of B+1 radical entries lies in J^(B+1)=0. Also
N_0=0, chi_0(t)=t^r, and Theorem 1 gives N^(pr)=0.

Sharpness construction. Put s=min(b,r). In an s by s upper-bidiagonal block,
put distinct variables x_1,...,x_s on the diagonal. There are s-1
superdiagonal positions. Label as many of these positions as possible with
the extra variables x_(s+1),...,x_b, each used at most p-1 times. Their number is

    e=min(s-1,(b-s)(p-1)).

Label the remaining s-1-e positions with diagonal variables x_1,...,x_s,
again using each at most p-1 times. This is possible because s-1 <= s(p-1).
Let a_i be the number of edges labelled x_i, and put zero in every other
matrix position; embed this block in M_r(R) if s<r.

For an upper-bidiagonal matrix with diagonal d_1,...,d_s and superdiagonal
y_1,...,y_(s-1), its (1,s) entry in the mth power is

    (y_1 ... y_(s-1)) h_(m-s+1)(d_1,...,d_s),

where h_k is the complete homogeneous polynomial, defined as zero for k<0.
Each weak composition of k corresponds to exactly one path: stay at each
vertex the specified number of times and traverse the superdiagonal edges
in their forced order. In particular each monomial of the distinct d_i has
coefficient one; there is no characteristic-p cancellation.

Choose the loop multiplicity at vertex i to be p-1-a_i, which is nonnegative.
The corresponding surviving monomial has degree

    D=(s-1)+sum_(i=1)^s(p-1-a_i)
      =s(p-1)+e
      =min(b(p-1),pr-1)=L-1.

Its coefficient is one and all variable exponents are below p, so N^D!=0.
For p=2 and b>=2r-1 the familiar particularly simple witness has r distinct
diagonal variables and r-1 distinct superdiagonal variables; its (1,r)
entry in N^(2r-1) is their product.

## Nilpotent residue rather than radical entries

If A_0 is nilpotent, then A^(pr)=0. If its nilpotence index is s, then A^s
has entries in J and the ideal bound also gives

    A^min(pr,s(B+1))=0.

The pr cutoff is sharp already with b=1 when s=r: take the companion matrix
of t^r-x_1. It has A^r=x_1 I, A^(pr)=0, and A^(pr-1)!=0. Its residue is a
single nilpotent Jordan block. Do not claim simultaneous sharpness of the
combined bound for every prescribed tuple (b,r,s) without further proof.

## Corollary: exact block inverses

For N in M_r(J),

    (I+N)^(-1)=sum_(j=0)^(L-1)(-N)^j,
    L=min(b(p-1)+1,pr).

Over F2 all signs are positive. At p=2 this changes the previous b+1 cutoff
to min(b+1,2r). The inverse can be evaluated by Horner, or by doubling a
power-and-partial-sum pair. The latter takes O(log L) matrix products; the
theorem saves the exponent/degree as well as the number of terms, but must not
be compared with a needlessly linear implementation if the baseline already
uses doubling.

For arbitrary A with invertible residue, write chi_0(t)=sum c_i t^i,
c_0!=0. Theorem 1 gives the alternative closed formula

    A^(-1) = -c_0^(-1) sum_(i=1)^r c_i A^(pi-1)

over F_p. For p=2, c_0=1 and the minus sign disappears. It uses only the
characteristic polynomial of an r by r matrix over the base field, not a
determinant over R. All intermediate matrix products still have costs
depending on the encoded coefficient vectors. Polynomial degree O(r) is not
a claim that those coefficient vectors or the block itself are succinct.

## Theorem 3: constructive Fitting projectors

Factor chi_0(t)=t^a q(t), q(0)!=0; a may be 0 or r. Put

    f(t)=chi_0(t)^p=t^(pa) q(t)^p.

By the polynomial Chinese remainder theorem there is a unique residue class
e(t) modulo f, represented in degree <pr, such that

    e=0 mod t^(pa), e=1 mod q(t)^p.

The conventions when a=0 or q=1 are e=1 and e=0 respectively. Set E=e(A).
Then

    E^2=E, AE=EA,
    A^(pa)(I-E)=0, q(A)^p E=0.

Thus R^r=ker(E) direct_sum im(E), A is nilpotent on ker(E), and A is
invertible on im(E). To see the last assertion construct z(t), degree <pr,
by CRT with z=0 mod t^(pa) and z=t^(-1) mod q^p, and set D=z(A). It satisfies

    AD=DA=E, DE=ED=D.

It follows that DAD=D and A^(pa+1)D=A^(pa); D is the Fitting/Drazin inverse.
Every equality follows from polynomial divisibility by f and Theorem 1.

The submodules are free of ranks a and r-a. A concrete proof and basis:
choose columns of E_0 spanning im(E_0) over F_p and columns of I-E_0 spanning
ker(E_0). Use the corresponding columns of E and I-E over R to form P,
with the kernel columns first. Its residue P_0 is invertible, so det(P) is a
unit in the local ring R and P is invertible. Its columns lie in the desired
summands. The equality EP=P diag(0_a,I_(r-a)) proves that P is the required
basis change. No expansion to an rp^b-dimensional F_p vector space is needed.

## Functoriality and ring-valued categorical chain splitting

Suppose a finite additive F_p-linear category contains objects X_j with
End(X_j)=R_(b_j,p), and Q is a degree-preserving chain endomorphism of a
complex, block-diagonal by degree and matching. Its block A_j acts on
X_j^(r_j); each differential entry T obeys A_j T=T A_i under actual category
composition. Compute the above E_i,D_i and E_j,D_j independently.

Then E_j T=T E_i, even if e_i(t) and e_j(t) differ. For N sufficiently large
to kill both nilpotent restrictions,

    (I-E_j) T E_i
      =(I-E_j) T A_i^N D_i^N
      =(I-E_j) A_j^N T D_i^N=0,

and, similarly,

    E_j T(I-E_i)
      =D_j^N A_j^N T(I-E_i)
      =D_j^N T A_i^N(I-E_i)=0.

Thus the nilpotent and invertible images form complementary subcomplexes.
The lifted bases above exhibit an actual chain isomorphism, provided every
inverse and every categorical cross term is evaluated and checked. This
extends the prior scalar Fitting procedure to supplied ring-valued chain
endomorphisms. It does not solve the search for useful such endomorphisms.

WARNING: the characteristic-polynomial theorem itself is not valid for an
arbitrary mixed-matching matrix with noncommutative cobordism coefficients.
It is applied only inside the same-matching endomorphism blocks; functoriality
across differently typed blocks uses the intertwining equations just proved.

## Decision and complexity scope

These theorems shorten local algebraic certificates and permit exact
ring-valued Fitting decompositions. They do not bound the number or size of
blocks constructed from an arbitrary knot, do not assert compressed matrix
products stay compressed, and do not establish a complete quasi-polynomial
unknot recognizer. The established 2^b coefficient-space barrier and arbitrary
scan multiplicities remain. A useful immediate experiment is to compare
residue-polynomial certificates against existing explicit inverses on blocks
actually extracted by the production scanner.

## References and priority notes

Standard ingredients: Cayley--Hamilton over commutative rings; Frobenius in
characteristic p; polynomial CRT; Fitting decomposition; projective modules
over local rings. Matrix-ring nil indices have older literature, including:

* Ofer Hadas, The index of nillity of the tensor product of a nil ring of
  bounded index by a matrix ring, Archiv der Mathematik (1993),
  DOI 10.1007/BF01198809.
* Ofer Hadas, Indices of nillity and absolute nillity of matrix rings,
  Communications in Algebra 25(5) (1997), 1485--1497,
  DOI 10.1080/00927879708825930.

The primary texts of these two papers have not been fully inspected here;
they are a priority-search lead, not a source for an asserted exact theorem.
Do not say the displayed bound is absent from the literature. State the
elementary proof and its specific application to the recognizer.
