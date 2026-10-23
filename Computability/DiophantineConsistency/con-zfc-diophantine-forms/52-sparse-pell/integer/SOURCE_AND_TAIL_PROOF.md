# Sparse-support ten-integer source and factored finalizer

## Fixed statement and dependencies

The three recommended Pareto variants are
`generated/sun10_interior_regular_homogeneous.json`,
`generated/sun10_interior_packed_shifted_homogeneous.json`, and
`generated/sun10_interior_packed_global.json`. Each has the ten unrestricted integer
unknowns f,g,h,k,l,w,x,y,z,m. Every named expression below is an abbreviation,
not an additional unknown. All powers are fixed nonnegative integer powers.
The circuit is division-free and uses only binary addition, subtraction and
multiplication. Its coefficient leaves are materialized and hashed in
`FIXED_BINDING.json`; the complete native tuple is the coherent tuple in
`../coefficients/COEFFICIENT_BINDING.json`.

The reduction of this tuple's positive quadratic parent to a finite ZFC
refutation is inherited. The parent has 31 strictly positive variables and
22 quadratic residuals. Substitute every variable by n_i+1. A simultaneous
natural zero exists if and only if the original parent has a positive zero.
The fifth residual has value 1 at the zero vector, so a simultaneous zero
cannot be the zero vector.

The finalizer uses Sections 4--8 of package31's SIGNED10_PROOF, whose
mathematical dependencies include Sun 2021 (arXiv:1704.03504v7) and Sun 2026
(arXiv:2609.01594v2). The general ten-integer reduction is Sun's result, not
claimed here. The sparse source below proves its required interface anew.
No end-to-end Lean/Rocq certification is asserted. Finite checks certify the
literal data and identities; the universal claims use the mathematical proof.

## 1. Certified sparse source

Write the shifted residuals r_j(n)=sum p_(j,alpha)n^alpha and set
c_(j,alpha)=(2-|alpha|)! product_i(alpha_i!) p_(j,alpha).
There are 136 nonzero symbolic coefficient records, with all fixed ports
specialized to the one active complete tuple. For the active certificate,
write p for its padding position, w_i for its 31 distinct nonnegative
variable digit positions (none equal to p), W=max(p,w_i), H_j for its target
positions, and e(alpha)=(2-|alpha|)p+sum alpha_i w_i. The final primary
certificates have p=81 and W=174. Set

D(T)=sum_(j,alpha) c_(j,alpha) T^(H_j-e(alpha)),
Z(T)=sum_j T^H_j,   ell(T)=sum_i T^w_i,
Dmax=max_(j,alpha)(H_j-e(alpha)),   K=Dmax+2W.

The independent sparse-support certificate proves every exponent is
nonnegative and, for all source records (j,alpha), all quadratic exponent
vectors gamma and all target indices k,

  H_j-e(alpha)+e(gamma)=H_k  iff  j=k and gamma=alpha.

This is only support-local isolation: pair sums for monomials having zero
source coefficient may collide. No full Sidon property is used or claimed.
The identity follows immediately:

[T^H_j] (T^p+sum n_i T^w_i)^2 D(T) = 2 r_j(n).

The coefficients of the square are the degree-two multinomial coefficients;
the displayed factorial weight cancels their denominators. In particular,
all 22 residuals can be tested by separate selected digits of one integer.
The certificate's leading coefficient is 2. In the primary interior variants,
Dmax=Hmax-162. These facts are
independently checked, rather than inferred from a numerical degree test.

## 2. Actual coefficient bound and source equations

Let C=1+sum_(j,alpha)|c_(j,alpha)|, an explicit positive integer computed from
the actual fixed coefficients, not from a consistency-dependent choice.
The independent arithmetic audit gives bit_length(C)=1,182,954 and verifies

 beta_source=2^1182966 > 2048 C.

The exponent is even, hence beta_source is 1 modulo 3. This is stronger than
merely bounding each coefficient independently. Materialized leaves and
fixed-port hashes are checked independently of the builder.

Define, in the two source unknowns f,g,

 b=1+3f,   B=beta_source b^2,   cap=b B^W,
 N0=B^(W+1),   N1=4 B^(K+1),   N=N0 N1,
 mask=N0-1-(b-1)ell(B),
 Tcode=mask+N0(B-2)Z(B),
 Jcode=2(B^p+g)^2 D(B)+B sum_(i=0)^K B^i,
 Scode=g+N0 Jcode,
 Rcode=(Scode+Tcode+1)N+Tcode+1,
 X=(N-1)Rcode,   Y=N^2.

All formulas are literal integer polynomials. The source gives these three
properties required by the inherited bridge:

(i) From a natural source zero, f may be chosen arbitrarily large, b a square
    and a power of two, b<=g<cap, with Y dividing binomial(2X,X).
(ii) Conversely f!=0, b a square and a power of two, 0<=g<2cap, and that
     divisibility imply a natural source zero.
(iii) Before assuming b is a power of two, f!=0, b a square and 0<=g<2cap
      imply X>3b and Y>max(b,256). Moreover 3 divides X.

### Size proof

Under the hypotheses of (iii), b=1+3f is a nonzero square. A nonzero f
therefore gives b>=4 and f>0. Thus B>2048 C b^2>4b. Since
|D(B)|<C B^Dmax and B^p+g<=3bB^W,

 |2(B^p+g)^2 D(B)| < 18 C b^2 B^K < B^(K+1).

The baseline B sum_(i=0)^K B^i lies between B^(K+1) and 2 B^(K+1).
Consequently 0<Jcode<3 B^(K+1)<N1. Also g<N0. The mask's digits are B-b
at w_i and B-1 elsewhere, so 0<=mask<N0. Distinct targets are at most K,
and (B-2)sum_j B^H_j < B^(K+1)<N1. Therefore 0<=Scode,Tcode<N.
It follows Rcode>=N+1, X>=N^2-1>3b, and Y=N^2>max(b,256).
Finally b and B are 1 modulo 3, N=4B^(W+K+2) is 1 modulo 3, and thus
3 divides X. The cap has exactly the required positive monomial form
2^(1182966 W) b^(2W+1).

### Carry proof

Now additionally let b be a power of two. Then B,N0,N1,N are powers of two.
Sun 2021 Lemma2.2 identifies Y|binomial(2X,X) with the absence of binary
carries in Scode+Tcode. The two block bounds above split this into no carries
in g+mask and in Jcode+(B-2)Z(B). The first condition, by the digit-mask
lemma (Sun 2021 Lemma2.4), is equivalent to

 g=sum_i n_i B^w_i, with 0<=n_i<b.

Set A(T)=(T^p+sum n_i T^w_i)^2 D(T). Its degree is at most K. Every
coefficient A_t satisfies

 |A_t| <= C(1+sum_i n_i)^2 < C(32b)^2 < B/2.

Thus the integer A(B)+(B/2)sum_(i=0)^K B^i has actual base-B digits
B/2+A_t, strictly between 0 and B, with no carrying between digits.
Multiplying both summands by two preserves the binary no-carry property.
At each selected target, the other summand has digit B/2-1, whose lower
log2(B)-1 bits are all 1. Its sum with a digit strictly between 0 and B
is carry-free exactly when that digit is B/2. By the isolation identity,
this is precisely r_j(n)=0 for every j. This proves (ii).

For (i), take a nonzero simultaneous natural zero n. Choose b=4^q larger
than all its entries and as large as desired, put f=(b-1)/3, and form the
encoded g. For interior padding the unique zero-weight variable is i, while the fifth
residual has constant term 1 and depends only on E,a,X, all with positive
positions. At least one positive-position coordinate of a zero is therefore
nonzero, giving g>=B>=b. In the older padding-zero comparison all variable
positions were positive and the zero vector was excluded.
Also g< bB^W=cap by the distinct-position expansion. The carry computation
then gives the desired divisibility. This proves the full source contract.

## 3. The inherited exact tail and its algebraic factoring

Use the formulas of package31 SIGNED10_PROOF Sections4--8, with the source
b,X,Y,cap above. In particular use its three radicands

 r0=b[1+(3O-4)b^2z^2],
 r1=(Pn^2-4)K1^2+4,
 r2=D F I,

its separating weights 1,r0,r0(Pn^2+K1^2+3), its intersective quintic
(v^3-v-1)(v^2+23), Sigma=zx S^5 and the homogeneous Theta, and its
collected three-radical norm. These expressions are defined completely
in the literal circuit and the standalone section file.

The new evaluator changes no tail polynomial. Let a=A/2, constructed
without division as a=(lYX)(V+1). The following exact identities shorten it:

 G*=(a-1)(F-1)-1,
 H*=C+F(B1-C+16Ey),
 t^3-tS^2-S^3=t(t^2-S^2)-S^3,
 f^2l^2=(fl)^2,
 b^2z^2=(bz)^2.

For the last scaled radicand, share sigma^2 r0^2 with the second radicand,
then multiply by (Pn^2+K1^2+3)^2 r2. Exact polynomial expansions in the
independent verifier check the nontrivial identities. These factoring
changes do not alter any positive/negative-branch argument, residue-class
freedom, divisibility hypothesis, root-separation hypothesis or domain.

With a_i=Sigma^2 weight_i^2 r_i and Z=Sigma m-Theta, define

 Vnorm=Z^2+a2-a0-a1,
 Wnorm=Vnorm^2+4 Z^2 a2-4 a0 a1,
 F10=Wnorm^2-16 Vnorm^2 Z^2 a2.

The independent symbolic verifier proves that this is exactly the product
of the eight signed linear factors over formal square roots. Package31's
proof shows F10=0 if and only if the source has a natural zero. Its Sigma=0
case is excluded because the norm becomes Theta^8 and the intersective
quintic has no rational root. Its separating weights handle negative as
well as nonnegative candidate radicands. There is no new assertion of an
unweighted three-radical theorem here.

## 3a. Full tail registers (no hidden variables)

For clarity the complete inherited tail is recorded here, rather than
requiring retrieval of another source:

 L=lY; U=2LX; V=4gwY; W1=bw;
 A=U(V+1); B1=2X+1; C1=B1+(A-2)h;
 Pn=U^2V; K1=X+1+k(Pn-2); S=2A-5;
 T=3W1 C1-2(W1^2-1);
 r1=(Pn^2-4)K1^2+4;
 Delta=8 cap^3 g K1^2-g^2[32(C1-K1 L)^2 cap^3+g^2 K1^2];
 O=f^2 l^2 Delta; xi=zx;
 D=(A^2-4)C1^2+4; E=C1^2 D xi;
 F=4(A^2-4)E^2+1;
 G=2(A+2)(A-2)^2 E^2-1;
 H=C1+(B1-C1)F+16 E F y;
 I=(G^2-1)H^2+1;
 r0=b[1+(3O-4)b^2 z^2]; r2=D F I;
 Sigma=xi S^5; t=T+S y;
 Theta=(t^3-t S^2-S^3)(t^2+23 S^2).

Use these in the weights, scaled radicands and final norm of Section3.
The code names C and K for C1 and K1, and names T and S for their small
bridge versions. They must not be confused with coefficient bound C,
source range K, or source Tcode and Scode.

## 3b. Shared-parent homogeneous evaluation

For a shifted residual q(n), let Q(u0,u1,...,u31)=u0^2 q(u1/u0,...,u31/u0)
be its formal degree-two homogenization, an integer polynomial. The weighted
quadratic form is Q+diag(Q), where diag means the sum of its pure-square
monomials: the factorial weighting doubles pure squares and leaves all
cross monomials unchanged.

Evaluate Q for all22 residuals by homogenizing the shared60-gate parent at
positive-source inputs u_i+u0. For an addition/subtraction of differing
homogeneous degrees, multiply the lower-degree operand by the required
fixed power of u0 before the operation. Constants are degree zero. Lift
each final residual to degree two. Then add only the constant/pure-variable
square diagonal correction. At u0=B^(W-p), ui=B^(W-wi), multiply row j by
B^(Hj-2W), which is polynomial whenever all Hj>=2W. The regular primary
certificate already satisfies this. Uniformly increasing all interior-
packed targets by186 establishes it for the middle variant, preserving
all extraction equalities and shifting Dmax and Kcode by the same amount.

The independent verifier expands the resulting Dcode as a sparse exact
polynomial in B and FOUR SYMBOLIC NATIVE PORTS, not just at numeric samples.
It matches all159 expanded port-monomial terms with the literal136-record
specification, and independently checks the target sum. Thus the
homogeneous evaluator's equality is certified exactly and remains uniform
in the coherent native coefficient tuple. Literal modular replay tests the
rest of each source and tail as a separate transcription check.

## 4. Complexity and logical endpoint

The primary interior-regular shared-homogeneous evaluator gives 582 live
binary operations and exact total degree 50,822,936. The shifted interior-
packed homogeneous evaluator gives 637 operations and degree 34,378,296.
The unshifted interior-packed global-Horner evaluator gives 689 operations
and degree 33,202,776. The 186-position uniform shift used for the middle
variant is a degree/operation tradeoff, not an identity of final polynomials. Degree is proved by circuit propagation for an
upper bound and a nonzero top diagonal coefficient modulo a prime for an
exact matching lower bound. Three primes are retained as redundant checks.
A live node traversal excludes dead registers from operation counts.
Constants and register reuse are free; constant construction is separately
specified by finite recipes and actual bytes. No variable exponent is used.

Composing the proven source contract with the inherited finalizer and the
coherent native compiler endpoint gives, without assuming consistency,

 ZFC proves: exists ten integers with F10=0 iff not Con(ZFC).

Classical negation gives the requested equivalence between the absence of
integer solutions and Con(ZFC). This does not prove either side of that
equivalence and does not assert globally minimal variables, degree or size.
