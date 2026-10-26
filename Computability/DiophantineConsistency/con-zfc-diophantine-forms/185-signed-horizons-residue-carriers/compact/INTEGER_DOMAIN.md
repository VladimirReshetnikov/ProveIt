# A 36-integer-variable equation of exact degree 288

The principal unrestricted-integer equation here is
`integer_equations/integer36_degree288.json`. It has 36 independently
quantified integer variables, 145 live binary arithmetic operations, and
exact total degree 288. Its coefficients are the same coherent four-number
Start-only4127 tuple as the positive fourteen-variable parent.

## 1. Three coordinates require no positivity encoding

For soundness of PROOF.md, only

    J,F,alpha,z,i,T,s,w,eta,zeta,gamma

must be strictly positive. The other three coordinates f,n,tau may be
arbitrary integers:

* The polynomial contains f only through f^2. After the unit-sign argument,
  the normalized strong equation is f^2-Delta*I^2=1 with I>0. Thus f is
  nonzero, and replacing it by |f| makes every original proof step valid.
* The polynomial contains tau only through tau^2. The first norm is
  tau^2-v(v+1)k^2=1, so tau is nonzero and may similarly be replaced by |tau|.
* The coordinate n appears only in the signed carrier u=k-Mn-R. No soundness
  step in Sections 2--4 uses n>0: outer bounds use Nt, index recovery uses
  |u|, and the residue u=k-R modulo M holds for every integer n. Thus the
  same soundness proof applies to negative n and n=0 without modification.

Completeness already constructs all three positively. Therefore existence
on this enlarged domain is still equivalent to a finite syntactic ZFC
refutation. This statement is not obtained by silently forgetting domains;
it follows from the displayed sign audit.

## 2. The explicit unrestricted polynomial

For each of the eleven coordinates x in the first list, introduce three
independent unrestricted integers x_a,x_b,x_c and substitute

    x = 1+x_a^2+x_b^2+x_c(x_c+1).

Leave f,n,tau unchanged. Substitute these eleven polynomials into
P_q_direct from PROOF.md. The result is the literal polynomial P36 in the
supplied graph. Its variable count is 11*3+3=36. No inequalities, variable
exponents, implicit predicates, or additional quantified registers remain.

For every integer triple the substituted expression is positive, because
c(c+1)>=0. Conversely it represents every positive integer. Indeed for
N>=0, 4N+1 is never of the form 4^a(8b+7). Legendre's three-square theorem
gives 4N+1=u^2+v^2+w^2. Exactly one of u,v,w is odd modulo 2; after
permuting, write u=2a, v=2b, w=2c+1. Then
N=a^2+b^2+c(c+1). This is also an explicit corollary in Anna Danilkin and
Loic Chevalier, *Three Squares Theorem*, Archive of Formal Proofs, 3 May 2023,
https://isa-afp.org/entries/Three_Squares.html .

Thus the substitution has exactly the required positive-coordinate range.
ZFC proves that P36 has an integer zero iff P_q_direct has a zero on its
enlarged domain, iff a finite syntactic ZFC refutation exists. Negation gives

    ZFC proves: (no integer zero of P36) iff Con(ZFC).

The cited Isabelle result is an independently available formalization of
the classical representation theorem. This package does not import it as
a new end-to-end formal verification of the consistency equation.

## 3. Operation count and exact degree

Each substitution uses seven binary operations: two squares, c+1,
c(c+1), and three additions. Eleven substitutions add 77 gates to the
68-gate positive graph, for exactly 145. All 36 variables and all gates
are live.

For an upper degree bound give the eleven substituted parent coordinates
weight 2, the free coordinates f,n,tau weight 1, and all fixed coefficients
weight 0. The five factor degrees of P_q_direct are then

    N0:44, N1:36, Na:128, Nt:4, Ns:76.

Their sum is 288. The cancellation of N1 is the same exact identity as in
the positive graph. The squared carrier contributes only degree 118 to the
auxiliary norm, strictly below its V^2 contribution of degree 128; no hidden
term overtakes the claimed leader when n remains unrestricted.

Write sigma_x=x_a^2+x_b^2+x_c^2. The full top homogeneous component is
obtained from

    8*(beta J)^87*gamma*i^4*(eta+zeta)^13*w^10*s^23*T^2*f^4
      *[w*(beta J-F-alpha)-z*beta J]

by replacing each of those eleven positive coordinates x by sigma_x and
leaving f unchanged. It is nonzero: set every x_b=x_c=0, and take the
-z*beta J term and eta^13 term. One attained monomial coefficient is
-8*beta^88, at

    J_a^176 * gamma_a^2 * i_a^8 * eta_a^26 * w_a^20
      * s_a^46 * T_a^4 * f^4 * z_a^2.

The exponents sum to 288. Thus the exact degree follows at the actual
beta>0 without expanding the entire large polynomial. The factorized top
form and the injective square specialization avoid any numerical degree
inference.
