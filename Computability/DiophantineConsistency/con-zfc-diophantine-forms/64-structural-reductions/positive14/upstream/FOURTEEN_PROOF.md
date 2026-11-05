# Fourteen positive unknowns at degree 56

This is an adapter of the ordinary-strong blank-K215 norm system at ProveIt
commit `124c07c0b77a9e20e84676514d8b1ff78536ea3f`. It deletes the positive
index quotient h without eliminating the root coordinates. The resulting
single equation has **14 positive unknowns, exact degree 56, and 79 binary
operations** (44 multiplications, 19 additions, and 16 subtractions).

The delivered instance uses the entire package-31 tuple, including its
already shifted MF, from `../coefficients/ports.json`. The proof is uniform
in complete authentic tuples with the same normalized compiler interface.
It is not a theorem about arbitrary substitutions for the four ports.

## 1. The polynomial

The supplied strictly positive coordinates are

    J,F,alpha,z,f,i,T,s,w,tau,eta,zeta,y,gamma.

Use the common polynomial abbreviations

    q=beta J+1, C=q-F-alpha, X=wq, Y=sq^3, E=XY,
    k=eta+zeta, c=kY+eta, a=E+Y, H=4a+3,
    Delta=a^2+H=(a+2)^2-1, b0=X+ac,
    R=((q-1)(q-F)+alpha)(q^2-1)+(MC+q MF)J,
    V=c(Tf-1)-Rf^2,
    N0=tau^2-(XY^2)(XY^2+1)k^2,
    Aaux=Delta(f^2-1), I=i c^2,
    Na=Aaux(V^2-y^2)+y^2,
    Nt=(K0+w)C+q-F-z(q-1),
    G=1+Delta c^2, U=4q^4, r=k-R-1,
    Dstar=U b0+H(U gamma-r).

The single equation is

    (Dstar^2-U^2 G)^2+(I^2-Aaux)^2+(Na-1)^2+(N0 Nt-1)^2=0.  (1)

The meaning of i is the **ordinary** strong coordinate. In particular the
strong equation is I^2=Delta(f^2-1), not the normalized equation
f^2-Delta I^2=1. No informal cancellation of Delta is allowed.
All abbreviations are computed polynomial expressions, and all powers have
fixed nonnegative integer exponents. The JSON gives all 79 paid gates.

## 2. The absorber and its early index bound

Put P0=2XY^2+1 and U=4q^4. The first Pell norm gives
k=2 psi_P0(n) for a positive index n. The recurrence gives

    k=2n modulo 2(P0-1)=4XY^2.

Since 4XY^2=4w s^2 q^7, this modulus is a multiple of U.
Furthermore gcd(U,H)<=3. Indeed H is odd and H=3 modulo q, so only
the prime 3 can divide both q and H. If 3 divides q, then 27 divides
Y, and H=3 modulo 27 has 3-adic valuation exactly one.
Therefore, on putting mu=U/gcd(U,H),

    mu>=4q^4/3.

Whenever U|H(k-R-1), we consequently have 2n=R+1 modulo mu.
If 0<R+1<mu, positivity of n already gives

    2n=R+1+j mu with j>=0, hence n>=(R+1)/2.       (2)

This lower bound is obtained **before** proving the main index p=R.
It is the point that makes the ordinary strong-rank theorem applicable.
If later n<R, then |2n-R-1|<R<mu forces j=0 and 2n=R+1.
Thereupon r=k-2n is divisible by both E and U.

## 3. Soundness: early roots and a large main index

At a zero of (1), all four squared residuals vanish. In particular
N0 Nt=1. The consecutive-product negative-Pell descent excludes
N0=-1, since XY^2>=2; hence N0=Nt=1. The authentic transport
interface gives

    q>=16, C>0, 3q<R<q^4-2, E>=q^4>R+2.

The first residual gives a rational square root g=Dstar/U of the
integer G, hence g is an integer. It is positive. Indeed H<5a and
b0>akY imply

    Dstar>U b0-Hk>ak(UY-5)>0.

Thus g^2-Delta c^2=1. Reducing Dstar=Ug modulo U gives
U|H(k-R-1), with no premature cancellation of H.

Let A=a+2. The main Pell norm and the first Pell norm give positive
indices p,n satisfying

    g=chi_A(p), c=psi_A(p),
    tau=chi_P0(n), k=2psi_P0(n).

Since P0>A and c>k, monotonicity gives p>n. By section 2,
mu>=4q^4/3>R+1 and n>=(R+1)/2. Since R>3q>=48, this gives
n>=25 and p>=26. In particular

    c>A Delta^2, c>2p, c>2R.                      (3)

For the first inequality one may use
psi_A(p)>=(2A-1)^(p-1)>=A^25>A^5>A(A^2-1)^2.
The bound c>2p follows from the same elementary recurrence growth.
The bound c>2R also follows from c>=psi_A(2)=2A and A>E>R.
Thus the large-c bootstrap does not assume the deleted index equation.

## 4. The ordinary strong-rank theorem and auxiliary index

We use the ordinary strong-rank lemma proved in
`../provenance/compiler_proofs/ORDINARY_BLANK_PROOF.md`, section 4:

    c=psi_A(p)>A Delta^2,
    (i c^2)^2=Delta(f^2-1)

imply, for a positive index m,

    f=chi_A(m), p|m, c|m, m>=c>2p,
    I=Delta psi_A(m), and c^2|(f^2-1).             (4)

Its proof is a rank argument in the integer-coordinate Pell group,
including the possible nonfundamentality of A relative to the squarefree
discriminant. It is stronger than rational-square recovery and is used
with its verified strict hypothesis (3). For orientation, if
A=chi_F0(e), Delta=(F0^2-1)psi_F0(e)^2, comparison of the gcd-index
ordinate with c/Delta and the bound c>A Delta^2 forces ep to divide
the index of f. Composition then gives I=Delta psi_A(m). The
congruence psi_A(p)=p A^(p-1) modulo Delta and quotient-sequence
reduction modulo c^2 yield c|m. This is the inherited lemma, not a
new assertion that Delta can be canceled from the supplied equation.

Put Q=I^2=Aaux. The auxiliary equation is

    QV^2-(Q-1)y^2=1.

It excludes V=0. Its Pell index j0 is odd because I divides the
abscissa. The odd-index abscissa polynomial, reduced modulo f,
uses Q=1-A^2 and V=-c modulo f to give
psi_A(j0)=+c or -c modulo f. The doubling identity and signed
abscissa reduction, valid because 0<2p<m, give
j0=+p or -p modulo m, hence modulo c by (4).
On the other hand Q=0 modulo c, f^2=1 modulo c by (4), and
V=-R modulo c give j0=+R or -R modulo c. Consequently
R=+p or -p modulo c. Bounds (3) give

    p=R.

This is precisely the ordinary signed auxiliary proof in source 31,
section 5, with the necessary large-c hypotheses established above.

Now n<p=R, and the last part of section 2 forces 2n=R+1. Set

    h=(k-R-1)/E, gamma_old=gamma-(k-R-1)/U.

Both are integers. The first is positive because n>=25 and
psi_P0(n)>n. For the second the carrier gives
gamma_old=(g-b0)/H. Since n>=2, k>=4P0>X and c>k>X;
also Delta>(a+1)^2 gives g>(a+1)c. Hence
g-b0>c-X>0 and gamma_old is positive.

All fifteen coordinates of the original **ordinary-strong** blank
compiler are now restored, with N0=N1=Na=Nk=Nt=1 and
I^2=Delta(f^2-1). Its inherited two-sided compiler theorem supplies
the finite blank K215 computation and hence a syntactic ZFC refutation.

## 5. Constructive converse

Conversely, a positive ordinary-strong compiler witness has p=R=2n-1
by the established ordinary index theorem. Thus
r=k-2n is a positive multiple of 4XY^2, hence of U. Define

    gamma=gamma_old+r/U.

It is a positive integer. Keep the other thirteen coordinates unchanged.
Then Dstar=U(b0+H gamma_old)=Ug, and all four residuals of (1)
vanish. In particular no new restriction on s or increase of an index
is required. Canonical normalized compiler witnesses also give ordinary
witnesses by the established change i_ordinary=Delta i_normalized.

This proves equivalent existence of positive solutions. Composing with
the inherited ordinary compiler and K215/refutation calibration and
negating existential solvability gives the Con(ZFC) equivalence in
ordinary mathematics formalizable in ZFC. No new end-to-end Lean/Rocq
certificate or object-language ZFC derivation is asserted.

## 6. Exact degree and audit

The four residual degrees, in the displayed order, are 26,22,28,24.
For the first, use the exact identity

    Dstar^2-U^2G
      =U^2[(b0+H gamma)^2-G]
       -2UH r(b0+H gamma)+H^2r^2.

The three terms have degrees 26, at most 25, and at most 20.
The bracket is the original main residual of exact degree 18.
Only (Na-1)^2 reaches degree 56. The highest homogeneous form is

    T^4 f^8 w^4 s^8 (eta+zeta)^4 (beta J)^28.

The J^28 eta^4 T^4 f^8 w^4 s^8 coefficient is beta^28, nonzero
on every authentic tuple. The independent standard-library checker
expands the entire main residual exactly (2,994 monomials with the
four coefficient ports symbolic), proves its degree 26, and propagates
valid bounds and highest homogeneous forms for the remaining circuit.
It checks all 79 gates, all 14 witnesses, all four ports, complete
liveness, and the nonzero final form. It is a finite circuit certificate;
the preceding unbounded number-theoretic proof is a separate assertion.

## 7. Comparison and contribution

The inherited wave-2 Q56 has 15 positive variables, degree56, and74
operations. The present equation has14 positive variables, the same
degree56, and79 operations. Thus one fewer coordinate costs five
operations. The active normalized 15-variable75-operation degree68
equation is a further local comparator, not the best historical degree.
The quotient absorber has not improved the 67-operation absolute
operation count. Lower-variable equations elsewhere have much larger
degrees. These are distinct tradeoffs, with no global minimality claim.

The new contributions are U=4q^4 absorption with a negative carrier
shift, its **early** lower bound on n, and the resulting ordinary-strong
fourteen-coordinate degree-56 circuit.
