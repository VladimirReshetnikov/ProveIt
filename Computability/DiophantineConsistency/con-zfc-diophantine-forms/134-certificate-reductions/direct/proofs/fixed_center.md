# Deterministic comparison centers in a signed Pell index certificate

This note is an ordinary mathematical proof for the current direct C222
compiler. It is independent of finite experimental checks. Its only imported
Pell fact beyond elementary recurrences is the same abscissa-residue
classification already used in the accepted signed index certificate.

## 1. A polynomial replaces the auxiliary Chinese-remainder choice

Let A be an odd integer with A >= 3. Suppose C >= 2 and

    U^2 - (A^2-1) C^2 = 1,
    H^2 - (A^2-1) J^2 = 1,
    C^2 divides J,   J != 0.

All variables other than A,C are allowed to be signed. Define

    D = A + (1-A) H^2.

The auxiliary norm gives the second exact identity

    D = 1 - (A-1)(A^2-1) J^2.                 (1)

Consequently:

* D == A (mod H), directly from the defining polynomial;
* D == 1 (mod 4C), because 4 divides (A-1)(A^2-1), and C divides J^2;
* D <= -15, since A >= 3 and |J| >= 1. In particular |D| > 1.

In fact the divisibility coefficient is a multiple of 16 for odd A, but
the weaker factor 4 is all that is used. Neither a free comparison-center
parameter nor its two CRT quotient witnesses is needed. The fact that D is
negative is allowed by the signed comparison certificate.

## 2. Complete signed index theorem with this center

Fix an intended positive index h with 1 <= h <= C. In addition to the
three hypotheses above, impose

    S^2 - (D^2-1) Q^2 = 1,
    S == U (mod H),
    Q == h (mod 4C).                         (2)

Then C = Y_h(A), and U is either sign of X_h(A).

Proof. Classification of the first two norms gives positive indices i,l
such that

    |U| = X_i(A),  C = Y_i(A),
    |H| = X_l(A),  |J| = Y_l(A).

They are positive because C >= 2 and J != 0. Since C^2 divides J,
monotonicity gives i <= l. Squared-ordinate divisibility gives C divides l.
The latter fact has the elementary proof used by the source certificate:
Y_i divides Y_l implies i divides l; writing l = i k, expansion of the Pell
unit power modulo Y_i^2 gives

    Y_l / Y_i == k X_i^(k-1) (mod Y_i).

The norm gives gcd(X_i,Y_i)=1, so Y_i^2 divides Y_l forces Y_i divides k,
and hence Y_i divides l.

Classify the comparison norm at |D|. There is j >= 0, and independent
coordinate signs, such that S and Q are signed X_j(|D|),Y_j(|D|).
The signed-base identities

    X_j(-a)=(-1)^j X_j(a),
    Y_j(-a)=(-1)^(j-1) Y_j(a)   (j >= 1)

absorb the negative D into those independent signs. Polynomial dependence
on the base, D == A (mod H), and S == U (mod H) therefore imply

    X_j(A) == +/- X_i(A) (mod X_l(A)).

The retained abscissa-residue classification and its half-period sign
identity imply j == +/- i (mod 2l). This includes i=l.

On the other hand, D == 1 (mod 4C) implies Y_j(D) == j (mod 4C).
Thus the last congruence in (2) gives j == +/- h (mod 4C).
Because C divides l, we obtain i == +/- h (mod 2C).

Now 1 <= i <= C, since Y_i(A) >= i, and 1 <= h <= C. If i-h is
divisible by 2C it is zero. If i+h is divisible by 2C, then i+h=2C,
so i=h=C. Either way i=h. This proves the claim. The j=0 case is
automatically excluded by 0<h<=C<4C.

The theorem does not use a sign of U,H,J,S,Q or a bound on the magnitude
of D. All actual uses of D are (1), |D|>1, and its two congruences.

## 3. Completeness, including an odd auxiliary quotient

Let A >= 3 be odd and let h >= 2 be arbitrary. Take

    U = X_h(A),   C = Y_h(A),
    l = h C,     H = X_l(A),   J = Y_l(A).

Then C^2 divides J. The argument is the same unit-power expansion in
Section 2 with k=C.

Furthermore J/C^2 is odd. Indeed, for odd A, every X_n(A) is odd,
Y_n(A) is odd exactly when n is odd, and

    Y_(2n)(A) = 2 X_n(A) Y_n(A).

It follows by writing n=2^e q with q odd that v_2(Y_n(A))=v_2(n).
Hence v_2(C)=v_2(h) and

    v_2(J)=v_2(hC)=2v_2(C).

Thus J=C^2(2e+1) for the natural integer e=(J/C^2-1)/2. The compiler
may quantify e over unrestricted integers because an odd multiplier is
automatically nonzero; its sign is immaterial for the soundness theorem.

Define D by Section 1, and use the signed-base Pell polynomials

    S = X_h(D),   Q = Y_h(D).

They are integers and satisfy the comparison norm. Polynomial base
transfer gives S == X_h(A)=U (mod H), while D == 1 (mod 4C) gives
Q == h (mod 4C). Thus the comparison quotient witnesses exist as integers.
Every retained public/semantic coordinate is unchanged. No application of
CRT, no adjustable comparison base, and no unknown growth bound is needed
to choose this comparison center.

## 4. Exact quadratic realization

Introduce a single square wire T=H^2 and retain a coordinate D with

    T-H^2=0,
    D-A-(1-A)T=0.

Both residuals have degree at most two. They replace the former comparison
center presentation D=1+4J(2d+1), D=A+Hf, including its private multiplier
coordinates d,f and the product wires that existed solely for those rows.
The comparison norm and the two remaining congruence rows are unchanged.
Actual variable and row savings depend on the whole subsequent exact
projection; they must be measured rather than inferred by subtraction.

## 5. Domain boundary

The negative deterministic center is suitable for unrestricted signed
comparison coordinates. It is not a direct replacement in a compiler
whose comparison coordinates and progression quotients are all natural.
The oddness of A is used to obtain the 4C congruence without changing the
auxiliary multiplier. For a general positive A>=2 an alternative valid
version is to require J=2C^2 e with a nonzero e; then 4C divides J^2 and
the same proof applies.

Novelty is claimed only relative to the inspected ProveIt sources: the
reviewed signed-cap implementations used an independently chosen CRT center.
No literature-wide priority claim is made.

## 6. Signed main bases and signed cap ordinates

The soundness theorem extends verbatim to odd A with |A|>=3 and nonzero
signed C, provided 1<=h<=|C| and |C|>=2. Use |A| in the classification
of the first two norms. Their coordinate signs and the identities for
negative bases absorb every difference between A and |A| in the residue
argument. The two required congruences are still

    D == A (mod H),   D == 1 (mod 4C).

Equation (1) gives D<-1 when A>=3 and D>1 when A<=-3, so the comparison
norm remains nondegenerate. Divisibility by signed C means the same
thing as divisibility by |C|. The short interval argument becomes
1<=i,h<=|C| and is otherwise identical.

For completeness it is enough to construct the positive-A witnesses
already described, if the surrounding existential compiler permits
them. If a signed-A completion is desired, take U=X_h(A), C=Y_h(A),
and l=h|C|. Choose H=X_l(A), J=Y_l(A); then C^2 divides J, and the
quotient is odd because v_2(|Y_n(A)|)=v_2(n). All norm and congruence
identities are polynomial in A. Here e=(J/C^2-1)/2 is an unrestricted
integer. It need not be even or nonnegative; only 2e+1 must be odd.
