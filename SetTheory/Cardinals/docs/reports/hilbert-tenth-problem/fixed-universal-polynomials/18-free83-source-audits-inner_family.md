# Independent audit: free-coefficient83 inner family

## Verdict

PASS for the auxiliary-completion theorem, the infinite intended inner family, ordinary-input loading, and the residual outer-interface equivalence in the reviewed scope. These are partial soundness research. They are **not** a genuine-compiler language counterexample, a full positive rejected-input zero, or a proof of language soundness.

The current author proof repairs two wording/scope issues identified during review: the growth estimate begins at recurrence index r>=1; the Section4 iff concerns realizing the prescribed R and intended transport factor Nt=1, not arbitrary product zeros. Neither repair changes the construction.

The independent checks read all83 saved source rows as data and compare every row with its expected mathematical register path. Neither upstream Python nor a saved arithmetic schedule was executed. The author checker was read before creating independent checkers. Author files were not modified. Mock-port checks are expressly only algebraic rewriting tests.

## Independently verified result

For every integer j>=0, set u=11^(12j+1), p=247u, n=208u, R=416u-1, X=2^p, Y=2^(57u-1), E=XY, A=Y(X+1)+2, Delta=A^2-1. There are positive integer witnesses for the actual first/main/index/auxiliary/strong factors, taking their intended values 1,1,1,1,Delta, with main rank p different from R, and with the exact main projection. For any odd input rank I>=3 with I<p, the input norm and shared rho/sigma projection also have positive witnesses with W=2^I. This is a theorem about the indicated factors and ports, not about completing the genuine outer source.

More generally, for A>=2 and odd p>=3, c=psi_A(p), D=chi_A(p), any R>0 with gcd(c,p)|R has a positive auxiliary/strong completion using f=chi_A(2p), S=Delta*psi_A(2p). The forced inverse S/(Delta*c^2)=2D/c is nonintegral. The divisibility condition is necessary and sufficient for this particular CRT pair; the audit does not assert it is necessary for every conceivable auxiliary completion.

## Auxiliary theorem

1. c is odd for odd p, because psi modulo2 alternates0,1. Therefore gcd(c,8p)=gcd(c,p). Choosing j0=1 for p=3 mod4 and j0=3 for p=1 mod4 makes j0*p=3 mod4. CRT for z=j0*p mod8p and z=R modc is compatible exactly when gcd(c,p)|R.
2. With f=chi_A(2p), b=psi_A(2p)=2Dc, S=Delta*b, the Pell identity gives Delta*f^2-S^2=Delta, c|S, f^2=1 modc, and gcd(c,f)=1.
3. Write z=2v+1, so v is odd. The quotient polynomial Q_v(t)=chi_s(2v+1)/s at t=s^2 obeys Q_0=1, Q_1=4t-3, Q_(v+1)=(4t-2)Q_v-Q_(v-1). Its initial values and recurrence prove Q_v(0)=(-1)^v(2v+1). Substituting t=1-A^2 and multiplying by(-1)^v gives the same odd-index recurrence and initial values as psi_A(2v+1); this proves the second required polynomial identity, without an invertibility assumption on S.
4. Pell doubling modulo f gives the pair at4p equal to(-1,0) and at8p equal to(1,0). The unit A+sqrt(Delta) has norm1 even in a possibly nonsplit or nonfield quadratic quotient, so this coefficientwise periodicity is valid. Triplication gives psi_A(3p)=(2f+1)c. Thus V=chi_S(z)/S satisfies V=-R modc and V=-c modf.
5. The positive numerator V+c+Rf^2 is divisible by the coprime integers c,f, proving T integral and positive. The literal argument is V=c(Tf-1)-Rf^2. The Pell norm at S gives the literal Na=S^2(V^2-y^2)+y^2=1 with y>0. No existential division is added to the circuit.
6. gcd(c,D)=1 follows from D^2-Delta*c^2=1, and c>1 is odd. Therefore c does not divide2D.

The independent checker uses chi_S(z) modulo S*c*f followed by exact division by S to obtain V modulo c*f. This is a different calculation from the author's Q recurrence. All five author fixture indices and bit lengths agree, including fully materialized auxiliary tuples with153073-bit V. Another288 modular completion cases pass. As a limit on overclaim, A=2,p=3 gives c=15: R=1 makes z=3 mod24 and z=1 mod15 inconsistent modulo3. This only refutes removal of the hypothesis from this CRT recipe, not all other possible completions.

## Resonance, inequalities, projection, and input

Let v=57u-1, L0=2XY, M0=4XY^2. The exact exponent equation is

(p-1)(1+p+v)=1+v+(n-1)(2+p+2v),

equivalently p(p-n)=(v+1)(2n-p). Here p-n=39u, 2n-p=169u, and247*39=57*169=9633. It proves L0^(p-1)=2Y*M0^(n-1).

For r>=3, (2A-1)^(r-1)<=psi_A(r)<(2A)^(r-1). The lower perturbation1+1/X+3/(2XY) strictly exceeds1+1/(2XY^2), and p>n, so c>kY. For epsilon=1/X+2/(XY)<2/X, one has (p-1)epsilon<1/2. The geometric bound gives c/k-Y<4pY/X=494u*2^(-190u)<1. For example u<=2^(u-1) reduces the last claim to494<2^(189u+1), true already at u=1. Thus eta=c-kY and zeta=k-eta are strictly positive.

P=2XY^2+1=1 modE, so psi_P(n)=n modE and k=2n modE. Since n>=2 and P>1, psi_P(n)>n; hence h=(k-2n)/E is a positive integer and k-hE-R=1 because2n=R+1.

For z_r=chi_A(r)-(A-2)psi_A(r), z_0=1,z_1=2 and z_(r+1)=2A*z_r-z_(r-1). The comparison sequence2^r satisfies that recurrence modulo H=4A-5 since its discrepancy is2^(r-1)H. For r>=1, monotone positive z_r gives z_(r+1)>(2A-1)z_r, so gamma=(z_p-X)/H is positive integral.

For odd I, psi_A(I)=I modDelta because A^2=1 modDelta. For I>=3, psi_A(I)>I, yielding positive delta. The same projection congruence gives positive rho=(z_I-2^I)/H. If p>I, then z_I<=z_(p-1), and z_p-z_I>=(z_p-z_(p-1))>(2A-2)z_(p-1)>2^p; therefore sigma=(z_p-z_I-X+2^I)/H>0. This proves the shared main/input projection rather than merely two unrelated Pell equations.

## Universal coprimality

The only prime divisors of p are11,13,19. L=lcm(12,18,13*(13^2-1),19*(19^2-1))=622440 and11^12=1 modL, so u=11 modL. The12 and18 periods fix the binary powers and hence A modulo13 and19. A determinant-one Pell companion matrix over F_l has order dividing |SL2(F_l)|=l(l^2-1), so the fixed rank residue gives respectively(A,c)=(4,1) mod13 and(11,18) mod19.

Modulo11, u=1 mod10, A=8 and Delta=8. Frobenius gives psi_A(11r)=Delta^5*psi_A(r)=-psi_A(r) mod11. Since psi_8(247)=10 and12j+1 is odd, c=1 mod11. None of11,13,19 divides c, proving gcd(c,p)=1 for every j. No testing of finitely many j is substituted for this argument. The independent modular checker corroborates32 values j=0..31 and verifies Frobenius at every residue A mod11 for24 small ranks, including Delta=0.

## Exact genuine outer interface and its unresolved condition

Fix an actual genuine compiler, keeping its six numerals B-1,K,ell,b,MC,MF_source unchanged, and fix positive input x. Let I=ell*x+b, W=2^I. For a family parameter j and integer N>=1 set t=dN, q=2^t=B^N, require3t<=57u-1 and p>I, and take J=(q-1)/(B-1), Q=q^2-1, M=(MC+q*MF_source)J, e=p modt.

The intended completion exists if and only if:

- Q divides R-M
- With G=(R-M)/Q, the least residue Z=(-G) modq is nonzero and F=(q^2-Z-G)/q is a positive integer
- F=(K+2^e)(W+Z) mod(q-1)
- F+2Z+W+ell*x<q

These equations force F,Z uniquely after(j,N) is chosen. They imply positive alpha=q-F-2Z-W-ell*x. They also imply the positive transport quotient1+((K+w)(W+Z)-F)/(q-1), because w=2^(p-t)>q and0<F<q. This proves the stated iff for the prescribed R and Nt=1. It does not characterize zeros produced by changing those intended factor values.

The sharp unresolved statement is: does there exist an actual genuine compiler and a known rejected positive x, and integers j>=0,N>=1, satisfying all four tests and scale restrictions above? No such pair or rejected-input certificate is supplied. Excluding all pairs only for this family would not prove general soundness.

Several genuine restrictions cannot be discarded:

- Since J divides both Q and M, the first test implies J|R
- If N is even, B=2^(5^r)=-1 mod11 gives11|J, but R=-1 mod11; impossible
- If3|N, B has order3 modulo7 and7|J, but u=4 mod7 and R=4 mod7; impossible
- Hence any completion requires gcd(N,6)=1
- With alpha>=1 and Z>=1, G=(2q-1)Z+q(W+ell*x+alpha)>=q(W+ell*x+3)-1. Therefore R>=[q(W+ell*x+3)-1](q^2-1)+M. This lower bound is algebraically sharp at Z=alpha=1, when F is positive

The exact materialized j=0 inner case is an especially concrete counterexample to confusing an inner fixture with a full completion. It has R=4575. Genuine positive-input compilers have d,b>=5, so W>=2^15=32768 and positivity forces q>W. The last lower bound already exceeds10^18 under the relaxed q>=32769,ell*x>=10,M>=1 bounds. Thus this j=0 fixture cannot be completed on any such genuine positive-input slice. Mock ports cannot evade this conclusion while retaining the genuine compiler requirements.

The Section6 warning about prime-existence shortcuts is also correct: after removing gcd(416,Q)<=13, the packing progression modulus is still comparable to q^2. On a fixed unwrapped transport branch F=L(W+Z), the Z-step in R is Q(1+qL), at least order q^3. No prime-existence result at the larger actual modulus was proved in this packet. This is a limitation of a proposed shortcut, not a nonexistence theorem for the interface.

## Source correspondence and executable evidence

The source register named A holds Delta, whereas the proof's mathematical A is a+2. This naming distinction is consistently respected. The exact gap path is(q-1)(q-F)+(q-F-Z)=q^2-qF-Z. The source uses the shifted MF numeral; replacing it by the native unshifted mask changes R and would invalidate the correspondence. All83 rows, all18 positive witness ports, the six fixed ports,46 multiplications,37 additions/subtractions, the factor order and final subtraction were checked as data. Degree111 is the upstream source claim and was not re-proved by this audit.

The main independent actual-family check materializes j=0 with u=11,p=2717,n=2288,R=4575,Y exponent626. Its c has9082305 bits; k has9081679 bits. Both exact Pell norms equal1. The strict ratio, literal index equation, literal main projection and gcd(c,p)=1 all pass. Positive input witnesses and exact input norms pass at I=3,5,17,2715, including the near-boundary I=p-2. Auxiliary witnesses for this enormous case are proved to exist by the theorem, not materialized.

Artifacts:

- audit.py and INDEPENDENT_CHECKS.json: all83 row paths; universal modular identities; exact actual-family inner fixture
- audit_auxiliary.py and AUXILIARY_CHECKS.json: independent CRT/quotient calculations, exact auxiliary fixtures, and incompatible-recipe example
- audit_interface.py and INTERFACE_CHECKS.json: genuine necessary congruence obstructions, sharp outer margin, author-receipt consistency
- source/complete83_free_coefficient_scout.json: immutable source snapshot used only as data
- AUTHOR_PROOF.reviewed.md: reviewed author proof; AUTHOR_PROOF.snapshot.md: earlier snapshot before the final wording changes

No uploads or external writes were made. All public claims should keep the inner/intended-factor/genuine-compiler distinctions explicit.
