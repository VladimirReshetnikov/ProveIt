# Exact degrees and literal cost of the round-15 norm pair

## Frozen circuits and domain

The selected files are `integral_centered_paired.json` (11 unrestricted integer variables, exact degree 464, 119 live binary operations) and `integral_direct_paired.json` (11 unrestricted integer variables, exact degree 488, 118 live binary operations). Their mathematical prefix is the frozen three-adic construction in `../scalar/PROOF.md`. The complete six ports are beta, K0, MC, MF, cone_A, cone_B; all six authentic byte payloads and their binding are included under `coefficients/`.

Every binary addition, subtraction and multiplication is charged, including scalar multiplication and squaring. Reuse is free. Integer literals, variables, and the six fixed coefficient ports are leaves, not operations and not new unknowns. Every retained arithmetic node is live. The selected pair has respectively (74 multiplications, 24 additions, 21 subtractions) and (74 multiplications, 23 additions, 21 subtractions).

The generator is original local code and imports no upstream executable. The independent skeptic's full register-cut audit is in `../scalar_audit/`; `check_norm.py` independently checks full-byte bindings, all 35 coefficients of the universal radical identity, the center identity, topology, and the exact leading coefficient of every literal DAG node (with the proved cancellation substituted at its one identified node).

## A paired quadratic-norm identity

For formal independent A,B,G,Z put

N(Z;A,B,G) = [(Z^2+A-B-G)^2 - 4(AZ^2+BG)]^2 - 64(AZ^2)(BG).

In the free triquadratic algebra this equals

product over eps in {−1,1}^3 of (Z−eps1 sqrt(A)−eps2 sqrt(B)−eps3 sqrt(G)).

Equivalently it is [(Z^2−A−B−G)^2−4(AB+AG+BG)]^2−64ABGZ^2. These are identities of complete integer polynomials, not numerical ray checks. Multiplying all eight conjugates gives exactly 35 monomials and zero coefficients on all seven non-scalar radical basis elements. Reusing AZ^2 and BG saves one binary multiplication over the source's symmetric norm schedule.

In the selected circuits, A=9S^2 Df, B=S^2 delta Cy, G=81S^2 P. The direct coordinate is Z=Sn−Ac; the centered coordinate is Z=S(n+QV)−Ac. The center is an integral shear, so it preserves integer-zero existence without any congruence condition on n.

## Weighted guard: one additional exact multiplication saving

The selected literal graph stores D81=243Budget−324, Dg81=81+D81 Dt s^2, P81=Dt Dg81, and G=S^2 P81. The complete polynomial identity

81+(243Budget−324)Dt s^2 = 81[1+(3Budget−4)Dt s^2]

proves Dg81=81Dg and P81=81P. Thus G remains exactly 81S^2P, with no zero-set change, new restriction, division, or change in witness ordering. Absorbing the constant81 into the existing guard constants saves one scalar multiplication. The proof uses conceptual D,Dg,P; their weighted counterparts are the live literal registers. The checker verifies this entire identity, not numerical instances.

## Prefix degrees and their leading forms

A subscript star denotes the highest homogeneous part in the eleven variables, with the six authenticated ports fixed constants. Let

q*=6 beta j,
X*=12w q*,
Y*=2v (q*)^3,
a*=X*Y*,
F*=12w C−6 beta j z,
R*=−(q*)^3 F*.

Then the exact leading forms needed below are

I*=r c^2,
S*=4s r a*,
Df*=(a*)^2 (I*)^2,
Q*=(a*)^4 (I*)^2,
V*=−Df* R*=(a*)^2 (I*)^2 (q*)^3 F*,
Ac*=(4a*T)^5,
Dt*=h^2 (a*)^4 (Y*)^2,
D*=−12(q*)^2 (Y*)^2 h^2(a*)^2,
P*=−12s^2 h^6(q*)^2(a*)^10(Y*)^6.

In particular the exact degrees are

I 3; S 8; Df 18; Q 30; V 23; Cy 76; delta Cy 106;
Dt 34; Dg 60; P 94; Ac 35; A 34; B 122; G 110.

The dominant term of V is −Df R, not the interpolation term 4Df I T. This distinction is essential after decoupling the strong scale.

The two nonzero norm-leading factors are

B*=16s^2 r^10 c^16 (a*)^14(q*)^6(F*)^2,
G*=−2^6 3^5 s^4 r^2 h^6(a*)^12(q*)^2(Y*)^6.

Both are nonzero polynomials for the authentic positive beta.

## Centered degree 464: global upper bound and exact attainment

Write W=Sn−Ac and C0=SQV, so Z=W+C0. The complete exact identity

Z^2−B = W^2+2SQVW+S^2[Q(V^2+1)−1]

has degree 96: the three displayed terms have degrees 70, 96, and 92. Its degree-96 part is −2S*Q*V*Ac*, which is nonzero. Adding A cannot affect this degree. Hence

v=Z^2+A−B−G has degree 110 and top form −G*.

The paired inner bracket is

v^2−4(AZ^2+BG).

Here v^2 has degree 220; AZ^2 has degree 156; BG has degree 232. Therefore the bracket has degree 232 and top form −4B*G*. Its square has degree 464. The final correction 64(AZ^2)(BG) has degree 388, so it cannot cancel that top form.

Consequently the entire highest homogeneous form is

16(B*)^2(G*)^2
=2^24 3^10 s^12 r^24 c^32 h^12(a*)^52(q*)^16(Y*)^12(F*)^4
=2^452 3^322 beta^260 j^260 w^52 v^64 h^12 s^12 r^24 c^32(12wC−6 beta jz)^4.

For example, the coefficient of

j^260 w^56 v^64 C^4 h^12 s^12 r^24 c^32

is exactly 2^460 3^326 beta^260, strictly positive. Its total degree is 464. A second endpoint has j^264 w^52 v^64 z^4 h^12 s^12 r^24 c^32 with coefficient 2^456 3^326 beta^264. This proves exact degree over the authentic integers, not just over a finite field and not only along a sampled line.

## Direct degree 488

In the uncentered circuit Z has degree 35, hence Z^2 has degree 70. The largest term of Z^2+A−B−G is uniquely −B*, degree 122. Its square has degree 244, while AZ^2 and BG have degrees 104 and 232. Thus the inner bracket has top form (B*)^2, and the output's entire top form is (B*)^4, degree 488. The final correction has degree 336 and cannot cancel it.

One attained monomial is

j^248 w^64 v^56 C^8 s^8 r^40 c^64,

whose coefficient is exactly 2^448 3^312 beta^248 > 0.

## Tested but dominated alternatives

The unfused symmetric comparison graphs cost two additional multiplications: centered 464/121 and direct 488/120. One saving comes from the paired norm and the other from the weighted guard. Expanding the center cancellation directly gives a syntactic degree-464 circuit but costs 136 operations. Replacing delta*y by y and clearing the auxiliary denominator gives degree 560 and 125 operations uncentered (126 centered). These are not selected. No field-normalization shortcut or unproved division is used in either selected integer circuit.
