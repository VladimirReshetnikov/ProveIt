# Review of the saturated Pell and radical arguments

The new ordinary arithmetic arguments appear sound under the explicitly
retained H2082/native/refutation interfaces. This is a separate AI-assisted
peer review of the mathematics and literal data, not an external human
review or a proof-assistant derivation. No Lean was run.

## Modified Pell representation

Let delta=A^2-1 and use the source proof's definitions

```
D=1+delta*C^2, e0=i*J*C^2, F=1+delta*D*e0^2,
Lambda=C*D+1-A, G=A+F*Lambda,
H=C+F*(B+j0*C), I=1+(G^2-1)*H^2.
```

The hypotheses are A>=3,1<B<A,C>B,J>=A,i>=1,j0>=0.
They ensure all quantities are positive. Modulo D one has F=G=I=1;
modulo F one has I=D. Thus D,F,I are pairwise coprime, without assuming
primality. If their product is square, each prime valuation in each factor
is even, so all three are integer squares.

Write d^2=D. Pell classification gives indices s,m,t with
C=psi_A(s), psi_A(m)=i*J*C^2*d and H=psi_G(t). The new middle coordinate is
correctly d*e0, although the polynomial norm itself contains only one D.
C>B>1 forces s>=2. Also d>=A and C>=3 imply psi_A(m)>=9*A^2>psi_A(3),
so m>3. If any index argument needs m>s, that follows immediately from
psi_A(m)>C=psi_A(s); it is not an additional premise.

The rank argument handles even C. Strong divisibility gives s|m; write
m=s*u. In the binomial expansion of
(chi_A(s)+C*sqrt(delta))^u, the second coordinate is
u*chi_A(s)^(u-1)*C modulo C^3. Since C^2 divides psi_A(m), division by C
and gcd(chi_A(s),C)=1 give C|u, hence C|m. No odd-prime-only valuation
lemma is being applied at2.

For the needed index congruence, put x=chi_A(m). Addition identities give
psi_A(k+2m)=-psi_A(k) modulo x and
psi_A(2m-k)=psi_A(k) modulo x. Every index folds to a signed value
psi_A(r),0<=r<=m, with original index congruent to r or-r modulo2m.
The Pell identity and A>=3 give x>2*psi_A(m). The signed folded values lie
strictly between -x/2 and x/2, so equal residues are equal integers.
Strict growth then forces equal folded indices. This proves the required
s=+/-t modulo2m without silently assuming that t is small.

The precise external congruence statement also matches this use:
[Sun, Lemma2.2](https://arxiv.org/html/2609.01594v1), with Lucas parameter2A
and v_m(2A)/2=chi_A(m). Its m>3 hypothesis is established above. The
positive Pell divisibility identities are also recorded in
[CILC2015, Fig.5](https://ceur-ws.org/Vol-1459/ProceedingsCILC2015.pdf).
The explicit folding derivation is sufficient for the narrower range here.

Modulo C, one has F=G=1 and H=B, so t=B modulo C. Because C|m, the
index congruence gives s=+/-B modulo C. For s>=2, psi_A(s)>=A*s and B<A,
hence0<s+B<C and |s-B|<C. The negative branch is impossible and the
positive branch gives s=B. This closes soundness of the modified certificate.

Completeness has a genuine unbounded construction. The determinant-one
Pell recurrence matrix has finite order modulo the positive integer
J*d*C^2. A positive multiple of that order makes psi_A(m) divisible by
this modulus and gives a positive integer i. Having fixed i and G, choose
a recurrence period T modulo F. The progression t=B+k*T*C preserves both
t modulo T and t modulo C, without any coprimality assumption on T,C.
The quotient (psi_G(t)-C)/F is integral, is B modulo C because F=1 modulo C,
and grows without bound. Eventually it yields j0>=0 and the exact required
H. Alternatively, i_new=d*i_old preserves the complete old F,G,H,I on an
actual old certificate. It is only an existential transport on such
certificates, not a polynomial inverse on arbitrary assignments.

## Positivity before integrality

The cheap majorant satisfies exact identities

```
Tmajor^2-D*F = D*(D*e0^2-1),
(Tmajor*G*H)^2-D*F*I
 = (Tmajor^2-D*F)*(G*H)^2+D*F*(H^2-1).
```

These defects are strictly positive on every ambient positive assignment,
before the final equation is used. The other majorant defect is K^2-1>0.
E0>0 excludes Omega=0 at a final zero. Real factorization of the two-root
norm gives E0=Omega*(V0+V1+r0+r1) for signed real roots. The strict
majorants make the parenthesis positive for every sign choice; therefore
m>0 is recovered before invoking any integer-root theorem.

The inherited margin now supplies |C-KY|<K/2 and C>B1+W1. In particular
C>K. The elementary inequalities A^2>P,D>C^2,F>=A^2,I>=A^2 give
DFI>C^2*A^4>K^2*P^2>a0. Hence x=r0+r1 cannot vanish. Since x=Theta/Omega
is rational,2*x*r0=x^2+a0-a1 makes both roots rational. Their integer
squares make them integral. Only then is J|Q deduced. Thus neither the
ambient range nor the margin is justified circularly using the Pell
representation that it is about to license.

For the radical variant, sigma=1024*C^5*i is a positive integer. An integer
root of sigma^2*DFI gives a rational root r1/sigma of the integer DFI;
that rational root is integral. No unproved divisibility shortcut is needed.
Completeness has n>0 because both majorants exceed2D, while the unchanged
canonical source witnesses satisfy W1^2+Q/J<2D. The source proof supplies
those witness and source bounds as inherited dependencies, not sample data.

## Radical correction and exact degrees

In the four-variable radical calculation J is specifically4A-5. The local
theorem allowing arbitrary J is not used to justify a polynomial calculated
with a different J. The uncorrected333-term polynomial P is not itself an
upper bound. The correction is the lower-A-degree term

```
L0=2^20*C^24*i^6*Z,
Pplus=P+L0,
sigma=1024*C^5*i.
```

The positive shifted P table has6650 terms and positive constant
15915642730652. The shifted corrected defect
Pplus^2-sigma^2*DFI has36309 positive coefficients and constant
32237226735615909648. Consequently Pplus>sigma*sqrt(DFI)>0 throughout
A>=3,C,i,Z>=1, including the boundary. The uncorrected defect has a
negative boundary value and is explicitly rejected as a majorant.

At weights(18097,1,1,8799) on A,C,i,Z, the complete unique positive leaders
checked in the materialized certificate are

```
cheap V1:       2^10*A^18*C^19*i^5*Z,
cheap defect:   2^20*A^34*C^38*i^10*Z^2,
radical V1:     2^20*A^18*C^24*i^6*Z,
radical defect: 2^41*A^18*C^48*i^12*Z^2.
```

The exact cancellation-resolved outer norm identity is verified as a free
polynomial identity. For the cheap endpoint its four summand degrees are
1628768,1393484,1095110,1122006. For the radical endpoint they are
1049688,1103950,1095122,832466. In each case there is one largest term,
with positive leading coefficient. The negative leading sign of Omega is
irrelevant because its dominant occurrences are squared. The retained
source's nonzero leading terms give exact specialized degrees1628768 and
1103950, not merely syntactic upper estimates.

## Finite binding and limitation

The candidate's verifier confirms all four literal DAGs, whole natural
translation, every new norm and certificate register, all shifted tables,
the exact topology and all11 fixed leaves. Full original binding bytes and
every compressed/uncompressed shared payload hash match the raw arrival.
Reconstruction from the entire four-port compact54-sharp tuple confirms
every signed leaf byte; MF_source is not shifted again. The sole relocation
of fixed_binding is reversed and checked against each original DAG hash.

The copied release verifier is independent of its builders and was inspected
before loading. Its compressed table reader is the only adaptation. This
review does not claim that its polynomial engine was independently
reimplemented. Normal and optimized replays and a corrupt-final-gate control
pass. None of these finite checks replaces the retained unbounded native
compiler or refutation calibration, or the remaining internal-ZFC proof.
