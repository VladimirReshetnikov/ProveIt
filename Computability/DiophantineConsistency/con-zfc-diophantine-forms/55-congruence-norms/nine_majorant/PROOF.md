# Congruence separation with a polynomial majorant

This note records an independent arithmetic review and the resulting
construction at repository pin 4b4349064a750ba6347293b55874a7f92abdd0db.
The code lives in build_nine.py. It retains the original package 31 positive quadratic source and the native
coefficient tuple. The fused frontend evaluates the unshifted 94-record
quadratic source at the packed word 1+g+ell. It uses the repaired
code_positive.json targets: original row 13 has target 2124 and row 21 has
target 1059. The source coefficient polynomial has leading coefficient 1.
All 49,632 record-by-word interactions are separately audited.

## Exact statement

The generated polynomial on nine positive integers has exact degree
5,671,669 and 630 live binary operations. Its natural-coordinate translate
uses 636 operations and has
the same degree. The supplied degree-certificate circuit evaluates D^16
times the primary polynomial; it is not the recommended evaluator.

The new arithmetic reduction preserves existence of source zeros. Composing
with the inherited source-to-refutation compiler gives the ordinary theorem
formalizable in ZFC that absence of zeros is equivalent to Con(ZFC).
This is not a new end-to-end Lean or object-language ZFC proof artifact.

## 1. Even coordinates and completeness

Use the calibrated selective source, but substitute the actual coding
coordinate g=2g' and the actual Jones multiplier h=2h', where g',h'>0.
For natural input coordinates use g=2(g0+1),h=2(h0+1).

The base B is even on every assignment. The calibrated block length L and
the lower block modulus N0 are even. Consequently S=g+N0*Jcode is even and

 R=L^2+(S+T)L+L-1-S

is odd. Jones's P=2M^2U is even, and

 K=R+1+h(P-1)

is even. Hence a0=(P^2-1)K^2+1 is1mod4.

Every weight of the inherited selected source code is positive (minimum7),
so its canonical g=sum n_i B^w_i is even, where the original positive source
coordinate is n_i+1. It is positive because if every n_i were zero, parent
residual 5, E X+E-a X, would equal 1. Thus source completeness supplies positive
g'=g/2.

For h, the actual construction in upstream/Ratio.lean:exists_B25core takes
K=psi_P(R+1), then derives positive h from K=R+1+h(P-1). The Pell recurrence
psi_P(0)=0,psi_P(1)=1,psi_P(n+2)=2P psi_P(n+1)-psi_P(n)
gives psi_P(n)=nmod2 by induction. Since R is odd, K is even, and since P-1
is odd, h is even. Hence this same construction supplies h'=h/2>0.
No unproved claim that arbitrary arithmetic witnesses are cofinal in an
imposed congruence class is being used here.

## 2. Polynomial majorant

Keep the Jones ratio registers A,C,D,E,F,G,H,I,J,i, with

 e=iJC, Lm=CD+1-A, D=(A^2-1)C^2+1,
 F=e^2 D^2(D-1)+1, G=A+F*Lm, I=(G^2-1)H^2+1.

Let lambda=2048 and define

 Nstar=2G+Lm,
 N1=2e^2D(D-1)Lm+3C,
 N2=2e^2(D-1)Lm,
 N3=2e^2(Lm-C), N4=2e^2C,
 correction=256i(e^2+2)+2048,
 Tm=e[(1024D^2-512D-128)Nstar-64N1-40N2-28N3-21N4]
      +correction.

The source coefficient polynomial is positive for every b>=2: its leading
coefficient is 1, it has only 94 records, each coefficient has magnitude less
than 2^2134926, and the base is at least 4*2^2134940. The total possible lower
coefficient contribution is therefore smaller than the leading monomial.
The mask is positive by comparison with the full geometric sum, so R>=8.
This verifies the positive ratio-register hypotheses after source fusion.

All are polynomial abbreviations. The inherited upstream/HIGHER_MAJORANT.md proves
Tm>lambda sqrt(DF)G for every A>=3,C,i>=1. Its hypotheses hold
unconditionally here (indeed A>=33280). Because I<=G^2H^2 and H>=1,

 V1=Tm*H > sqrt(a1), where a1=lambda^2 DFI.

The majorant's previously supplied Bgap padding and its h multiplier are
unnecessary in the new finalizer. We retain V0=PK, for which
V0^2-a0=K^2-1>0. Thus V0>sqrt(a0).

For completeness, the key inherited majorant identity is as follows. Put

 tn=1024D^6-512D^5-128D^4-64D^3-40D^2-28D-21,
 dn=33792D^5+10560D^4+4928D^3+2464D^2+1176D+441.

Then tn^2-1024^2D^11(D-1)=dn>0. The four exact remainders
Nstar=D^j Nj+rj are

 r1=3-A,
 r2=3CD+3-A,
 r3=2e^2(A-1)D^2+r2,
 r4=2e^2(1-A-C)D^3+2e^2(A-1)D^2+r2.

These turn Tm into the rational approximation e*tn*Nstar/D^4 plus explicitly
bounded remainders. The correction dominates the negative remainder terms
using eA/D<9i/2, eC/D<3i/2, and e(A+C-1)/D<6i. The strict concavity inequality
sqrt(X+D)<sqrt(X)+D/(2sqrt(X)), with X=e^2D^3(D-1), then proves the stated
majorant. The full uniform-inequality argument is retained in the pinned
upstream note; it holds for all assignments, not merely asymptotically.

## 3. A two-root norm needs no multiplicative separator

Let u=JF>0,v=QF+J(H-C)>0 and Mdiv=Q+H-C, so0<v/u<=Mdiv.
Let mu be the usual Jones margin, and put

 Omega=u(2mu-1),
 E0=un+v-Omega*Mdiv,
 Theta=E0-Omega*(V0+V1),
 F9=(Theta^2-Omega^2(a0+a1))^2-4Omega^4*a0*a1.

Since mu is integral, Omega is nonzero on every assignment. Both radicands
are positive. Section1 proves a0=1mod4; the fixed factorlambda^2 proves
a1=0mod4. Thus a0!=a1 unconditionally.

Suppose F9=0 and write t=Theta/Omega inQ. The norm identity gives

 (t^2-a0-a1)^2=4a0a1.

Equivalently t=r0+r1 for signed real roots r0^2=a0,r1^2=a1. If t=0 then
a0=a1, impossible. Hence

 r0=(t^2+a0-a1)/(2t), r1=t-r0

are rational. A rational square root of an integer is an integer, so both
radicands are squares. Moreover a1=lambda^2DFI is square exactly when DFI
is square, again by the rational-root lemma.

Since V0,V1 are integer strict majorants, |rj|<=Vj-1. Therefore
Z=Mdiv+V0+V1+r0+r1>=Mdiv+2>0. The selected factor equation is

 n+v/u=(2mu-1)Z.

Its left side is positive, so mu>0; its right side is integral, so u|v.
Thus every zero recovers the four unchanged Jones ratio conditions.

Conversely assume those four conditions. Take any signed integer roots,
form Z as above, and set n=(2mu-1)Z-v/u. This is integral and at least2,
hence an allowed natural input. The selected factor vanishes. This proves
the finalizer equivalence in both directions and, with Section1, source
existence-equivalence.

The only new restriction on the source/Jones coordinates was the proved
even-coordinate specialization. No assumption of ZFC consistency, unknown
coefficient choice, or transcendental operation enters the polynomial.

## 4. Exact degree and why a second cancellation is essential

Use the calibrated source's nine input coordinates, all of total degree1.
The decisive exact degrees are

 D139324; e69663; G719588; H22967; P81527; K81528;
 V0 163055; V1 1090866; Omega791147; E0 814115;
 a0 326110; a1 2181732.

Define delta0=V0^2-a0=K^2-1 and delta1=V1^2-a1. The inherited majorant
identity, with the Bgap terms omitted, gives

 deg(delta0)=163056, deg(delta1)=1253160.

A naive gate degree walk of the primary expression overestimates its degree.
The following exact identity exposes the cancellation of the leading root
products. Set

 Bsmall=E0^2-2E0*Omega*(V0+V1)+Omega^2(delta0+delta1).

Then

 F9=Bsmall^2+4Omega^2 V0V1 Bsmall
       +4Omega^4(delta0 V1^2+a0 delta1).

The three summand degrees are respectively

 5,670,908; 5,671,669; 5,509,376.

The middle term is uniquely highest. Its leading coefficient is positive
and nonzero; there is no cancellation to infer statistically.

The division-free certificate computes D^8*delta1 by the inherited exact
identity, D^8*Bsmall by the displayed formula, and consequently D^16*F9 by
the two-defect identity. Its exact degree is 7,900,853. Since
16deg(D)=2,229,184, the primary exact degree is 5,671,669.
On the diagonal of positive or natural variables, with fixed
base scale a=2^2134940 and threshold scale c=2^16012040, its leading coefficient
is exactly 2^507*a^2835574*c^348. The certificate's coefficient is
2^667*a^3950070*c^476; dividing by the known leading coefficient of D^16
recovers the former. This division occurs only in the mathematical degree
argument; neither literal circuit divides.

## 5. Reproduction and verification boundary

Run build_nine.py to regenerate the four primary/certificate circuits and
exact-degree records. check_ring_identities.py expands all decisive identities
as integer polynomials independently of the circuit builder. Its small
polynomial-ring engine is adapted from the inherited majorant independent
checker and retains the same mathematical identity definitions.

check_circuits.py checks every gate is live, all operands precede their uses,
the paid operation ledger,240 actual-coefficient modular comparisons of
certificate=D^16*primary, and40 congruence fixtures. The fixtures test the
implementation; the universal parity and inequality proofs are Sections1-3.

This is an AI-assisted independent review within the session, not external
human peer review. The unbounded compiler, syntactic calibration and Jones
ratio theorem remain explicitly inherited dependencies.
