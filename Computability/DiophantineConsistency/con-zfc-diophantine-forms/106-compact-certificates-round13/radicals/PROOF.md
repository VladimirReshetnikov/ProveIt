# Coprime scale carriers with fixed-prime root separation

This note gives ordinary algebraic reductions relative to the incoming signed CRT source17 theorem and its canonical completeness family. No new kernel certificate is claimed. The coherent six literal coefficients are the same source34/source71 ports as in root-fusion and prime-separation.

## Common prefix
All unknowns are unrestricted integers. Start with
j,C,z,h,r,v,w,T,c,n,t,p2,p3 (13 coordinates), adding f, gamma, p1 only where expressly listed below. Set
J=6j+1; q=beta J+1; W=12w+4; X=qW; Y=qv; E=XY; a=E+Y; H=4a+3; Delta=a^2+H;
F=(K0+W)C-z(q-1);
R=(q(q-F)-C)(q^2-1)+(MC+q MF)J;
k=R+1+hE; eta=c-Yk; zeta=k-eta;
u=XY^2 k; A_tau=u(u+k)+1; A_main=1+Delta c^2; b0=X+ac;
d=(cone_A F)(cone_B C)-(q-cone_A F-cone_B C)^2;
Bguard=d eta zeta-(t^2-d-eta zeta+1)^2-1-p2^2-p3(p3+1);
I=(2r+1)c^2; M=2q^2; U=MH; defect=v-q^2.

For ordinary strong f (14+ coordinates), set Q=I^2; S=Q-Delta(f^2-1); V=f c T-f^2 R-c. For normalized strong elimination (13 coordinates), set A_f=1+Delta I^2; Q=Delta^2 I^2; V=A_f(cT-R)-c. In both cases delta=Q-1; Cy=QV^2-1; A_y=Cy/delta (proof notation only).

## Elementary preliminaries and correct ordering
Because beta is odd, congruent1 mod3, and >17, J is odd and congruent1 mod3. Thus q is even, q=2 mod3, |q|>=16. W is nonzero and1 mod3, so X=2 mod3, |X|>=64. Y is even; a=(X+1)Y is even and0 mod3. In fact a is a multiple of6, so Delta=(a+1)(a+3)>=3. Therefore Delta>0, Delta=3 mod4, 3 divides Delta and H, and H is nonzero odd. H=3 modq, hence gcd(H,M)=1.

A_tau=1+b(b+1)k^2>=1 for integer b=XY^2; b=0 or2 mod3, hence A_tau=1 mod3. A_main=1 mod3. Under S=0 in ordinary variants, Q is a square divisible3, hence divisible9. Also delta cannot vanish: Q=1 would give Delta(f^2-1)=1 with Delta>=3. In normalized variants Q is divisible9 and cannot1 unconditionally. When Q=0, A_y=1. When Q>1 and A_y is recovered rational, the adjacent-Pell saturation lemma below proves its root integral. No positivity guard is assumed in these preliminary statements.

## Separation and integrality
Use roots with squared rational3-adic orders -2v3(H),0,2,4,(6): main d0/H, auxiliary y, first3tau, then guard9p1 in ordinary14 or strong9f and guard27p1 in normalized13. The guard root may be zero; its squared order is at least4 or6 respectively. For a rational linear combination with these fixed weights, every nonzero root is rational. Proof: a nontrivial subset of at least two roots has a unique even minimal3-adic square order; dividing by its power of3, the product over signs of the other roots is a unit mod3, so the signed sum cannot vanish. Subtracting a Galois conjugate of the rational sum would give such a forbidden sum; all roots are fixed by every automorphism and thus rational. This works even for negative radicands. Their rational recovered roots force them nonnegative.

Integer-square radicands yield integer roots. For auxiliary rational y and Q>1, QV^2-(Q-1)y^2=1 forces integer y by adjacent-Pell descent: in y=A/m reduced, m^2 dividesQ-1. Replace (V,y) by ((2Q-1)V-2(Q-1)y,(2Q-1)y-2QV), take signs positive, and descend in positive|V|; the new V is integral with smaller nonzero absolute value, and denominatorm is unchanged because 2Q-1=1 modm. At |V|=1, y=1. For Q=0, y=±1 directly. Hence no Q=0 exception is lost.

## Carrier restoration
For the ordinary14 and normalized13 norms take Z=U(n+V)+M b0+H defect. After root recovery the factor relation is
Z=M d0+U(3tau+y+9p1) (ordinary14),
or Z=M d0+U(9f+3tau+y+27p1) (normalized13).
ModuloM and H respectively, gcd(H,M)=1 gives defect divisibleM and d0-b0 divisibleH. Thus v=q^2(2v_old+1), Y=(2v_old+1)q^3, gamma=(d0-b0)/H are integers. In particular v≠0 now, after extraction. The guard root p1 is integral and p1^2=Bguard, restoring the exact joint positivity residual G=Bguard-p1^2=0. It implies d>0, eta zeta>0. Since c=0 would give eta zeta=-Y(Y+1)k^2<=0, c≠0 and Q>1 follow. This ordering is not circular.

The five residuals of the literal inherited degree88_17 parent are restored directly. Put old J3=2j, old C_native=C, old v_scale=(v-q^2)/M, and retain z,h,r,w,T,c,f and the guard variables. Restore its midpoint first coordinate as tau_old=2tau-(2u+k), its auxiliary gap as y_gap=y-V, and its main coordinate gamma=(d0-b0)/H. The first parent residual is
  tau_old^2+2 tau_old(2u+k)+k^2-4=4(tau^2-A_tau)=0.
The auxiliary parent residual is
  V^2+(1-Q)y_gap(2V+y_gap)-1=QV^2-(Q-1)y^2-1=0.
The other three parent rows are precisely the recovered main norm, S, and G. Every displayed parent polynomial abbreviation, including V=f c T-f^2 R-c, agrees after substitution. Thus soundness composes directly with the exact source17 system; no new CRT-quotient or Pell rank theorem is asserted or needed for this transformation.

For normalized13, put I_old=Delta I, r_old=(Delta(2r+1)-1)/2, and T_old=fT. Delta is odd, so r_old is integral, and the parent's V=f c T_old-f^2 R-c equals the new V. Q=I_old^2 and I_old^2=Delta(f^2-1), since f^2=1+Delta I^2. All five parent rows again vanish. This polynomial/rational-with-exact-parity restoration is independent of any division by Delta or c.

## Completeness
Start with a finite refutation and the inherited canonical source family. It has J odd and1 mod3, so J=6j+1; its scale Y=(2v_old+1)q^3 gives v=q^2(2v_old+1). Preserve the arithmetic and guard witnesses. Its midpoint first coordinate is congruent to k modulo2 by its own residual, so tau=(tau_mid+2u+k)/2 is integral. The source gap gives y=V+y_gap. Choose the single n to make the displayed root relation hold; defect/M and gamma are integers. For normalized13 use the separately proved canonical normalized strong and fresh auxiliary reconstruction, exactly as in incoming prime-separation/root-fusion. Nothing prescribes a new residue of a canonical guard witness.

## Finalizers
If integer residuals R1,...,Rm are never -2, then (1+N) product(1+Ri)-1=0 iff N=R1=...=Rm=0: every integer factor in a product equal1 is±1; each Ri factor must be+1, forcing also the lone unrestricted N factor+1. No claim about N modulo4 is needed.
S is never2 mod4: Delta=3 mod4, I^2 is0 or1, and f^2 is0 or1; if f even then S=I^2-1 mod4, if f odd S=I^2 mod4. The main residual D=(b0+H gamma)^2-Delta c^2-1 also never2 mod4: for c even D is0 or3, for c odd D is0 or1. Finally4G is always0 mod4.

## Complete packets
13: only base coordinates; N=delta^16 F5(Z;81U^2 A_f,9U^2 A_tau,M^2 A_main,729U^2 Bguard,U^2 Cy/delta); equationN=0; exact degree1072.
14: addf; N=delta^8 F4(Z;9U^2 A_tau,81U^2 Bguard,M^2 A_main,U^2 Cy/delta); P=(1+N)(1+S)-1; exact degree378.
15 direct: addf,gamma; Z=M(n+V)+defect; N=delta^4 F3(Z;9M^2 A_tau,81M^2 Bguard,M^2 Cy/delta); P=(1+N)(1+S)(1+D)-1; exact degree172.
16 centered: addf,gamma,p1. t0=2u+k, ell=k^2-4, x=M n+defect; j0=delta[x^2+M(6t0+4V)x+9M^2 ell]-4M^2(V^2-1); h0=12delta t0 V M^2;
N=j0^2+2h0j0+576delta M^4 A_tau(1-V^2)+144delta^2 M^4 ell V^2.
Exactly N=delta^2 F2(M(n+3t0+2V)+defect;36M^2 A_tau,4M^2 Cy/delta). P=(1+N)(1+S)(1+D)(1+4G)-1; exact degree98.
15 centered: addf,p1. Z=U(n+3t0+2V)+2M b0+H defect; N=delta^4 F3(Z;36U^2 A_tau,4M^2 A_main,4U^2 Cy/delta); P=(1+N)(1+S)(1+4G)-1; exact degree170. The factor relation recovers scale modM and gamma modH because2M is a unit mododdH. Completeness picks n=6tau+2y+2gamma-3t0-2V-defect/M.

## Exact degree upper bounds, including cancellation

The independently propagated prefix bounds are q:1, X:2, Y:2, a:4, H:4, Delta:8, R:5, k:5, u:11, A_tau:22, A_main:10, b0:5, Bguard:28, I:3, M:2, U:6. Ordinary Q and delta have degree 6 and V degree 7; normalized Q and delta have degree 22 and V degree 19. The residual bounds are S:10, D:10, G:28.

Naive exact DAG degree propagation already gives the required upper bounds 378,172,98 for ordinary14, ordinary15 and centered16. It gives only 1152 for normalized13 and 198 for centered15, so cancellation must be proved for those two. The following formal weighted-algebra arguments do so without relying on finite lines or generic asymptotics.

### Normalized13

Pair the two signs of the auxiliary root first. Write Z=UV+s and let

    B=s +/-9U f +/-3U tau +/-M d0 +/-27U p1,
    s=Un+Mb0+H(v-q^2).

The weights of the four formal roots f,tau,d0,p1 are 7,11,5,14. Their squared radicands have at most twice these weights, so reductions in the root algebra never increase weighted degree. Thus B has weight at most 20. The paired factor is exactly

    delta*((UV+B)^2-U^2*Cy/delta)
      =delta*B^2+2delta*U*V*B-U^2*(V^2-1).

The equality uses Cy=(delta+1)V^2-1 and is checked as an integer polynomial identity. The three term bounds are respectively 62,67,50. Taking the product over the sixteen signs of the other four roots therefore gives degree at most 16*67=1072. That product is exactly the cleared five-root norm, including its delta^16 factor.

### Centered15

Use the exact centered two-root identity, whose integer expansion is separately checked. In that identity replace M by U, t0 by 2u+k, ell by k^2-4, and x by

    x=Un+2Mb0+H(v-q^2) +/-2M d0.

Its weight is at most 7. Define

    j=delta*(x^2+U(6t0+4V)x+9U^2 ell)-4U^2(V^2-1),
    h=12delta*t0*V*U^2.

Then j has weight at most 30 and h at most 36. Every term of

    j^2+2hj+576delta U^4 A_tau(1-V^2)
          +144delta^2 U^4 ell V^2

has weight at most 66. The exact identity uses t0^2=4A_tau+ell and holds without any Pell zero assumptions. Taking the two main-root conjugates gives the cleared three-root norm of degree at most 132. Adding the product-finalizer factors contributes at most 10+28, giving 170.

For every circuit, two different actual-coefficient univariate specializations, modulo 65521 and 65519, attain the stated degree with a nonzero coefficient. The checker uses directions different from the builder's certificates and records every slope and actual fixed-port residue. Such a nonzero specialization proves the matching lower bound. Together with the universal upper arguments above, all five degrees are exact.

## Exact degree and executable audit
The finite modular-line certificates in CHECKS.json use both65521 and65519 with the actual six numeral payloads. Each attains the stated total degree with nonzero leading coefficient; this supplies the rigorous lower bound matching the preceding universal upper bound. Every complete graph is checked for topological order, declared-variable closure, all-leaf liveness, binary operation count, and actual coefficient raw SHA-256 identities. Independent direct formulas are compared against a formal32/16/8/4-sign product in a square-root algebra on signed modular inputs, including c=0, v=0 and their intersection. These are transcription diagnostics, not replacements for the universal norm identities or source theorem. Normal and optimized Python checks do not rely on removable assertions.

The literal operation counts are13/1072/192,14/378/145,15/172/123,15/170/134,16/98/138, in the order variables/degree/operations. Numeral leaves are free; every binary addition, subtraction, multiplication, squaring and scalar multiplication costs one, with shared identical subexpressions reused. The coefficients are exactly the coherent mixed-parity-unrounded-1064921 source34 tuple and the source71 cone scales. Fixed ports are not free parameters and the existing shifted MF is not shifted again.

## Universal norm identities
F_m denotes the product over all2^m independent signed sums of m radicals. Sign changes permute its factors, proving its integer-polynomial nature even when radicands are zero, negative, equal or algebraically dependent. The complete DAGs use the elementary identity
  F_3(x;a,b,c)=((x^2-a-b-c)^2-4(ab+ac+bc))^2-64abc x^2.
For four and five roots, evaluate the cleared three-root identity at x-u or x-u-v in the free algebra u^2=c, v^2=d, then take the two or four conjugates. Multiplication in the basis1,u,v,uv proves every displayed gate is integer polynomial arithmetic and the denominator-cleared expression is exactly delta^(2^(m-1)) F_m. The centered16 formula is the expansion of delta^2 F_2(M(n+3t0+2V)+defect;36M^2 A_tau,4M^2 Cy/delta); its identity is checked independently, including delta=0, in exact symbolic variables.

## Scope and rejected shortcut
No global minimum, historical priority, coefficient-height improvement or new Lean/Rocq certificate is claimed. The logical endpoint is obtained by composing the explicit algebraic reduction with the same pinned ordinary source17/native/compiler/K215 theorem used by the incoming packages. It is a theorem about the specified recursive syntactic refutation predicate, not a proof of consistency itself.

An attractive attempted12-coordinate shortcut is not justified: replacing the ternary positive representation1+p1^2+p2^2+p3(p3+1) by1+p1^2+p3(p3+1) fails even with t freely chosen. For determinant d=1 and eta*zeta=9, positive Pair=9-(t^2-9)^2 is possible only at t=±3 and equals9; but8 is neither a square plus z(z+1) for any integer z. Cofinal canonical tuning might avoid this obstruction, but is not proved here and is not claimed as a construction.

## Explicit carrier choices for completeness
Write e0=(v-q^2)/M. Then use n=9f+3tau+y+27p1+gamma-V-e0 for13; n=3tau+y+9p1+gamma-V-e0 for14; n=3tau+9p1+y-V-e0 for15 direct; n=6tau+2y+2gamma-3(2u+k)-2V-e0 for15 centered; and n=6tau+2y-3(2u+k)-2V-e0 for16 centered. These formulas use signed integral roots from the source and impose no new restriction on the guard variables.
