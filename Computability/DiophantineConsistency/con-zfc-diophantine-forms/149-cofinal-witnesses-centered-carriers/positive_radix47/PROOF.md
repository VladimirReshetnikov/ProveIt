# Whole incoming complemented-label radix47 specialization

## 1. Status and exact theorem boundary

This is a separately scoped specialization of all four new lower-Y charts to
one complete fixed tuple: the **incoming complemented-label radix47 tuple**.
The sibling `positive/` radix67 component remains frozen and canonical.
The row lists, ten strictly positive inputs and exact degree proofs are identical;
the actual specialized integer polynomials are different because all four fixed
ports change. The useful alternate profiles are 79/382 and80/338; 78/516 and79/456
are dominated controls. The four raw integers total 207,214 bytes; the largest has
415,904 bits. This is storage reuse of an incoming result, not a new encoding,
carry theorem, controller, compression result or global-simplicity record.

Do not confuse this source with the current repository's conditional47
three-anchor/clause-alias layout. Our source is the complete incoming package
`docs/incoming/ConZFC_Common_Remainders_Radix47_2026-10-25.zip`, inspected at
snapshot 3ecd6a6cf53d47519228328567f45fb7ee9781d9. Its own retained source snapshot
is 55d1f72aedebf892e446c90d35fa1ae37689b0f2. Its complete ordinary proof is
`provenance/radix47/radix47/radix47_proof.md`, SHA256
3c854e9fb951f030f9d5b9dc7186c3be98f65cf4b94c63810869add08ec2c224.
The full incoming P66 polynomial, formula, coefficient payloads,51 native target
identities, finite receipts, independent review, and all 37 pinned dependencies
are copied, not replaced by a citation to an unavailable source.

The equivalence is ordinary mathematics formalizable in ZFC, composed with the
named retained P66/Pell and syntactic-refutation calibration. Each new polynomial
has a positive zero exactly when that calculus has a finite ZFC refutation.
Consequently ZFC proves no positive zero iff Con(ZFC). No consistency decision,
new complete Lean/Rocq proof or emitted object-ZFC certificate is asserted.
The incoming encoding is not claimed newly accepted in the current repository.

## 2. The entire coefficient recipe, not four arbitrary ports

Retain the same complete 436-character seed, 430 decoded actions, and 943 indexed
tiles t_i=(w_i,n_i,p_i,s_i), including Start0 and Forbidden1. Replace each physical
horizontal label by 255-label and each vertical label by 511-label. These are
bijections applied to both ends of every edge; occupancy and phase anchors are
not complemented. The whole native language, including the forbidden distinction,
is transported bijectively, not inferred from sampled words.

Put rho=2^47, L0=8807, d=47L0=413929, Bbase=rho^L0, beta=Bbase-1 and
Lambda=rho^4393+rho^5495. The complete 3297 coefficient array is

    u_i=w_i+2^8 n_i+2^17 p_i+2^25 s_i;
    c_i=1+2^10(u_i+1), i=0,...,942;
    c_(1023+j)=2^(10+j), c_(1003+j)=2^(27+j), j=0,...,7;
    c_(1013+j)=2^(18+j), c_(983+j)=2^(35+j), j=0,...,8;
    c_e=2^44 for e in {992,1011,1022,1031,1095,2195,3296};
    c_e=0 otherwise.

Let Ephys be the full 986-position support, including the two zero-coefficient
dummy positions 1063,1064, as printed in the incoming proof and our coefficient
appendix. Define

    K0=rho^30+rho^62+rho^1100+rho^2201+rho^8849
       +sum_(e=0)^3296 c_e[rho^(4393-e)+rho^(5495-e)],
    MC=beta-sum_(e in Ephys,e!=1)rho^e-2rho^1063,
    Ccore=sum_(e=1013)^1022 rho^e+sum_(e=1065)^1073 rho^e
          +rho^2195+rho^3296,
    Z47=(rho-1)sum_(e=8792)^8806 rho^e
        +(rho-1)sum_(e=7691)^7693 rho^e+(2^28-4)rho^7694,
    MF_native=4+(rho-2)Lambda+Ccore+Z47,
    MF=beta+MF_native.

The source mask is shifted by beta exactly ONCE. This is not obtained by simply
changing 67 to 47 in old padding or in old selector coefficients. All seven shared
marker weights are 2^44; all 34 physical label bits are complemented.
`rebuild_coefficients.py` decodes the full seed and all 943 tiles, reconstructs
all 3297 coefficients and all four integers, and compares them with the actual
whole incoming P66 binding and payloads. It imports no inherited producer.

The independently recomputed finite facts include

    sum(c_e)=3953059820717999,
    max(c_i:i<943)=15049678914561 <2^44, max(c_e)=2^44,
    pc(MC)=d-986, pc(MF_native)=986,
    MC=2 mod4, MF_native=4 mod8,
    beta odd>=31, K0>0, 0<MC<beta<MF<2beta.

## 3. What the new native decoder and controller actually license

The complete incoming proof, sections 3--5, supplies the changed native soundness:
its full convolution bound yields a cyclic carry cap 29; the low ten selector
bits force at most one selector since 943+29<1024; the payload then recovers the
complemented label and all seven markers. An occupied clause emits carry 1, which
is retained. Decoding improves the carry cap to12. Separate exact predecessor
resets protect phase anchors, all ordinary copy tests, both clauses, all 872
padding bits and the next cell origin. The two-anchor argument recovers a
whole-Bbase temporal stride. Inverting the color bijections recovers the retained
marked periodic language and finite syntactic refutation. These are proved for
arbitrary length, not established by finite examples.

Its sections 6--7 supply fresh canonical words under every simultaneous safe
low-dummy subset, with positive margin and actual rank

    0<F<q/rho^15, 0<C<q/rho^5510, alpha=q-F-C>0,
    q=Bbase^N, pc(R)=3dN+2, R=3 mod4.

The new controller prime is 1012691. The actual whole K0 gives

    modulus:         47       8807       1012691
    Bbase:           12       2677       959313
    K0:               5       4079       1005855
    1+Bbase K0+Bbase²:17       5042       834350
    order(Bbase):    23       4403       1012690.

All relevant brackets and Bbase²-1 are units. Its lift is
Bbase^1012690=1+282338*1012691 modulo1012691², with valuation exactly one.
Our reconstruction verifies those primes, exact orders, units and the lift
using the actual entire new K0. No radix55 unit, mod5 wrap argument, or different
radix47 condition is imported.

The cofinal width/height powers of that prime and the proved subset-sum orbit
change the ACTUAL native rank, not an independently prescribed R. The conclusions
needed below are

    R>3q, W_native=2^(R-dN)>Bbase^width,
    W_native=Bbase^width mod(q-1), X=q W_native=2^R,
    z_source=1+z0+[(W_native-Bbase^width)/(q-1)]C >=1,
    t=z_source-1>=0,
    (K0+W_native)C-F=t(q-1),
    q³|Y, with Y/q³ positive odd and Y the native half-binomial.

The last half-binomial/Pell construction is the incoming section 8 composed
with its retained uniform P66 source theorem. Its d and N are odd, so the
source square-scale contracts hold; no stronger fourth-power assumption is used.

## 4. Arithmetic interface of the new four charts

Use exactly the four complete definitions in `REDUCTION_PROOF.md`, substituting
THIS entire tuple. That file is frozen historical proof text from the sibling 67
component; its coefficient-size and numerical-native labels refer to that
original specialization. This bridge changes the final native source and fresh
canonical data, not its displayed arithmetic identities or degree proofs.

Reduction sections 1--5 are uniform in the ports subject to precisely the scalar
box, scalar mask phase, and mask-population interface just listed. The root
extraction, signed folding, third-index exclusions and B>=0 argument do not
invoke any decoder early. The outer R bound, normalized rank and mask parity
use the same algebraic R and source shift. The first-index q⁴ congruence uses
literal X,Y normalization. Projection before full denominator uses only
H=-1 modq and the same universal Pell/ratio identities. Thus their hypotheses
are all matched by this whole tuple, with no old numeric decoder used.

A zero therefore produces positive J,F,alpha,Wbase,Y and C>0 with

    q=beta J+1, X=q Wbase=2^R, q³|Y, R=3 mod4,
    Y equal to the native half-binomial,
    (K0+Wbase)C-F=t(q-1), t>=0 integral.

In the q1 chart Wbase=qw; in q2 Wbase=w. Setting z_source=t+1>0 yields
exactly

    (K0+Wbase)C+(q-F)-z_source(q-1)=1.                  (15)

The source rank is unchanged because h(q-F)+alpha=q(q-F)-C. These are the
uniform ordinary positive-source premises of the SAME P66 kernel printed in
the incoming 47 package. The uniform source recovery of q=Bbase^N and the native
masks precedes the new 47 carry/decoder theorem. It does not use the old 67 decoder.

## 5. Explicit positive bridge to the incoming P66 equation

For clarity, here is the intermediate polynomial, not merely a numerical-port
box. Reconstruct fresh source witnesses from the recovered outer data. Put

    a_s=Y(X+1), A_s=a_s+2, H_s=4a_s+3,
    Delta_s=A_s²-1=a_s²+H_s,
    c_s=psi_(A_s)(R).

The retained uniform source reconstruction, with the native half-binomial Y,
supplies positive k_s,tau_s,eta_s,zeta_s, with

    k_s=eta_s+zeta_s, c_s=k_sY+eta_s, 0<eta_s<k_s,
    tau_s²-XY²(XY²+1)k_s²=1,
    h_s=(k_s-R-1)/(XY)>0 integral,
    D_s=X+a_s c_s+gamma_s H_s=chi_(A_s)(R), gamma_s>0.

Choose a fresh strong positive pair with

    f_s²-Delta_s i_s² c_s⁴=1,
    S_s=Delta_s i_s c_s².

The same ordinary auxiliary completeness lemma supplies positive V_s,y_s and
the raw positive quotient

    T_s=(V_s+c_s+R f_s²)/(c_s f_s²),
    V_s=f_s²(c_s T_s-R)-c_s,
    S_s²(V_s²-y_s²)+y_s²=1.

Use the P66 inputs J,F,alpha,z_source,f_s,h_s,i_s,T_s,
s_source=Y/q³,Wbase,tau_s,eta_s,zeta_s,y_s,gamma_s, all positive.
The complete incoming P66 factors are then literally

    N0=tau_s²-ell_s(ell_s+k_s)=1, ell_s=(XY)(k_sY);
    N1=D_s²-Delta_s c_s²=1;
    Na=S_s²(V_s²-y_s²)+y_s²=1;
    Nk=k_s-h_s XY-R=1;
    Nt=(K0+Wbase)C+(q-F)-z_source(q-1)=1;
    Ns=Delta_s f_s²-S_s²=Delta_s.

Therefore N0*N1*Na*Nk*Nt*Ns-Delta_s=0 for the ENTIRE incoming 47 tuple.
This permits application of its actual ordinary P66 theorem and its new 47
native soundness to yield a finite syntactic refutation. Source witnesses are
proof constructions, not extra variables of our ten-variable polynomial.
We neither identify A_s with our A nor reuse our strong ordinate numerically.

## 6. Constructive converse through fresh47 controller data

Feed a finite refutation to the incoming 47 canonical construction and controller,
not the old 67 or55 one. Section3's genuine data have q=2^m, m=dN>=5,
X=2^R, R>3q, q³|Y and t>=0 with the exact new transport. The inequality
R>3*2^m>=6m gives q⁶|X. In q2 choose w=X/q, s=Y/q². In q1 choose
w=X/q², s=Y/q. All four quotients are positive integers. In both charts
Wbase=W_native, so the actual coefficient of C in B is preserved.

Now apply reduction section 7 at scale one: form the first/main Pell witnesses,
eta,zeta from the half-binomial ratio, choose a fresh positive Pell period
modulo c²tau, double it, and take the actual positive unshifted T. The first
recurrence and q⁶|X give integral rho=e/D. Projection gives integral kappa;
canonical sigma=Y/q³ is integral. Finally

    n=gy+(1+hL)t+rho-kappa-sigma>0,

because the fresh seed construction gives g>kappa+sigma. The carrier is z=gy
and the new polynomial vanishes. This constructs all ten independent inputs
positively, using the actual rank produced by the new 47 controller. It does
not assert a pointwise equality of packed words or an inverse witness shear
between two different numerical coefficient specializations.

## 7. Exact finite artifacts and attribution

The four free-port row lists and whole leading forms are IDENTICAL to the
sibling 67 equations. All four specialized constants differ. In particular
beta differs, so the selected coefficient -2^10 beta^162 in q1_bv differs;
the polynomials themselves are not identified. Counts/degrees remain
78/516,79/382,79/456,80/338. The finite checker independently covers every gate,
proves whole leading forms, checks liveness and counts, enforces one complete
binding across all charts, and rejects actual algebraic corruptions.
The rebuilder verifies every 3297 coefficient, every raw payload byte, all 51
retained target linear identities and the actual fixed controller associations.
Normal and optimized receipts agree. These supplement, not replace, the
unbounded proof and complete source calibration retained here.

Compared with the sibling's 295,388 raw bytes, the whole incoming tuple uses
207,214 raw bytes, a reduction of 88,174 bytes. The incoming native package owns
this coefficient improvement. We claim only its explicit checked composition
with the new four lower-Y charts. The original 67 component is unchanged.
No remote repository was modified and no new encoding was published.
