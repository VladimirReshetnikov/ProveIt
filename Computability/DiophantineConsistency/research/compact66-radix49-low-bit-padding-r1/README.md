# R1: corrected actual-factor calibration for radix49 low-bit padding

CODE-FREE CONDITIONAL ORDINARY PROPOSAL. The complete original proof is
retained below, with its sole closing factor assertion corrected under
the separate ROOT authority committed as
`db4b5f21dd7421bd33fa6c37682af125514e4b44`.

The original three-file proposal remains immutable at
`976c27a14f32c618103c7e14ec179faf89cdbfa1`, manifest
`92d4bdc3d816687386f69e3ad305e22632b9a9ae8459931ed5d21f50fa19b0c5`.
Its complete first independent review, preserved at
`5de0b3843c4c1f6a76265446e43a0f7657ac1332`, is **FAIL_AS_WRITTEN**
with finding F1: the literal printed strong factor is Delta, not one.
That finding is a code-free calibration-prose error; no application
failure or runtime capture occurred or is relabeled here.

The bounded R1 edit is by `/root/intake_e13`. In section6 it now states
explicitly that S^2=Delta*(f^2-1), Ns=Delta and
N0=N1=Na=Nk=Nt=1. Their actual product is Delta, so the unchanged
P66 equals0. No normalized strong factor is silently substituted for
Ns. Every other original proof-body byte is retained. No constant,
mask, rank, native argument, witness construction, equation, kernel or
finite controller condition is changed. All32 original direct source
records and three whole parent inventories are retained, with the entire
original source and first finding pair bound additionally in SOURCE_PINS.

The original title and authorship statements in the retained body identify
ROOT's original proposal and historical self-read. They are not an
independent approval of R1. The R1 author's complete readback and inert
byte authentication likewise are not an independent approval. Two FULL
independent ordinary reviews and separate ROOT conditional acceptance
remain necessary on this new final seal.

No candidate, mathematical helper, evaluation, import, AST, compiler,
coefficient/residue/prime/Pell calculation, Lean, TeX or PDF process has
run in this R1 preparation. The original proposal, first reports, held
49 probe, parents, maintained artifacts and Lean are unchanged. All
finite controller premises remain conditional; no tuple, endpoint,
measured source/glyph/PDF gain, page promotion or runtime authority is
supplied. No commit is made by the R1 author.

The complete retained proof follows.

---

# Low-bit partial padding for the shared-marker radix49 equation

CODE-FREE CONDITIONAL ORDINARY PROPOSAL, authored by ROOT. This changes
one fixed high mask of the accepted conditional shared-marker49 adapter.
The whole polynomial is still P66, with fifteen positive unknowns,
66 operations and degree157. The new complete coefficient tuple is a
new specialization; no identity with the preceding specialized polynomial
or pointwise transport of its private witnesses is claimed.

The change permits a shorter telescoped spelling. This note proves the
full ordinary adapter conditional on exactly the same finite controller
conditions as the parent. It supplies no measured source/glyph/PDF gain,
numerical tuple, accepted controller or page promotion. No application,
mathematical helper, import, AST, compiler, coefficient/residue/prime/Pell
calculation, Lean, TeX or PDF process has run for this proposal. Frozen
parents, the separate49 probe, maintained page and Lean remain untouched.

## 1. Exact retained data and all four new ports

The complete finite language is the parent's ordered943 tiles,430 actions,
436-character seed,62-character alphabet and closed decoder/table. In
particular Start0=(2,435,3,1), Forbidden1=(5,0,0,0) and the corrected
initializer929=(3,436,4,4) are retained, with no permutation or conjugacy
change. For each tile put

    u_i=w_i+2^8*n_i+2^17*p_i+2^25*s_i in[0,2^34),
    c_i=1+2^10*(2^34-u_i), 0<=i<=942.

Set L=8807,rho=2^49,d=49L,B=rho^L,beta=B-1,mu=2^47-2 and

    E={0..942} union{983..992} union{1003..1011}
      union{1013..1031} union{1063,1064,1095,2195,3296},
    M_mark={992,1011,1022,1031,1095,2195,3296}.

All3297 coefficients, including every zero, are fixed by the selector
formula above and

    c_(1023+j)=2^(10+j), c_(1003+j)=2^(27+j), j=0..7;
    c_(1013+j)=2^(18+j), c_(983+j)=2^(35+j), j=0..8;
    c_e=2^44 for e in M_mark; every unlisted coefficient is0.

Thus the two coefficient-zero dummies remain1063/1064. There are986
allowed positions and984 nonzero coefficients. Put

    Phi(x)=sum_(e=0)^3296 c_e*x^e, G_m(x)=sum_(j=0)^(m-1)x^j,
    Lambda=rho^4393+rho^5495,
    DC=rho^30+rho^62+rho^1100+rho^2201
       +sum_(e in E)c_e*(rho^(4393-e)+rho^(5495-e)),
    DR=rho^42, K0=DC+B*DR,
    MC=beta-sum_(e in E,e!=1)rho^e-2*rho^1063,
    Ccore=rho^1013*G_10(rho)+rho^1065*G_9(rho)
          +rho^2195+rho^3296.

The ONLY changed port is defined through the nonnegative expansion

    Zlo=(rho-1)*rho^8792*G_15(rho)
        +(rho-1)*rho^7691*G_2(rho)+(2^39-1)*rho^7693,
    MFlo_native=4+mu*Lambda+Ccore+Zlo,
    MFlo_source=MFlo_native+beta.

The complete tuple is(beta,K0,MC,MFlo_source), with beta added exactly
once. Phi,DC,DR,K0,MC,beta are literally identical to the conditional49
parent; none is imported from old53/55 as a new numerical premise.
In particular the complete same K spelling is

    K0=rho^30+rho^62+rho^1100+rho^2201+rho^8849+Lambda*Phi(1/rho).

The apparent reciprocal is integral because4393-3296=1097>0.
The same support-decoded spelling of MC is exact since every c_e<rho.
The full control polynomial remains

    2^10*x^1003*(x^20+2^17)*G_8(2x)
    +2^18*x^983*(x^30+2^17)*G_9(2x)
    +2^44*[x^992*(1+x^19+x^30+x^39)
            +x^1095*(1+x^1100+x^2201)].

All limits and every exponent are fixed constants, independent of any
witness, native dimension or future controller prime.

## 2. Exact cancellation, population and scalar boxes

The two geometric telescopes give

    (rho-1)*rho^8792*G_15(rho)=B-rho^8792,
    (rho-1)*rho^7691*G_2(rho)=rho^7693-rho^7691.

The latter cancels the minus-one part of the new partial coefficient.
Consequently the ENTIRE changed compressed mask is

    Zlo=B-rho^8792+2^39*rho^7693-rho^7691,
    MFlo_source=2B+3+mu*Lambda+Ccore-rho^8792
                +2^39*rho^7693-rho^7691.

These expressions denote the preceding positive expansion; their minus
terms do not represent negative mask digits. The parent used39 bits2..40
at7693. Here the same39 ones occupy bits0..38 of that field. These
fields and all active masks are disjoint; no population is lost or added.
The padding count is still15*49+2*49+39=872. The two mu fields have
46 ones each and Ccore plus the unit4 contributes22. Therefore

    pc(MFlo_native)=986, pc(MC)=d-986,
    MC=2 mod4, MFlo_native=4 mod8.

The partial coefficient2^39-1 is positive and below rho. The high mask
has the same fifteen full top fields, while field8791 is still0; hence
0<MFlo_native<beta and beta<MFlo_source<2beta. The existing MC box
0<MC<beta, beta odd>=31 and K0>0 are unchanged. Nothing at the origin
or a low residue is changed by moving bits in field7693.

For J=1+B+...+B^(N-1), repeated masks remain disjoint B-blocks.
MC*J+1 changes10 to11 at the origin and MFlo_native*J-1 changes100
to011. Their populations remain(d-986)N+1 and986N+1. Thus the same
uniform positive-source/population recovery applies to these NEW ports:
q=B^N, C,F>0, F+C<q, 0<F<q-1, and

    (C-1) AND(MC*J+1)=0,
    F AND(MFlo_native*J-1)=0.                         (1)

Its hypotheses are the just-proved boxes, residues and populations;
this is not an application of the parent's final theorem to old MF.

## 3. Full native soundness

The low mask is unchanged, so the Boolean fields, possible0..3 dummy,
origin Start and globally excluded selector1 are exactly as in the parent.
Transport is unchanged because K0 and the actual q,C,F,w relation are
unchanged. The support identities, entire predecoded cyclic carry bound24,
clean-clause bootstrap, decoded carry bound3 and all49 fractional phases
therefore apply without amendment. Their hypotheses use the low mask,
transport and the active tested high fields; all those high fields are
literal in MFlo_native with their original coefficients.

In particular the two mu clauses,19 copy tests and two anchor tests are
retained, with no additional active test removed. The local counting lemma
recovers one selector at most, all34 variable label bits and each of the
seven physical markers. The reset/phase proof forces a whole-B-cell
rotation and all aligned copy/clause equations. Start occupancy propagates
around the spatial cycle and typed labels match. The temporal stride is
nonzero. The complete retained marked Wang-language/state-color/native
contract gives the blank K215 computation and finite syntactic refutation.
No padding-only implication is substituted for any active decoding step.

For the outer source implication use the exact P66 formula in section6.
Its sign/rank proof, including weak C>=0 and unresolved coupled Nk=Nt
signs until main/strong/auxiliary recovery, requires only the uniform
scalar boxes and populations proved in section2. It yields the same
actual-rank and mask interface(1), before native decoding. Thus no new
unit premise or controller is needed for soundness.

## 4. Completeness: every padding bit and every dummy subset

Take the parent's independently cofinal canonical one-Start tiling and
encode it freshly at rho. Initially all dummy bits are0; any simultaneous
Boolean subset of safe low1063 bits is permitted. Neither Phi nor K0
changes. The full carry fixed point, decoded bound3,49-phase argument,
copy tests, clauses and anchors apply to each such word.

The exact raw predecessor resets are still c_0*x_2195 at7690 and
c_0*x_3296 at8791, each below rho-3. The complete fields7691..7695
and8792..8806 have no formal contributions, temporal input or outgoing
carry after these resets. Thus the WHOLE field7693 is0 under EVERY
simultaneous dummy subset. This is the reason low bits0..38 can be
used there; a proof merely about the parent's tested bits2..40 would
not suffice. Both full lower fields7691/7692 and all fifteen top fields
also remain0, so the ENTIRE new padding mask passes. At the unit field,
no part of the changed distant padding affects the same shifted-origin
tests. Low mask, active high tests and complete(1) all hold.

With t=dN,q=2^t and M=q^2, all words obey the SAME strict bounds

    0<F<q/rho^15, 0<C<q/rho^5510, 2C+F<q/3,
    alpha=q-F-C>0.

These bounds follow from the full zero tail, independent of which bits
of7693 are tested. No supplied F is silently changed or divided.

## 5. Fresh actual rank and the unchanged conditional controller

Define the NEW ACTUAL rank, not a selected target, by

    Rlo=[q(q-F)-C]*(q^2-1)+(MC+q*MFlo_source)*J.

Put S'=(C-1)+qF and Tlo=(MC*J+1)+q*(MFlo_native*J-1).
The two disjoint binary packing blocks give exactly

    Rlo=(M-1-S')*M+(S'+Tlo), pc(Rlo)=3t+2,
    Rlo=3 mod4.

The count uses pc(Tlo)=t+2 and S' AND Tlo=0 from(1). Origin residues
C=1 mod4,F=0 mod4,J=1 mod4 are unchanged on these canonical words.
For the same C,F,q,J the old rank would differ by

    Rlo-Rold=-3*q*J*(2^39-1)*rho^7693.

This identity is not an assertion of equal ranks, binary populations for
unmasked words, equal w, or equal private Pell tuples. Fresh tuning is
required even though K0 is unchanged.

The unresolved finite assumptions are EXACTLY the parent's: an odd prime
lambda>d with1887 dividing kappa=lambda-1, B^2!=1 modlambda,
v_lambda(B^kappa-1)=1 and Hctrl=1+B*K0+B^2 nonzero modulo7,8807,
lambda. The full known orders are3 modulo49 and629 modulo8807.
They imply B^kappa=1 modulo FULL49L. No prime/unit is evaluated here.
Because all these conditions depend on beta,K0 and rho, changing only
MF preserves their literal meaning. Results of the separately prepared
old49 probe, if later released, can concern those very same finite
conditions; no probe result currently exists or is assumed.

For fresh width=lambda^r_w,height=lambda^r_h,N=lambda^(r_w+r_h),
choose the independent exponents sufficiently large as in the parent.
Every simultaneous dummy subset preserves(1) and the strict bounds.
A safe low1063 flip has the same exact ORDINARY increment

    deltaF=(K0+B^width)*rho^1063*B^j,
    deltaRlo=-Gamma*B^j,
    Gamma=rho^1063*(q^2-1)*[1+q*(K0+B^width)].

Indeed the difference of the new rank cancels its constant MFlo term;
the no-wrap proof uses the unchanged convolution and full zero tail.
Gamma is a unit modulo dN, including7^2, under the stated premises.
The same complete CRT/LTE Boolean-subset construction therefore tunes
Rlo=d*width moddN for the NEW initial actual rank. All masks, active
labels, padding, origin, slack and each physical dimension stay valid.
The same lower rank bound makes w=2^(Rlo-t)>B^width positive, and
w=B^width mod(q-1). The fresh positive integral z then satisfies Nt=1.
No old rank or old private witness is reused pointwise.

## 6. Complete P66 calibration and both positive witness maps

Use exactly fifteen positive unknowns
J,F,alpha,z,f,h,i,T,s,w,tau,eta,zeta,y,gamma and the four NEW ports.
Every other symbol below is a polynomial abbreviation:

    q_-=beta*J, q=q_-+1, C=q-F-alpha, X=w*q, Y=s*q^3,
    Eprod=X*Y, k=eta+zeta, ell=Eprod*k*Y, c=k*Y+eta,
    a=Eprod+Y, H=4*a+3, Delta=a^2+H, D=X+a*c+gamma*H,
    R=[q_-*(q-F)+alpha]*(q^2-1)+(MC+q*MFlo_source)*J,
    V=f^2*(c*T-R)-c, S=i*Delta*c^2,
    N0=tau^2-ell*(ell+k), N1=D^2-Delta*c^2,
    Na=S^2*(V^2-y^2)+y^2, Nk=k-h*Eprod-R,
    Nt=(K0+w)*C+(q-F)-z*q_-, Ns=Delta*f^2-S^2,
    P66=N0*N1*Na*Nk*Nt*Ns-Delta.

Soundness uses the full retained uniform positive proof, as in section3.
The quotient bridge is T_old=f*T>0, with all other inputs and all four
current ports held fixed; equivalently i_ordinary=Delta*i for the
ordinary strong-norm bridge. These do not divide an arbitrary witness.
The masks(1), active native decoding and refutation implication were
proved for the exact NEW ports above.

Conversely section5 supplies fresh native words, actual rank and w.
The same uniform half-binomial/ratio converse applies to R=Rlo:
R=3 mod4,pc(R)=3t+2,3q+1<=R<q^4,q>=16. It constructs fresh
positive X=2^R,Y=s*q^3,k,c,tau,h,eta,zeta,gamma with odd s.
Since d,N are odd, both w=2^(R-t) and the proof-only symmetric scale
2^(R-3t) are positive integer squares; no fourth-power condition is
introduced. For A=a+2, take m=cR,f=chi_A(m),i=psi_A(m)/c^2.
The retained odd-index divisibility and recurrence give integral odd i
and f^2=1+Delta*i^2*c^4. Put S=i*Delta*c^2 and construct freshly

    Vstar=chi_S(R)/S, ystar=psi_S(R),
    Tstar=(Vstar+c+R*f^2)/(c*f^2).

The odd-index identities give Vstar integral, Vstar=-c modf^2 and
Vstar=-R modc. With gcd(c,f)=1 and f^2=1 modc, Tstar is a positive
integer, Vstar=f^2*(c*Tstar-R)-c, and the Pell norm gives Na=1.
Since S^2=Delta*(f^2-1), the ACTUAL printed strong factor is
Ns=Delta*f^2-S^2=Delta. The fresh construction has
N0=N1=Na=Nk=Nt=1, so N0*N1*Na*Nk*Nt*Ns=Delta and P66=0.
This is the same whole arithmetic converse at a newly constructed actual
rank; it is not an isolated auxiliary norm identity or an old specialized
solution map.

The literal free-port graph remains66 live operations with degree157,
factor degrees22,18,62,7,2,46 and nonzero selected coefficient8*beta^92.
This is an ordinary uniform symbolic statement, not a new finite source,
degree/liveness run or emit. Together with the unchanged complete
syntactic-refutation/foundational contracts, it gives the intended
ZFC-provable unsolvability iff Con(ZFC), CONDITIONAL on the displayed
finite controller premises. No new internal-ZFC, unbounded compiler,
native-program or Lean proof is claimed.

## 7. Scope, prior art and next obligations

The accepted49 parent moved and counted seven marker weights; that
mathematical change is retained. The present change ONLY relocates39
already counted padding bits inside an entirely zero field, allowing
a telescoping cancellation. It is distinct from support simplifications,
selector-prefix cancellation, seed compression and the optional separate
kernel-unit modification, which is NOT assumed or included here.

The complete49 proof and both full ordinary reports plus separate
acceptance are pinned directly. Its prior exact catalogue and three
closed parents remain retained ordinary provenance, not a newly executed
compiler/kernel verification. Author ROOT has read this entire note and
the relevant parent text and authenticated the full direct sources.
Independent full ordinary review and separate acceptance are required.

A future complete equation page must print every language/seed/table/
constant, materialize and check the coherent tuple, audit every source
and actual-PDF binding, retain both ordinary reviews and actual visual
checks, and compare the complete page before any maintained update.
No numerical size/glyph gain or shortened page follows merely from
having a shorter algebraic substring in this note. No execution authority
for this proposal or the separate held probe is conferred here.
