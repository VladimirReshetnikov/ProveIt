# A quartic consistency equation in 45 unrestricted integer variables

## 1. Source and result

The source is package 34's 50-integer, 29-quadratic-residual system,
`Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/low_degree/quartic50.json`,
at ProveIt commit `4b4349064a750ba6347293b55874a7f92abdd0db`.
The active coefficient tuple is package 34's complete
`mixed-parity-unrounded-1064921` tuple, not the historical tuple mentioned
inside the inherited source proof. Its radix is B=2^1064921. The four
ports are beta=B-1, K0, MC and the already shifted MF_source. All four must
be bound together. The original polynomial is retained as source data.

The new packet `quartic45.json` contains all 45 unrestricted integer
unknowns and all 28 quadratic residuals. Their sum of squares is an
ordinary quartic polynomial. Its tau^4 coefficient is 1, so the total
degree is exactly four on the fixed coefficient slice.

The construction saves five integer variables. It does not improve the
nine-natural/positive or ten-unrestricted-integer high-degree counts.
No global minimum is asserted.

## 2. Two guard principles

Write Pos(u,v,t)=1+u^2+v^2+t(t+1). This is always a positive integer and
represents every positive integer by Legendre's three-square theorem:
represent 4n-3 as three squares, one odd and two even, then divide by 4.
Here 4n-3 is 1 modulo 4 and therefore is not of the excluded form
4^a(8b+7).

**Common-sign lemma.** If q>0, C=q-F-alpha, F alpha>0 and F C>0, then
F, alpha and C are positive. Indeed both positive products make these
three nonzero integers have the same sign, and their sum is q>0. Conversely
F,alpha,C>0 make both products positive. Thus the two quadratic equations

    F alpha = Pos(FA1,FA2,FA3),
    F(q-F-alpha) = Pos(FC1,FC2,FC3)

encode the open three-coordinate simplex without separate positivity
parameters for all three coordinates.

**Dyadic guard lemma.** If beta>=3 and integers J,v satisfy

    beta J+1 = 2v^2,

then J>0. If J<=-1 the left side is negative, and if J=0 it is 1, which
cannot equal twice a square. Conversely the compiler's canonical radix
q=2^t with t odd has this representation with v=2^((t-1)/2).

The canonical oddness of t is already proved for the active tuple in
package 34's `coefficients/COEFFICIENT_PROOF.md`, section beginning
"All d,w_c,h_c,N are odd". It is also a hypothesis explicitly used by
the inherited quartic50 source's odd-scale completeness argument.

## 3. Exact change of residuals

Keep the source's first 23 arithmetic residuals unchanged. Keep the
ternary positivity equations for eta and zeta. Delete the four positivity
equations for J,F,alpha,z and their twelve private variables. Add seven
variables: q_half_root and the two triples for FA and FC. Add the three
quadratic equations in Section 2. Hence

    50 - 12 + 7 = 45 variables,
    29 - 4 + 3 = 28 residuals.

This changes the existential solution predicate, not merely the spelling
of one polynomial. Soundness and completeness must therefore be proved.

## 4. Soundness: the transport quotient need not be guarded early

Take an integer zero of the new quartic. The sum of squares forces all
28 residuals to vanish. The dyadic guard gives J>0 and q=beta J+1>=16.
The common-sign lemma gives F>0, alpha>0 and C=q-F-alpha>0. The unchanged
guards give eta,zeta>0. The source's odd substitutions still give
i=2r+1 and s=2v_scale+1; w=u^2 is retained.

The only initially missing source guard is z>0. We cannot invoke the
whole source theorem before restoring it. Instead inspect the order of
the source Pell recovery argument. The coordinate z appears only in
the transport equation. Its positivity is used initially only to infer
C>=0 (strict C>0 in the shifted system). We have already obtained C>0
independently, so that initial use of transport is unnecessary.

More explicitly, define the same source abbreviations

    X=wq, Y=sq^3, E=XY, k=eta+zeta,
    c=kY+eta, a=(X+1)Y, H=4a+3,
    Delta=(a+2)^2-1, D=X+ac+gamma H.

The retained equations assert the first and main Pell norms, the ordinary
strong equation, and the auxiliary norm exactly, together with

    k=R+1+hE,
    V=of-c=jc-R,
    R=((q-1)(q-F)+alpha)(q^2-1)+(MC+q MF)J.

These identities follow from the unchanged quadratic lift exactly as in
the source quartic50 proof. Its exposed-quotient argument uses the two
displayed V congruences; it does not assume an unchecked quotient.

With q>0, F>0, alpha>0 and C>0, the original packing bounds follow
directly, without any sign assumption on z:

    q(q^2-1)<R<q^4-2, R-2>3q+1.

The unchanged zero-square-scale exclusion gives w>0, hence X>=q and
|E|>=q^4>R+2. The negative-odd-scale argument then excludes s<0 using
only these bounds, the Pell equations, eta,zeta>0 and the two exposed
V congruences. Thus s>0. No occurrence of z enters that argument after
the original preliminary C>=0 step.

The positive-scale signed recovery now applies in its same proof order:
Pell classification and the ordinary strong-rank lemma give the main
index p=R; the short index interval fixes the first Pell index; the
signed-gamma argument selects the positive main root; and the congruence
and strict interval yield

    X=2^R.

The proofs used here are the inherited `ODD_SCALE_27_PROOF.md`, Sections
1--4, and `SIGNED_DOMAIN_29.md`, "Soundness of the wider domain" through
"Signed gamma", with the ordinary-strong paragraph. Their only use of
the original z>0 hypothesis before X=2^R was to establish C>=0. Every
remaining use of transport can be deferred because C>0 is now an
independent consequence of the two new guards.

Finally R>3q implies 2^R>q^2, so w=X/q>q>F. The unchanged unshifted
transport equation is exactly

    (K0+w)C=(z-1)(q-1)+F.

Since K0>=0, C>=1 and w>F, its left side exceeds F. Hence
(z-1)(q-1)>0, and q-1>0 gives z>1. We have now recovered the original
z>0 guard. All six original guarded coordinates are positive. Supply
their ternary positive representations to obtain a zero of the original
50-variable quartic. Its inherited compiler/calibration theorem yields
a finite ZFC refutation.

This order is essential: z is restored after Pell recovery, rather than
presumed positive while invoking a theorem that needs it.

## 5. Completeness

If ZFC has a refutation, use the source's canonical accepting arithmetic
witnesses with its unchanged complete tuple. They have q=2^t, t odd,
F>0, alpha>0, C>0. Put q_half_root=2^((t-1)/2). Represent F alpha and
F C by Pos, and retain the original eta,zeta guards and all arithmetic
variables. All 28 new residuals vanish. This proves existence in the new
system. No coefficient depends on whether a refutation exists.

Combining soundness and completeness with the source's ordinary
calibration argument gives, formalizably in ZFC,

    no integer zero of Q45  iff  Con(ZFC).

The claim uses inherited arithmetic, native-window and K215 calibration
theorems. This note supplies no new end-to-end Lean/Rocq proof and no
exported object-language ZFC derivation.

## 6. Reproducible finite checks

`python3 build_verify.py` uses only the Python standard library. It reads
the source packet as data, emits the new packet, expands the sum of squares
in exact sparse arithmetic with the ports left symbolic, checks all
variable counts and liveness, and proves exact degree using tau^4. It also
runs finite sign/radix diagnostics; those diagnostics are not substitutes
for the universal elementary proofs in Section 2.
