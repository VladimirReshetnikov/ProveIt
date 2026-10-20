# Exact conditional-K source used by the 223-state candidate

## Result and boundary of this certificate

The source file with SHA-256
`b4e453a8801597124fd9b3ee1cd2db1cdf80c0bd904c2ffb59b79d95e91a6e96`
emits the conditional-K numerical calculus described below. This calculus is
equiconsistent with StandardZFC by composition of the retained conditional-K
interpretation and the retained restricted-equality-helper interpretation.
The source changes no logical row, gate, command, parameter parser, or stack-slot
count. Its complete structured register-program CFG equals the literal emitter
for that calculus.

These are the source and logical layers. The binary transition-table build,
local state fold, universal runtime simulation, and blank-tape initialization
have separate candidate-specific certificates. This note does not assert a new
compiled Rocq endpoint for the conditional interpretation.

## 1. Literal formula family

Use native constructors I, Q, R, E and relative falsity F=1. Let N(A)=I(A,F),
And(A,B)=N(I(A,N(B))), and Ex_x(A)=N(Q_x(N(A))). The private binder and opaque
matrix are both the original numeric parameter c; no recoding is performed by
the emitter. Define

    S = Q_c I(R(c,a),R(c,b))
    W = Q_b I(c, N(Q_b I(c,N(R(b,c)))))
    U = Q_a I(S,W)
    H = Q_b I(R(b,c), N(Q_a I(c,N(U))))
    Kc = I(c, N(Q_c I(R(b,c),N(H))))
    VR = I(R(a,b),Q_c R(a,b))
    VE = I(E(a,b),Q_{Rcode(a,b)} E(a,b))
    Bc = N(I(Kc,I(VR,N(VE))))

The returned current formula is 0 when c=a or c=b and Bc otherwise. All eight
old logical rows, in their original order, and the GEN/cache/stack operations
are unchanged. Rcode(a,b)=4P(a,b)+1 is strictly greater than both endpoints.

The unfused conditional core is

    I(c, Ex_c And(R(b,c),
      Q_b I(R(b,c), Ex_a And(c,
        Q_a I(S, Q_b I(c,Ex_b And(c,R(b,c)))))))).

The fresh certificate `conditional_fusion_certificate.json` derives both
directions between its bundle And(Kc_unfused,And(VR,VE)) and Bc. It has 1,611
closed proof nodes and 1,724 formula nodes. Its only leaves are the retained
K/S/Peirce derived schemas and literal rho2/rho6; its only inference rules are
MP and theorem GEN. The independent checker rejects changed endpoints, broken
MP, and hypothesis leaves. This derivation assumes no freshness or distinctness
and treats its matrix as an opaque formula parameter. Thus its substitution
k=m=c is uniform for all natural values, including a=b and codes 0 and 1.

## 2. Exact source binding

The certified K224 baseline source is pinned by SHA-256
`309358206463f8e8d88d86304e7c9f2273e3cdde64984b6db20c412516010878`.
The bundle occupies global instruction ordinals [2541,4618), equivalently local
ordinals [1893,3970) in subtree `11101001001110`. The verifier first checks that
this baseline interval is exactly the old, fully fused unconditional emitter.
It then builds the conditional emitter from the same pinned primitive macro
contracts and the literal formulas above.

`verify_conditional_source.py` imports no source generator, allocator, or search
module. It checks every instruction and every control-flow successor against
that literal emitter, verifies that the candidate is unchanged outside the
declared subtree, and binds both independently checked Hilbert endpoints.
The candidate has 4,799 instruction occurrences. Its normalized instruction CFG
has SHA-256
`e182dc627be6e746c4c12639cc93a89c21256f87bddc7c5bc715c7776d92f04c`.

The unchanged 34-instruction gate suffix is part of this exact comparison.
The prefix still supplies the eight old logical rows and the same parsed roles.
There is no assumption that a source DAG count equals a binary working-state
count.

## 3. Upper consistency direction, including the edge cases

In the retained ordinary interpretation, an enabled unconditional K core gives

    Ex_c And(I(m,R(b,c)),H) -> I(m,Ex_c And(R(b,c),H)).

Here c is free-variable-fresh in the decoded matrix. This implication needs no
distinctness of a and b: if m is true, retain the old container witness; if m is
false, the conditional conclusion is true. The upstream theorem
`KDecodeFresh.D_private_fresh` supplies freshness for EVERY numeric matrix code.
Specifically, code 0 decodes to the closed tautology

    (All_0 Eq(0,0)) -> (All_0 Eq(0,0)),

and code 1 decodes to R(0,0), which is false under IR. No low code is replaced
silently by a separately chosen matrix. If c equals either endpoint, the old
source gate returns the truth code 0 before the AX command returns.

Membership vacuity retains its original enabled side conditions. The Rel-code
helper is valid in ordinary equality because its binder exceeds both endpoints.
The old logical rows retain their original soundness proofs. Combining these
facts with the closed fusion equivalence establishes soundness of every actual
emitted formula in the same ZFC upper interpretation. The unconditional source
already has the required coincident-role interpretation, so this direction does
not reinterpret an a=b source instance as a distinct-variable schema instance.

## 4. Lower consistency direction and actual-code coupling

The retained ordinary conditional-K+IR theorem has the consistency strength of
unconditional K+IR, and hence StandardZFC. Its two-marker hereditary-domain
interpretation supplies a definable empty object; it does not assert that raw
conditional K alone proves an empty object. This is precisely the root used
above, with the same support-and-subset-closure formula H.

The restricted equality-helper theorem explicitly covers this conditional root.
It translates primitive equality to two-sided membership indiscernibility E,
using the actual Rel-code helper, membership vacuity, the eight old logical rows,
MP and GEN. It does not assume full primitive equality vacuity or use a
symmetry-only shortcut.

For an ordinary finite matrix f choose the retained safe active names input1,
output3, with its other names assigned as in the retained named-formula encoding.
First form its logical interpretation psi=theta(f), THEN form the double-negated
matrix pp=not not psi, and choose c=enc(pp). Padding gives c>3 and the code-label
bound makes c absent from psi. Choose the ordinary comparison instance's private
name to be this c. Since the conditional template outside its matrix contains
only membership and logical constructors, it commutes literally with theta.
Its interpreted matrix has actual native code c. Therefore its numerical
instance is exactly the source instance at (a,b,c)=(1,3,c), whose gate is enabled.
Bundle projection and the fresh fusion theorem supply that instance.

This order of operations is essential: one must not choose c from f first and
then assume equality translation preserves that numeric code. The retained
finite-proof interpretation supplies the translated logical axioms, the
translated IR theorem, and every selected conditional K instance. Thus a finite
StandardZFC refutation yields a numerical derivation of F=1. Together with the
upper direction this identifies the numerical calculus's consistency strength.
The source binding and the fusion theorem cover all triples; only the lower
calibration deliberately selects safe distinct triples.

## 5. Proof enumeration remains the same

AX still pushes ten entries above its old stack, including its old current
formula, and leaves the gated bundle current. Every new current bundle is either
0 or N(X)=4P(X,1), so it is never code1. All other pushed formulas are unchanged.
Consequently the old DISCARD, logical-leaf, GEN, MP, and bundle-leaf block lengths
are unchanged, including DISCARD's NIP^10 and the logical-leaf cleanup NIP^(11-j).

The command parser still consumes exactly four AX fields. The retained cofinal
reset family START_U=AX(0,1,1,U) still resets the additive counter and cache.
Its argument that Build_F accepts arbitrary current/stack codes is unchanged.
Thus the initializer's nonzero proof cutoff is handled by the same explicit
unbounded candidate numbers P(3,P(1,P(1,P(U,R)))). No new proof-list encoding or
padding assumption is introduced.

## Pinned mathematical inputs

The K224 package's `portable/theory/` files are unchanged inputs:

- `conditional_k_calibration.md`: SHA-256
  `3e7ab7f2fcf2f68d7bff68743771160827907a488330de27779245c728083ed4`
- `k_equality_helper_extension.md`: SHA-256
  `880abc28bd2d13f584bdf24c04d0769f84c46a4e698da9e87b003f66b47510ff`
- `enumerator_adaptation.md`: SHA-256
  `13ff2367e645c49096354a139ee9d51491da5693799df26e68275c43770fb668`
- Actual Rel-helper finite certificate `rel_helper_certificate.json`: SHA-256
  `3cba11f96eb71dcaeac32b69e662aa640d7728e18fd8b3b995e709555119c23b`

The source contracts and decoder freshness theorems come from the retained
Elliot Glazer K230 proof provider, commit
`3142e4dd980f0be12f4abb636c4ae2528afc17eb`, and the already certified K224 source
transport. Their verification remains part of the parent packet's pinned chain.
