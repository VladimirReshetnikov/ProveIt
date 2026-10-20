# Reusing the witness-request subformula in K

## Mathematical result

This note isolates a calibrated alternative to K230's output-root schema. Its
purpose is to create more repeated compiler input. The selected reordered
variant now underlies the explicit 223-state candidate. The authoritative
final theory proof is `theory223.tex`; exact source binding is replayed by
`audit_ks223_emitter.py` and recorded in `ks223_emitter_audit.json`.

Work in classical first-order logic with genuine equality, a nonempty domain,
and a binary relation R. Matrices may have arbitrary finite parameter tuples q.
Write

    Sub(p,u) := forall z (R(z,p) -> R(z,u)),
    W_phi(p,C) := (exists y phi(y,p,q)) ->
                  exists y (phi(y,p,q) and R(y,C)),
    H_phi(C) := forall u (R(u,C) ->
                  ((exists p phi(u,p,q)) and
                   forall p (Sub(p,u) -> W_phi(p,C)))).

Let K_s consist of genuine equality axioms and the universal closures of

    forall a exists C (W_phi(a,C) and H_phi(C)).                 (K_s)

Then K_s is equiconsistent with StandardZFC. So is K_s plus irreflexivity.
The reductions are effective transformations of finite derivations and are
formalizable in ZFC. No new Rocq endpoint is claimed here.

### Upper consistency direction

Let K_o be the calibrated ordinary output-root theory:

    forall a,x exists C ((phi(x,a,q) -> R(x,C)) and H_phi(C)).

For a fixed phi,a, split classically on whether an output exists. If some x
satisfies phi(x,a,q), use the K_o witness for this x. Its root supplies an
output inside C, and its closure supplies H_phi(C). If no output exists,
the K_o witness for any x still supplies H_phi(C), and the request W is
vacuous. Thus K_o proves every K_s instance. This is precisely the
object-level argument of upstream `KPSeed.v`, theorem `output_root_to_seed`.

The upstream interpretation of K_o plus irreflexivity in constructible set
theory therefore proves

    Con(StandardZFC) -> Con(K_s + IR) -> Con(K_s).

This is a relative interpretation on finite proofs. It does not assert that
ZFC proves the existence of a set model of all of ZFC.

### Lower consistency direction

For each a the K_s witness C satisfies both support and the following request:

    forall p ((p=a or exists u (R(u,C) and Sub(p,u)))
              -> W_phi(p,C)).

In the first case transport W_phi(a,C) by genuine equality. In the second
case use H_phi(C) at u and then at p. These are exactly the requests and
support required by upstream `kp0 phi`. Thus every K0 axiom is a theorem
of K_s. This is the substance of `KPrimeCore.v`'s
`seeded_core_to_kp0`; the displayed ordinary formula merely chooses the
opposite, equivalent conjunction order in the selected witness.

The published lower consistency chain already factors through K0. More
specifically, `KQuotZFTransfer.v` proves `K0_ZFc_inconsistent`, and
`KQuotZFC.v` composes the Foundation/Choice relative-consistency translation
with that chain. Consequently

    StandardZFC |- contradiction  ==>  K0 |- contradiction
                                    ==>  K_s |- contradiction.

Adding IR to K_s preserves this implication. Together with the upper
direction this proves both equiconsistency statements.

Every new step uses a fixed finite first-order proof template for each input
matrix. It composes with the effective finite-proof translations in the
upstream development. This proves the intended internal formalizability; it
does not identify the metatheory of Rocq with ZFC.

## Why the alternative may compress

In native numerical syntax let I, Q, R be implication, universal quantification,
and membership constructors; let N(A)=I(A,1). As in K224, input a, output b,
and the actual matrix/private code c retain their literal roles. Define

    S = Q_c(I(R(c,a), R(c,b))),
    W = Q_b(I(c, N(Q_b(I(c, N(R(b,c))))))),
    U = Q_a(I(S,W)),
    H = Q_b(I(R(b,c), N(Q_a(I(c,N(U)))))).

After the same double-negation fusions as K224, the new core is

    K_s^f(a,b,c) = N(Q_c(I(W,N(H)))).

The old fused core is

    K_o^f(a,b,c) = N(Q_c(I(I(c,R(b,c)),N(H)))).

The new root replaces the short seed implication by the entire request W.
The same W already occurs inside H, including the same literal variable
labels and the same opaque matrix code. The longer formula therefore gives a
source compiler an opportunity to share a complete repeated program block.
The state cost depends on source bracketing and decoder-context sharing;
formula length and distinct formula-subterm counts do not answer it. The
selected final variant swaps the core conjunction to And(H,W), reorders the
bundle to And(V_R,And(H_R,core)), and fuses the negation of that final core.
Its exact bundle is

    N(I(V_R, I(H_R, Q(c, I(H, N(W)))))).

The successful source has 4,962 primitive occurrences, 209 distinct internal
subtrees, maximum depth37 and maximum zero run6. Its 77-macro formula emitter
has independent all-register source contracts. These are properties of the
selected source; they do not apply automatically to every seed variant.

The universal presentation of W used here,

    forall b (phi(b,a,q) -> exists b (phi(b,a,q) and R(b,C))),

is classically equivalent to the existential-premise definition above.

## Exact search material

`generate_formula_variants.py` writes 720 candidate arithmetic expressions and
postfix macro words to `formula_variants.json`. They vary:

- output-root, seed-request-root, and previously calibrated conditional root;
- the two orders of each of three conjunctions;
- all six orders of the core and two vacuity implications in the bundle;
- the equality-helper binder R(a,b), Q(a,b), E(a,b), I(a,b), or the old c.

Double-negation simplification is explicit. The unchanged default expression
and its entire 71-macro word are asserted equal to K224's exact emitter
contract, providing a concrete reference point for the search. This assertion
is an input-binding check, not a consistency proof for the other expressions.

The optimized arithmetic macro trees are in `macro_data.json`. Their default
concatenated leaf instructions match the exact 4,799-leaf source at interval
[2541,4618). The smallest containing closed source subtree has path
`11101001001110`, global starting leaf 648, and 4,004 leaves. Cutting that
subtree at local offsets 1,893 and 3,970 gives six closed prefix blocks, the
formula block, and two closed suffix blocks. This permits an independent
grammar search on the complete closed emitter region.

## Native-machine obligations

The ordinary K_s theorem alone is not a certificate for a new transition
table. A promoted K_s machine must additionally establish:

1. Exact symbolic binding between its emitted arithmetic expression and the
   claimed schema, including the unchanged `c!=a,b` gate and `m=k=c` identity.
2. Both directions of the native numerical-calculus consistency comparison,
   including exceptional low codes and coincident active labels. In the lower
   direction the existing equality interpretation is performed before the
   actual padded matrix/private code is chosen, exactly as in K224.
3. Correct enumeration from the actual nonzero seed and the proof cutoff.
4. Complete source-to-binary runtime simulation, exact blank startup, and the
   correctness of every retained context-dependent decoder sharing.

Conjunction permutations and double-negation cancellations are numerical
logical equivalences in the retained core. The change from K_o to K_s is a
calibrated theory change; it should not be described as an equality of native
codes or as a mere register-program reassociation.

## Sources and attribution

Elliot Glazer's K theory, K0 quotient construction, and consistency proofs are
the mathematical starting point. The primary source is `elliotglazer/k230-rocq`
at commit `3142e4dd980f0be12f4abb636c4ae2528afc17eb`, particularly:

- `coq/settheory/KPSeed.v`;
- `coq/settheory/KPrimeCore.v`;
- `coq/settheory/KQuotZFTransfer.v`;
- `coq/settheory/KQuotZFC.v`;
- `coq/settheory/KUpperConsistency.v`.

The seed form and its logical reduction already occur in that proof. The
research proposal here is to use the repeated request as actual source input
for compression. No novelty claim is made for the seed theory itself.
