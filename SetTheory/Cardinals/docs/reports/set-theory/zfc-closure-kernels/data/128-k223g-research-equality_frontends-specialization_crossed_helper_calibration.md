# Universal self-specialization plus crossed equality vacuity

## Exact source proposal

Retain the unchanged original rho8 and rho1--rho6 rows, modus ponens,
closed-theorem generalization, the original K core, the original gate, and
the full gated membership-vacuity family. Replace the rho7 row by

\[
 T(i,A):\quad \forall_i A\longrightarrow A,
\]

for every numerical label `i` and every numerical formula code `A`.
Replace the equality-helper component of the gated K bundle by

\[
 C_1(a,b,c):\quad
 \operatorname{Eq}(a,b)\longrightarrow\forall_c\operatorname{Eq}(b,a),
 \qquad c\notin\{a,b\}.
\]

The point of the replacement is that `T` is a particularly short formula
constructor row, while `C1` uses the already available gate binder `c`.
The syntactic size or expanded instruction count does not by itself prove
a state improvement; the actual shared-source compilation must be counted.

Every `T(i,A)` is valid under the original ordinary first-order
interpretation. It is universal specialization to the same variable,
with no substitution or capture issue. This remains true for the truth
code 0, for the exact bottom `F=Rel(0,0)=1`, for formulas with `i` free, and
for formulas with internal quantifiers. No formula-recognition test is
added: the original decoder assigns meanings to all natural codes.

## Tiny derivations of symmetry and full equality vacuity

Fix any `a,b`, and choose `c` distinct from both. Put
`e=Eq(a,b)` and `f=Eq(b,a)`. Then

\[
 e\longrightarrow\forall_c f\longrightarrow f. \tag{1}
\]

The first implication is `C1(a,b,c)` and the second is `T(c,f)`.
Classical propositional composition therefore gives primitive equality
symmetry `e -> f`. For the diagonal this could instead be taken as
propositional identity, but the displayed derivation also works.

Now use the reversed crossed helper at the **same binder**:

\[
 e\longrightarrow f\longrightarrow\forall_c e. \tag{2}
\]

The final implication is `C1(b,a,c)`, whose gate is the identical
condition. Thus the new source derives every ordinary gated primitive
equality-vacuity instance, not merely one canonical instance.

Both arguments are finite closed theorem proofs. They use only `C1`, `T`,
and propositional composition; no deduction theorem, generalization of an
open assumption, substitution rule, equality reflexivity theorem, or rho7
is needed.

## Extraction from the joint source bundle

The source emits the K core, membership vacuity, and equality helper
jointly, using the baseline negative-conjunction encoding. After this
change, a successful gated bundle is propositionally equivalent to

\[
 K_{a,b,c}\ \wedge\ V_R(a,b,c)\ \wedge\ C_1(a,b,c).
\]

The unchanged rho8/rho6 classical bridge is already available as an independent
logical row. Its propositional projection theorems therefore recover each
of these three components from the joint bundle without a K axiom or an
equality helper as a premise. In particular, extracting the `C1` instances
used in (1)--(2) is not circular. Conversely, conjunction introduction
recovers the joint bundle from its three components.

The old gate `c != a,b` is sufficient. Both orientations of an equality
pair occur because the source enumerates all input triples; reversing `a`
and `b` preserves the gate. The independent `T` row must actually be
emitted for all numerical parameters, as the old rho7 row was. A modified
source emitter should check this coverage and placement, in addition to
checking the formula AST and machine state count.

## Applicability of the existing Source116 interpretation

The baseline Source116 result already treats the logical basis with:

* original rho1--rho6 and the original classical rho8;
* primitive equality symmetry;
* full membership vacuity;
* one fresh canonical equality-vacuity helper per off-diagonal pair;
* the retained theory axioms, MP, and closed GEN.

Derivation (1) supplies its symmetry premise. Derivation (2) supplies more
than its equality-helper premise: specialize `c` to the native membership
code `RelCode(a,b)`, which exceeds both endpoints, or to any other fresh
canonical label. Consequently the entire membership-defined equality
interpretation from
`portable/theory/source116/proofs/general_kappa_equality_helper.md` and
`portable/theory/source116/audit/mathematical_audit.md` applies.

For precision, the comparison equality is the fixed safely bound
membership-indiscernibility formula `E(a,b)` from those files. Its proved
properties include the translations of rho1, rho3, rho5, rho7, and every
gated Eq-vacuity instance. The interpretation fixes membership, the
designated bottom, implication, and quantifiers. Primitive rho7 itself
need not be derivable with its old numerical equality code.

The syntactic proof transport is an induction on the old calculus
derivation. Every old axiom leaf has the indicated translated closed
proof. MP is preserved because the interpretation commutes with
implication; GEN is preserved because it commutes with quantification and
the translated premise remains a closed theorem. No induction step for
substitution is needed, since substitution is not a primitive proof rule.
Derived specialization and alpha-conversion inside the old completeness
proof are covered by this axiom-and-rule interpretation instead of being
assumed as new primitive rules.

For the K theory, retain the existing adapter from
`portable/theory/k_equality_helper_extension.md`. It chooses the private
comparison K label after interpreting and padding the named matrix, so
the interpreted native matrix/code coupling literally matches an emitted
K core. The original gate is satisfied by the resulting freshness bound.
The K core was independently projected from the joint bundle above.
Changing its companion equality component from the old canonical helper
to `C1` does not alter this K axiom extraction or matrix-code argument.

These finite transformations give

\[
 \operatorname{Con}(H_{T,C_1,K})
 \quad\longleftrightarrow\quad
 \operatorname{Con}(\mathrm{ZFC}),
\]

using the already calibrated ordinary K/ZFC interpretation. The forward
direction uses the described comparison-calculus proof transport. The
reverse direction uses the original ordinary model interpretation: `T`
is valid universally and the `C1` binder is fresh from both endpoints, so
every replacement row and bundle is valid. The finite proof transformations
and the retained ordinary interpretations can be formalized in ZFC. This
statement does not assert a new proof-assistant endpoint for a changed
transition table; the compiler/table obligations are separate.

## Exact finite certificate

`specialization_crossed_helper_certificate.py` is a stdlib-only finite
proof builder and checker using the local representation module
`combined_helper_certificate.py`. It exports all proof nodes, checks every
leaf and MP edge, reloads the exported JSON, and checks again. It rejects
all rules except `C1`, `T`, `TAUT`, and MP. The TAUT leaves are classical
Boolean tautologies justified by the retained original rho8/rho6 bridge.

The schematic symmetry root has **5 proof nodes**; the full gated
Eq-vacuity root has **9 proof nodes**. The bundle includes one schematic
instance and five numerical instances, including coincident endpoints,
the label 0 as an endpoint, and 0 as the permitted binder. The output
`specialization_crossed_helper_receipt.json` records the proof hash and
all rule counts.

## Why rho6 cannot simply be deleted after adding T

Universal self-specialization does not make original rho6 redundant in
this logical basis. A small modal countermodel demonstrates the issue.

Let worlds be pairs `(v,t)`, where `v` assigns each natural label a value
in `{0,1}` and `t` is a stage in `{0,1}`. At `(v,t)`, `Q_i A` means that
`A` holds at every world `(v[i:=d],s)` with `d` in `{0,1}` and `s>=t`.
These accessibility relations are reflexive and commute. Interpret Eq by
ordinary equality of assigned values. Interpret membership by

\[
 R(a,b)(v,t)\quad\text{iff}\quad t=1\ \text{and}\ v_a\ne v_b.
\]

Then `F=R(0,0)` is always false. The model validates classical logic,
`T`, rho1, rho2, rho3, rho4, rho5, all positive gated membership and
equality vacuity instances, and `C1`. Validity is preserved by MP and
closed GEN. Membership-vacuity holds because true membership can only be
at stage 1 and a fresh binder does not change its endpoints.

However, at stage 0 with `v_1 != v_2`, the formula
`Ex_3 Q_3 R(1,2)` is true by choosing stage 1, whereas `R(1,2)` is false.
Thus `Ex_3 Q_3 R(1,2) -> R(1,2)` is a false rho6 instance. This is an
obstruction to deleting rho6 from the **logical interpretation proof**;
it is not presented as a model of the K theory itself.
