# K/S-only: the stable-label commutation gap and a model-class obstruction

Author: review_upstream_reflection, 20 October 2026. Ordinary structural
analysis, no proof-assistant or search execution. The new mixed-commutation
calibration is separate; it changes rho4 and is already published.

## Exact remaining obligation

Retain original rho4 and replace only rho8 by K/S. The co-translation from the
mixed-commutation proof is still an injective primitive-recursive native-code
map, fixes zero and falsum, and makes every translated code stable. All of its
row/rule and literal-bundle translations except rho4 go through unchanged.
Writing i'=tau(i), j'=tau(j), A'=tau(A), the single missing family is

    NN Q_i' NN Q_j' A' -> NN Q_j' NN Q_i' A'.             (T4)

Every i', j', A' is a stable FORMULA code. The ordinary proof currently has no
rule that converts stability of the formula named i' into a special property
of quantification at the numeric variable label i'. They are the same natural
number in the native syntax, but occupy different constructor positions.
Literal bundle instances are the available bridge between these two roles;
forgetting that distinction would assume the desired result.

The stronger mixed schema M implies T4 by the already checked finite bridge.
For K/S alone, deriving M on these triples would suffice, but T4 itself is the
weaker and exact target. There is no need to derive M for arbitrary untransformed
codes or full quantified stability in order to complete this particular
refutation translation.

The Source 144 nine-element example refutes unrestricted commutation of the
Booleanized modal maps under normality, seriality, B6 and original commutation.
Its body witness is already regular. Assigning stable formula names to the
operator indices does not add a modal premise by itself. However that example
does not interpret all native R/E constructors or the full gated bundle, so it
is not a countermodel of this precise native problem.

## A stronger obstruction: only membership recycling is needed

Consider any nontrivial Heyting algebra H with bottom f and top t, and a native
valuation v satisfying the following particular model design:

* v(0)=t, v(F)=f, and native implication is Heyting implication;
* v(R(a,b))=r(v(a),v(b)) for a binary operation r;
* v(Q_i A)=q_i(v(A)), with completely arbitrary dependence on the literal
  numeric label i; each q_i preserves top and bottom;
* the literal Code254/KCode222 definitions and every gated bundle are valid.

No finiteness assumption is needed. These conditions are inconsistent.

The native falsum is F=R(0,0)=1, so r(t,t)=f. The positive code
k=I(F,F)=16 has value t, just as code zero does. Use the valid gated bundle
(a,b,c)=(16,16,0); both inequalities 0!=16 hold. The matrix and both formula-valued membership arguments have value t. The
operators q_0 and q_16 may be different. Exact native definitions nevertheless give

    R(a,b)=R(b,c)=R(c,a)=R(c,b)=f,
    Sub = q_0(f -> f) = t,
    B=req(b,c,c) = q_16(t -> N q_16(t -> N f)) = q_16(f) = f,
    C=clos(a,b,c,c) = q_16(f -> N q_16(t -> N q_16(Sub -> B))) = t,
    J=nks(a,b,c) = q_0(C -> N B) = t,
    V=vrel(a,b,c) = f -> q_0(f) = t,
    bundle = N(V -> J) = f.

That contradicts validity. This is an all-algebra calculation, not a finite
negative search. It needs neither commutation nor B6 once top/bottom preservation
has been supplied. In a standard Heyting interpretation of the full K/S-only
rows, theorem-only GEN supplies q_i(t)=t and the previously derived seriality
q_i(f)->f supplies q_i(f)=f for each literal label i. Thus those two assumptions do not add a missing axiom
to the intended model class.

The contradiction also directly covers the translated-label fragment:
tau(0)=0 and tau(16)=16, so the two offending names are themselves stable
translated codes. Injectivity preserves their different NUMERIC identities;
it does not permit membership to depend only on their coinciding formula
values. Quantification may already distinguish the literal labels and the
contradiction still holds. No restriction on E beyond whatever was used to
establish seriality is needed for this calculation.

This explains why extending the earlier recycled-code-value three-value model
to full K/S is not a useful next finite search. That earlier model does not
validate all identities: its value of code16 differs from designated truth.
It therefore evades the exact collision used above. Nothing here contradicts
that accepted K+RAB(+QS) obstruction.

## What a further model or proof would need

A further algebra cannot let membership factor solely through formula values.
A separate component sigma(n) used by membership is one possible repair, but
this argument does not force an analogous change to equality or quantifier
indexing: the strengthened proof above already allows all q_i to be distinct.
It requires only that the relevant membership atoms cease all collapsing to
f. Keeping sigma(0) distinct from sigma(16) can remove this particular collapse;
no assertion that a zero/nonzero classification validates the remaining rows
is made. The bundle must still use the same literal c for its matrix value and
private binder, and its gate remains numeric c!=a,b. Treating label features
and matrix values as independent variables without checking all actual native
instances would change the task.

The strongest economical proof target remains T4 restricted to the tau-image.
A proof of all quantified stability would be sufficient but is stronger.
Likewise, ordinary first-order variable instantiation, unrestricted substitution,
a deduction step generalizing an open premise, or a witness-container theorem
cannot be imported silently: the Source 144 supplement itself identifies their
native bootstrap as unresolved. No such rule has been derived in this note.

Consequently this investigation yields a rigorous model-class exclusion and
isolates one exact missing native theorem. It proves neither K/S-only
calibration nor its failure. No broad solver search is justified by the old
three-value design without first giving membership more information than its arguments' formula
values. Root independently read the first version and observed that the
quantifier-recycling restriction was unnecessary. This successor retains
arbitrary literal-label operators; the original note and receipt are preserved
under history-v1, with their narrower valid theorem and overbroad suggested
next-model requirement explicitly superseded here.
