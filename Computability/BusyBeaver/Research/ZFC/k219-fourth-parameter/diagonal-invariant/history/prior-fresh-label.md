# Fresh-label correction: exact Boolean quantifier values are unnecessary

Independent source-only analysis by opening_encoder, 20 October 2026.
This is an addendum to [analysis.md](history/analysis.md), retained unchanged
as history. The fresh-label lemma was proposed by root and independently
checked here against the literal K definitions.
It corrects that note's claimed need for an exact Boolean-valued Q in the
semantic model-extraction step. It does not establish model existence from
consistency of the modified calculus.

Assume a nonempty assignment domain, one designated value t, distinct falsum
0, compositional native evaluation and the native strict free-label support
bound. Assume r(x,x)=0, J(0,x)=t, J(t,x)=t iff x=t, and Boolean negation:
J(x,0)=t for x!=t, J(t,0)=0. Q need only satisfy

    Q_i A has value t iff every i-variant of the assignment gives A value t.

Its nondesignated value can be arbitrary. The native truth alias has value t,
so J(t,t)=t. Equality in the ordinary target is actual identity. Every literal
modified rho8 instance and every enabled native K bundle are valid under every
assignment.

## The new lemma

Fix any native code B>0 and assignment sigma, with value b. The strict support
bound makes label B absent from B's free support. Change only assignment B to
sigma(0). This preserves b, including when B contains free label0. In the
rho8 instance A=C=truth code0, its literal fourth argument R(0,B) now has value
r(sigma(0),sigma(0))=0. Thus validity gives

    L(t,b,t,0) = J(t,J(t,J(b,t))) = t.

Twice using J(t,x)=t iff x=t yields J(b,t)=t. For B=0 the result is simply
J(t,t)=t. This proves implication-to-truth for every realized native formula
value, with no designated membership edge, richness, Boolean Q, or unproved
syntactic substitution rule. The temporary assignment modification is purely
semantic; it exploits exactly the numerical code-as-label coupling.

Consequently implication into either Boolean consequent is material on all
realized values. Native N is Boolean; NN A is the Boolean indicator of A's
designatedness. Native conjunction N J(A,N B) is Boolean and designated iff
both A and B are designated. Native existential N Q_i N A is Boolean and
designated iff some i-variant makes A designated. The atomic-material lemma
from the fixed codes A1/B0/C73/U5 still makes native Sub designated exactly
when designated membership is ordinary inclusion.

## Extracting the unchanged K bundle

One must not call the literal bundle N J(V,D) a fully Boolean conjunction
when D itself is a potentially non-Boolean quantified core. That stronger
claim does not follow. The needed implication does follow:

    N J(V,D) designated implies D nondesignated,

because D=t would force J(V,D)=t by the new lemma. In the literal core
D=Q_C J(H,N W), nondesignatedness yields a C with J(H,N W) nondesignated.
The consequent N W is Boolean. Material implication into Boolean consequents
therefore forces H designated and W designated. No projection of V is needed
for ordinary K extraction.

In H, universal designatedness and MP imply the required closure whenever
membership and Sub are designated. Native conjunction gives the support
clause as well. Possible failure of a nondesignated antecedent to imply a
nondesignated consequent can only strengthen H; exact classical equivalence
of H is unnecessary. W's existential/support subexpressions use N/Q, so their
needed designatedness meanings follow from the preceding elementary laws.
Thus the extracted container satisfies the ordinary subset-closure and full
support K clauses for the designated relation. Irreflexivity follows from
r(x,x)=0.

To instantiate every ordinary matrix, translate atoms by NN, translate
implication recursively, and translate universal quantification by NN Q of
the translated body. Structural induction gives a Boolean value equal to
ordinary truth. Native code0/implication alias is compatible with J(t,t)=t.
Choose the literal K private binder to be the resulting translated code,
after translation, using the unchanged strict support bound and the usual
public-label renaming/padding. The old matrix code must not be silently kept.

## Remaining gap

The semantic reduction now works for this larger class with arbitrary
quantifier output values satisfying designatedness semantics. The previous
analysis.md objection at Sub→W does not block one-way K extraction and should
not be repeated as a remaining obstruction.

There is still no proof that consistency of the modified, code-coupled
calculus yields a model with one designated value, Boolean negation and the
listed implication/quantifier laws. A general Lindenbaum algebra does not
automatically satisfy those properties; ordinary classical completeness would
presuppose the missing propositional strength. This is therefore substantive
semantic progress, not the missing equiconsistency theorem or a <=218 machine.

## Literal-code cross-check (KCode222, unchanged by K219)

I read the exact maintained definitions of req, clos, nks and bundle222 in
Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KCode222.lean, together with the
SeedProp interface in KSeed222.lean. They are, with private label k and matrix m:

    req(b,k,m) = Q_b (m -> N Q_b (m -> N R(b,k)))
    clos(a,b,k,m) = Q_b (R(b,k) ->
        N Q_a (m -> N Q_a (Sub(a,b) -> req(b,k,m))))
    nks(a,b,c) = Q_c (clos(a,b,c,c) -> N req(b,c,c))
    bundle(a,b,c) = N (V(a,b,c) -> nks(a,b,c)).

The two occurrences of Q_a in clos intentionally shadow the first witness:
the outer negative universal selects one supporting input x for a container
member y; the inner universal ranges over every x' subset of y. This is not
an unguarded closure theorem for the same supporting x. In the subset formula,
its Q_k shadows the private container only inside Sub; it does not bind k in
the sibling req consequent. The gate c!=a,b and matrix independence of c
are exactly the required assignment facts.

Literal extraction at a fixed member y is therefore:

1. clos designated and R(y,C)=t force
   N Q_a(m -> N Q_a(Sub -> req)) designated.
2. Some a-assignment has m -> N Q_a(Sub -> req) nondesignated.
3. Boolean-consequent materiality forces that m designated (support) and
   Q_a(Sub -> req) designated (closure for every shadowed a-assignment).
4. Actual subset gives designated Sub; MP gives designated req.
5. req designated yields a member of C witnessing the matrix whenever that
   matrix has a witness, by its displayed negative-universal consequent.

This is precisely the ordinary SeedProp support/subset-closure condition,
not the weaker HC equality-only closure. The outer nks extraction gives the
same req at the seed input. Only one-way extraction of clos is used.
