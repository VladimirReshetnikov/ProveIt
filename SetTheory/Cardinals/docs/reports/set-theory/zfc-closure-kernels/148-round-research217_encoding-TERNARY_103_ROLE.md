# Exact role of the repeated103-leaf block

The owned allocation reconstruction on the pinned primary218 source identifies:

- I = physical90's27-leaf implication-constructor source subtree.
- Q = physical86's29-leaf quantifier-constructor subtree, literally(I,(CI1,CI1)).
- N = physical184's47-leaf negation constructor, literally(PushOne,I).
- C = physical172's103-leaf role, literally((I,Q),N).
- Physical200's206-leaf role is literally((I,Q),(N,C)). A closed left rotation makes(C,C).

These equalities were checked against full literal ASTs, not inferred from leaf counts. Physical172 also has a distinct74-leaf source role, so the equality does not imply a context-free physical entry.

With the inherited constructor contracts, write P for Cantor pairing, I(a,b)=4P(a,b), Q(a,b)=4P(a,b)+2, and N(x)=I(x,1). On R1=c, R2=P(b,P(a,t)), and scratch R6=R7=0, C terminates with R1=N(Q(a,I(b,c))), R2=t, scratch again0, and every other register unchanged. The arithmetic values a,b,c,t are arbitrary naturals; no decodability assumption about formula operands is needed. This follows by composing the implication pop/construct, quantifier pop/construct, and negation push-one/construct contracts in that order.

Twice executing C starts on five stack operands(a,b,c,d,e), with e on top, and produces C(a,b,C(c,d,e)). It is neither double negation nor an idempotent transformer. Logical simplification of this constructor pattern would change the axiom presentation and requires a new soundness/completeness calibration; no such reduction is asserted here.

The simple200 allocation fails because C's existing physical172 entry currently uses predecessor marker1, whereas the first C in(C,C) has marker0. The failed prefix/alias receipts are in TARGET_ROTATION_RESULTS.json.
