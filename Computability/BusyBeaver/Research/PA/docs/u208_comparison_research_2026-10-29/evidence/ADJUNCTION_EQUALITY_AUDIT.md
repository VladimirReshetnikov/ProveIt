# Independent audit of proposed weak filtered adjunction

This is a mathematical review of the proposed new theory, not acceptance of a transition table or an exported PA derivation.

## Equality issue: conditional quotient argument, native bridge NOT closed

IMPORTANT CORRECTION after reading Interp222.v and L224Def.v: the argument below applies to a schema ALREADY interpreted with EInd in its guard. The actual proposed numerical emitter has a raw auxiliary-equality guard. Interp222 only supplies interpreted pure logic, and does not automatically translate that nonlogical raw-equality axiom. Thus this note DOES NOT prove completeness of the proposed native calculus. A finite derivation of EInd-guarded adjunction, ordinary auxiliary-equality vacuity, or a replacement equality-free emitter is still required.

The inherited native numerical calculus's auxiliary equality need not be primitive equality in an arbitrary membership structure. Interpret it by

EInd(x,y) := [forall z (E(z,x) iff E(z,y))] and [forall z (E(x,z) iff E(y,z))].

EInd is an equivalence relation. If EInd(x,x') and EInd(y,y'), then E(x,y) iff E(x',y') by the second and first profile clauses in succession. Thus it is a congruence for the entire membership language. Structural induction proves every formula translated by replacing equality by EInd invariant in its free variables.

Consequently the following weak adjunction schema, with equality interpreted by EInd, is a relative interpretation of the corresponding genuine-equality theory on the definable quotient:

forall a,y exists b [forall x (E(x,b) -> phi(x)) and forall x ((E(x,a) or EInd(x,y)) -> (phi(x) -> E(x,b)))].

Here output b is not free in phi; arbitrary other parameters are allowed. Using matrix (E(x,a) or EInd(x,y)) and phi(x) gives exact filtered adjunction. Every formula of the quotient theory has a legal translated native matrix. The argument can be formulated entirely syntactically: equality axioms follow from equivalence/congruence, and each exact-adjunction schema instance follows by a fixed finite derivation from one weak instance. Formula relativization and proof concatenation are primitive recursive. No Extensionality axiom is needed for this quotient step.

The PA upper interpretation uses binary-bit membership. Binary extensionality proves EInd(x,y) iff x=y, and bounded binary comprehension supplies exact filtered subsets of a union {y}. Global irreflexivity is true in this interpretation. Thus upper soundness and the quotient lower interpretation fit together; one must not simply reuse the old equality-free W argument unchanged.

## Small-code cases in the proposed fixed-role emitter

Let source variable be v0, test v1, adjoined variable v5, and output vc, where c is also the decoded matrix. Assume the inherited code identities D(0)=truth, D(1)=E(v0,v0), D(5)=E(v1,v0), and global irreflexivity.

* c=0 captures the source as output, and truth reduces the lower clause to requiring a container of v5. Adjunction supplies one; no prescribed old source is required after binding v0.
* c=1 captures the tested variable. The matrix is false under irreflexivity, so the lower implication is vacuous and the upper clause holds because E(v1,v1) is false. Nonempty domains supply the existential witness.
* c=5 captures the adjoined variable. Choose output equal to the source v0. Both clauses reduce to implications between E(v1,v0) and itself. This remains valid with EInd equality.
* Other c must satisfy the actual codec's domination lemma ensuring vc is not free in D(c). This is an inherited lemma to verify against the precise emitter, not a consequence of the three small cases alone.

These checks establish soundness of the three collision cases; they do not by themselves establish completeness of enumeration. Completeness must show that arbitrary matrices can be renamed/padded into the fixed source/test/adjoined role convention with fresh output, while preserving the numerical proof-search compilation and protected startup.

## PA strength remains an explicit cited dependency

Harvey Friedman, Issues in the Foundations of Mathematics, Goedel Lecture, 2 June 2002, section C2, printed page10, explicitly states that the single exact filtered-adjunction schema in first-order logic with equality is mutually interpretable with PA. The text does not add Extensionality as a separate axiom. The displayed formula appears to interchange the output and tested variable (z/w) on the right; the intended filtered-adjunction reading and this typographical correction must be disclosed.

Source: https://cpb-us-w2.wpmucdn.com/u.osu.edu/dist/1/1952/files/2014/01/GodelLect060202-n2gdjc.pdf

The lecture announces the mutual interpretation but does not give the full lower interpretation. A claimed self-contained proof must reconstruct it, or cite it honestly as a mathematical dependency. Naively identifying objects with equal membership profiles does not solve the lower proof: coextensionality alone need not be a first-coordinate congruence, and empty objects need not be unique without Extensionality. A possible constructive lower route uses finite transitive linear orders with represented-subset endpoints, separation-based least-failure induction, and equality interpreted by order-isomorphism/cardinality; this route is not completed in this note.

## Possible but unproved repair
The raw schema instantiated with matrix Eq(x,y) suggests an Eq-singleton whose membership is equivalent to raw Eq(x,y). With ordinary quantifier reasoning this would imply EInd(x,y) -> Eq(x,y) by reflexivity and membership congruence. But arbitrary raw-Eq vacuity is precisely absent in the retained numerical basis, so using ordinary quantifier specialization or renaming to justify this step can be circular. It needs an explicit derivation in L224Def/Thm222, not merely a model-theoretic quotient statement.
