# A ZFC internalization criterion that does not require a proof-code compiler

The requested metatheory is ZFC. A primitive-recursive translator between all
proof codes is an excellent stronger deliverable, but it is not a necessary
hypothesis for a ZFC-provable consistency equivalence. Uniform semantic
arguments over set-coded structures can suffice. Conversely, an external
equivalence about standard computations, or a successful proof-assistant
build, does not by itself specify the required internal statement.

## Model calibration

Fix effective first-order presentations of T and ZFC, with explicit syntax
and proof predicates. Write Mod_T(M) for the first-order set-theoretic formula
saying that the set-coded structure M satisfies every axiom code of T.
Satisfaction here is the ordinary recursively defined satisfaction relation
of a set structure. It is not a truth predicate for the ambient universe.

Suppose ZFC proves both of the following uniform assertions:

    for every M, Mod_T(M) implies there exists N with Mod_ZFC(N);
    for every N, Mod_ZFC(N) implies there exists M with Mod_T(M).

Then ZFC proves Con(T) iff Con(ZFC).

Proof. The first-order completeness theorem, formalized in ZFC for countable
effective languages, proves Con(T) iff there exists a set-coded model of T.
The same internal theorem applies to the formally presented theory ZFC.
Apply the two hypothesized model-existence implications between these
equivalences. No selection of a model is needed as an executable operation,
and no simultaneous recursive choice of proof translations is needed.

The quantifiers over M and N are essential. A construction checked only in
the intended ambient universe, only for transitive models, or separately for
each standard axiom does not establish the displayed formulas. In particular,
Con(ZFC) is equivalent to the existence of an arbitrary set-coded model;
existence of a transitive or externally well-founded model is a stronger
requirement and must not be silently substituted.

For a definable interpretation of a theory inside a set-coded model M, this
uniformity is concrete: its interpreted domain is a definable subset of the
set underlying M, and its quotient is a set quotient by a definable equivalence
relation. Formula translation must be recursive on arbitrary finite formula
codes, with a proved satisfaction induction, and every axiom-schema case must
be proved uniformly in its matrix code and parameters. Noncomputable use of
Separation, quotient sets, completeness, or the Henkin construction is allowed
in the metatheory ZFC even though the machine itself must be computable.

## Refutation calibration and the machine

Let C(n) be the exact acceptance predicate for a finite candidate, including
parsing, variable conditions, axiom recognition and the fixed contradiction
target. Let Halt_M(t) be the explicit finite-run halting predicate for the
literal blank-tape machine M. It is enough to prove in ZFC that

    exists n C(n) iff not Con(T),
    exists t Halt_M(t) iff exists n C(n).

Together with the model-calibration result, these give in ZFC

    not exists t Halt_M(t) iff Con(ZFC).

The first equivalence can be established by syntactic proof transports, but
also by ordinary soundness and refutational completeness: no model can admit
an accepting refutation; if no refutation is accepted, the complete calculus
supplies a model, with all finite proof witnesses represented by candidate
codes. A semantic proof still has to refer to the actual checker and its
finite-code definitions. Merely naming a complete abstract calculus does not
verify a Python implementation or its machine compilation.

The second equivalence requires an unbounded computation proof. A finite
bootstrap theorem discharges its initial-configuration obligation. One then
needs an invariant at each dispatch boundary and a verified macro simulation
whose blocks always terminate under that invariant, preserve representation,
perform the intended next instruction and introduce no spurious halting edge.
The proof search also needs a completeness argument from the actual retained
registers/cache/stack, not only from an ideal cleared abstract state. The new
253 bootstrap fixes a concrete starting frame but proves none of those
arbitrary-runtime obligations by itself.

## Relation to Coq and Lean verification

A Coq theorem about finite computation traces or finite derivations is highly
relevant evidence and can provide the entire mathematical argument. For this
ZFC target there is no requirement to port that argument to Lean or serialize
an enormous object-level ZFC proof. What is required is an identified ZFC
formalization of the concrete statement and its supporting constructions.

A safe route is to give ordinary ZFC proofs of the uniform model,
refutation, and machine equivalences above, using the checked development as
the source of the finite algorithms and mathematical lemmas. Another route is
to supply a verified interpretation of the actually used foundational
fragment. Neither route may simply assume global Coq or Lean soundness inside
ZFC: unrestricted proof-assistant foundations, universes, and reflection are
different issues from a particular finite arithmetical statement.

Thus two blanket conclusions should be avoided. 'Not ported to Lean' does not
show that ZFC provability is absent. 'Coq checked it' does not, without the
statement and interpretation audit, establish the exact arithmetized ZFC
biconditional requested here. The present formal contribution closes only
the named-variable logical-completeness component. The model-calibration and
literal-machine equivalences remain separately stated obligations for each
candidate and each exact machine table.
