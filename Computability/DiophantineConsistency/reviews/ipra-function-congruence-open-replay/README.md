# Open arbitrary-arity function congruence in native iPRA

`function_conj_open` proves in a finite context of actual native Leibniz,
reflexivity and transitivity axioms that the finite conjunction of arbitrary
coordinate equalities implies equality of arbitrary-arity function outputs.
The proof specializes the native Leibniz schema at one coordinate and uses
Lean metatheoretic finite iteration; it assumes no object-theory induction or
equality decidability. The module also proves a reusable universal-closure
generalization lemma for a shift-invariant finite context.

Binding this open result to Foundation's exact closed function-congruence
axiom and its GG image remains open. The parent provider is historical; five
unrelated post-merge broad source guards are excluded and listed in the
manifest as inherited from the specialization packet. Actual native import
closures were separately source-audited post-merge. External transitive
ancestry is inherited. Run
`python3 Computability/DiophantineConsistency/reviews/ipra-function-congruence-open-replay/replay.py`.

Author PASS; all five endpoint axiom reports were separately parsed and
contain only the standard Lean trio.

Independent peer PASS; all six source/object/full-log rows match author,
and all five endpoint axiom reports contain only the standard Lean trio.
