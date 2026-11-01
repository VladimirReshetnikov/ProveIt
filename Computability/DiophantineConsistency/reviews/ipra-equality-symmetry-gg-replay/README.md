# Native equality symmetry and its GG image

This derives the ordinary intuitionistic symmetry sentence in native iPRA
from the existing reflexivity and full finite-parameter Leibniz substitution
axioms. It instantiates those closed axioms, closes the free-variable proof
under their shift-invariant finite context, and applies the checked atomic
implication GG adapter. `symmetry_image` proves the GG image of the actual
Foundation `Theory.Eq.symm` axiom, without assuming equality decidability.

Transitivity and arbitrary-arity function/relation congruence remain open, as
do the classical equation comparison and ordinary consistency bridge.
External transitive ancestry is inherited. Run
`python3 Computability/DiophantineConsistency/reviews/ipra-equality-symmetry-gg-replay/replay.py`.

Author PASS; all four axiom reports were separately parsed and contained
only `propext`, `Classical.choice`, and `Quot.sound`.

Independent peer PASS; source/object/full-log rows match author and all
four axiom reports contain only the standard Lean trio.
