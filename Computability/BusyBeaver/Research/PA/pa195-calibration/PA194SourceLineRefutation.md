# Conditional internal PA refutation from source lines

`PA194ContradictionInternalRefutation.lean` lifts the existing standard PA
proof of the universal closure of the negated distinguished contradiction to
an internal PA proof in every IΣ₁ arithmetic model. The proof explicitly
quotes the standard proof, identifies the universal closure's single bound
variable, and specializes it at internal free variable 0. It then shows that
internal PA provability of the quoted contradiction implies internal PA
provability of falsum. These are model-uniform proof-existence statements;
the latter theorem does not require a candidate-PRA expansion.

`PA194SourceLineRefutation.lean` combines that endpoint with the numerical
source line-history soundness theorem. In every nonempty candidate-PRA model
with equality and an IΣ₁ arithmetic reduct, any internally coded line
sequence, including one of nonstandard length, yields an internal PA proof of
falsum if:

- every line is a seed, numerical modus-ponens conclusion from earlier lines,
  or numerical universal-generalization conclusion from an earlier line;
- every seed's positive translation is internally PA-provable; and
- some line is the distinguished numerical contradiction code `1`.

Lean reports `propext`, `Classical.choice`, and `Quot.sound` for the printed
theorem dependencies, with no `sorryAx`. The line-validity and seed
hypotheses are explicit: this package does not prove all concrete numerical
seed axioms or construct the line history from a PA194 machine execution.
It is not yet an object-theory iPRA theorem or a PA194 consistency implication.

Run `check-source-line-refutation.sh` with the audited `IPRA_LEAN_OVERLAY` and
`IPRA_FOUNDATION_OVERLAY` set; it rebuilds the dependencies in a fresh
temporary overlay and rejects `sorryAx`.

An independent suffix replay rebuilt both final modules against retained
prerequisite overlays, with no `sorryAx` in the reported theorem dependencies.
The complete author fresh dependency replay also passed with the audited
overlays and no `sorryAx`.
