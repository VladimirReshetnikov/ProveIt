# Explicit candidate formula-closing code

`PA194FormulaUpdate.lean` defines a candidate-PRA stage update for closing a
free label in a Foundation arithmetic formula. It indexes history by the
pair of source formula code and remaining depth budget, and retains the label
and a fixed depth ceiling as parameters. At an atom, the current depth is
`ceiling - budget`. Boolean children retain the budget, and quantifier bodies
use one less. The explicit `closeAtDepth` chooses the original formula code as
its starting budget and `budget + depth` as the ceiling. The explicit
`closeFormula : Code 2` supplies the compiler's expected label/formula
argument order and starts at depth zero.

For arbitrary elements in every candidate-PRA model, with certificates for the
two pairing projection codes, the file proves numeric equations for:

* positive and negative binary relation nodes (`modelAtom`), using the
  previously constructed candidate term closer on both arguments;
* truth and falsity (`modelTruth`);
* conjunction and disjunction (`modelBoolean`), preserving the budget;
* universal and existential quantifiers (`modelQuantifier`), decreasing a
  positive budget by one.

These equations do not require IΣ₁. The atomic equation expresses the
ceiling as `budget + depth`. The general Boolean and quantifier equations use
the **same fixed ceiling**, and thus are equations for `budgetClose`, not yet
constructor equations for the root wrapper `closeFormula`. The stage code's
behavior on malformed formula codes is outside this claim.

The separate [agreement proof](PA194FormulaAgreement.md) proves that the root
wrapper agrees with `PA194InternalFormulaClose.close` on all model-internal
well-formed formulas, and handles the changing budget at a fixed ceiling. It
also proves well-formedness of the fixed canonical root wrapper. Neither that
agreement nor the compiler's overall correctness is proved by this file's
constructor equations alone. No PA194 machine/refutation implication follows
from these equations alone. The printed theorems use only `propext`, `Classical.choice`,
and `Quot.sound`, with no `sorryAx`.

Run `check-formula-update.sh` with the audited `IPRA_LEAN_OVERLAY` and
`IPRA_FOUNDATION_OVERLAY` set. The script builds the term and budget
dependencies in a fresh temporary overlay before checking this file.

An independent fresh Linux replay of `check-formula-update.sh` passed with the
audited overlays, rebuilding the local dependencies and finding no `sorryAx`
in the checked theorem dependencies.
