# Internal free-label renaming fixes PA axioms

`PA194GenericRenameBase.lean` constructs internal term and formula traversals
from any supplied arithmetic Σ₁ formula that correctly represents a
parameterized model-internal free-label map. Bound variables are left unchanged;
the map parameter passes unchanged through quantifiers. The definition is a
Foundation internal recursion with a supplied graph, not yet a fixed
candidate-PRA code for the formula traversal.

`PA194GenericRenameAxiom.lean` proves that these traversals leave every
shift-fixed internally well-formed formula unchanged, and in particular fix
every code in Foundation's concrete `𝗣𝗔.Δ₁Class`. The result applies to
nonstandard formulas, axiom codes, and map parameters, in every nonempty
candidate-PRA model with equality and an IΣ₁ arithmetic reduct. It assumes the
supplied graph is correct for **all** model values. No injectivity or semantic
truth predicate is assumed. Lean reports `propext`, `Classical.choice`, and
`Quot.sound` for the printed dependencies, with no `sorryAx`.

The final corollary supplies a fixed Σ₁ graph for the existing finite
candidate-PRA protected-prefix label code `PA194LiftRename.renameCode`, with
its `k,a` parameters packed into one model value. The generic theorem also
applies to other maps once their fixed Σ₁ graph and all-model correctness are
provided. In particular, this corollary alone does not establish closure of
that small family under the proof calculus's shift rule; an expanded
renaming family, formula-code implementation, compatibility with proof-rule
premises, and a derivation transformer remain open. No iPRA proof or PA194
consistency equivalence follows yet.

Run `check-generic-rename-axiom.sh` with audited `IPRA_LEAN_OVERLAY` and
`IPRA_FOUNDATION_OVERLAY` set. It rebuilds the dependencies in a fresh
temporary overlay and rejects `sorryAx`.

An independent fresh Linux replay passed with the audited overlays, rebuilding
the local prerequisites. The displayed axiom-invariance theorems reported no
`sorryAx` dependencies.
