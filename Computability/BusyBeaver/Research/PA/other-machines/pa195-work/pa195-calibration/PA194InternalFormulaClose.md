# Model-internal formula closing

`PA194InternalFormulaClose.lean` instantiates Foundation's internal
`UformulaRec1` construction for closing a selected free label. A packed
parameter contains the selected label and current depth. Atomic relation
arguments are traversed by the internal term closer from
`PA194InternalClose.lean`; conjunction and disjunction recurse at the same
depth; quantifiers recurse at depth plus one. Positive and negative relations,
truth, falsity, conjunction, disjunction, and both quantifiers have explicit
checked recursion equations.

`graph` gives one model-independent Σ₁ formula defining the packed traversal.
`close_wellformed` proves that a formula well formed at depth `d` is sent to
one well formed at depth `d + 1`. These theorems apply when the formula code,
label, and depth are arbitrary model elements, including nonstandard values.
`close_vec_nth` identifies every atomic argument with the output of the fixed
certified candidate-PRA term-closing code. They assume a nonempty model of the
candidate `PRA` language, equality interpreted as equality, and an `IΣ₁`
arithmetic reduct. No projection-certificate premises are needed in the
exported statements because the term-code projections are chosen using their
existing certificates.

Lean reports only `propext`, `Classical.choice`, and `Quot.sound` as axioms of
the printed results. The Σ₁ graph and the structural/well-formedness results are separate facts;
this file alone does not supply a candidate-PRA formula-closing `Code 2`.
The separate [agreement proof](PA194FormulaAgreement.md) supplies such a code
and proves its all-model agreement with this traversal. This result does not
prove semantic correctness of the complete compiler or either direction of
the PA194 machine/refutation equivalence.

Run `check-internal-formula-close.sh` with `IPRA_LEAN_OVERLAY` and
`IPRA_FOUNDATION_OVERLAY` set to the audited project and Foundation object
directories. It compiles dependencies and the formula traversal into a fresh
temporary overlay and checks displayed theorem axioms for `sorryAx`.

An independent fresh Linux replay of `check-internal-formula-close.sh` also
passed with those overlays, including its dependency rebuild and axiom check.
