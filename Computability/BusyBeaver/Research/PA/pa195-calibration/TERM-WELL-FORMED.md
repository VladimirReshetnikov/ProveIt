# Conditional well-formedness of internal terms

`PA194TermWellFormed.internal` proves that the primitive-recursive `closeCode`
returns an internally well-formed arithmetic semiterm at depth `d + 1` when
applied to an internally well-formed semiterm at depth `d`. The input code,
label, and depth are arbitrary model elements, including nonstandard ones.

The model must satisfy candidate PRA, and its arithmetic reduct must satisfy
IΣ₁. The first and second pair projections must satisfy the explicit PRA
certificates. In addition the theorem **assumes**, for the selected code,
label and depth, that the predicate “the output of `closeCode` is a
well-formed semiterm at depth `d + 1`” is Σ₁-definable in the arithmetic
reduct. This final definability assumption has not been discharged here. It
is needed to invoke Foundation's `IsSemiterm.sigma1_induction`.

`predicate_of_function` and `internal_of_function` give a sufficient
condition: it is enough that the unary function taking an internal term code
`t` to `closeCode(t, label, d)` is Σ₁-definable in the arithmetic reduct. The
predicate condition then follows by composition with Foundation's definable
`IsSemiterm` relation. The function-level condition has not been proved for
the candidate-PRA interpretation, and it does not follow merely from the
code's primitive-recursive behavior on standard natural numbers.

The proof handles all internal arithmetic function nodes using their arity 0
or 2. It establishes well-formedness of the result, not its identification
with a particular internal syntax rewrite, and does not prove a formula
closing theorem or a machine/PA consistency equivalence.

Run `check-term-well-formed.sh` with the audited `IPRA_LEAN_OVERLAY` and
`IPRA_FOUNDATION_OVERLAY` paths set. The checker rebuilds the local prerequisite
chain and rejects `sorryAx`; the theorem's axiom report contains only
`propext`, `Classical.choice`, and `Quot.sound`.
