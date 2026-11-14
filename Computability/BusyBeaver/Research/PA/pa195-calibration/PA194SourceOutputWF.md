# Named-source translation output is well formed

`PA194SourceOutputWF.lean` proves that the explicitly coded dual translation
of the PA194 separate-diagonal calculus produces a pair of internally
well-formed depth-zero arithmetic formulas for **every** model element used as
a source code. The source code can be nonstandard. The numerical source uses
implication `4 * cantor a b`, membership `4 * cantor a b + 1`, universal
`4 * cantor body label + 2`, equality `4 * cantor a b + 3`, and the
zero/truth alias. These match the source constructor shapes used by the
standard PA194 calculus; this theorem concerns the internal candidate-PRA
code, and does not identify nonstandard machine executions with derivations.

`all_wf` assumes a nonempty candidate-PRA model whose arithmetic reduct
satisfies IΣ₁, equality interpreted as equality, and candidate-PRA certificates
for the source tag and both child decoders. The canonical formula closer's
projection certificates are already discharged. `fixed_all_wf` chooses the
three certified source decoders once and for all, eliminating those certificate
premises as well. Lean prints the exact theorem signatures and reports only
`propext`, `Classical.choice`, and `Quot.sound` for the proved results, with no
`sorryAx`.

The proof establishes the five constructor cases, splits every internal code
using division by four and internal Cantor surjectivity, and applies Σ₁ strong
induction. For nonzero implication codes, both children are strictly smaller;
for universal codes, the body is strictly smaller. In the universal case it
uses the model-uniform canonical-closer agreement and proves the recursive
well-formedness hypotheses, rather than assuming them.

The separate [polarity proof](PA194SourcePolarity.md) shows that the
negative output is the internal syntactic negation of the positive output.
Well-formedness and syntactic polarity by themselves do not establish a truth
predicate or positive/negative semantic duality for nonstandard formulas, preservation of the source calculus's axioms and inference rules, a
proof-code translation to or from Foundation's relational source syntax, or
either PA194 machine/consistency implication. The latter source syntax has a
different encoding; the bridge remains a separate proof obligation.

Run `check-source-output-wf.sh` with the audited `IPRA_LEAN_OVERLAY` and
`IPRA_FOUNDATION_OVERLAY` set. It rebuilds both the arithmetic closing chain
and the numerical-source traversal chain before checking this theorem.

An independent fresh Linux replay of `check-source-output-wf.sh` passed with
the audited overlays, rebuilding both prerequisite chains and finding no
`sorryAx` in the checked theorem dependencies.
