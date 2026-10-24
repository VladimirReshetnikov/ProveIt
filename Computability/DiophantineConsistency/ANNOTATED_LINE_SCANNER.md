# Guarded numeric proof lines and the complete logical scanner

This checkpoint supplies literal `ScalarPRCode` data for the full logical
proof-line scanner. Its accepted certificate language is exactly the existing
`AnnotatedProofChecker` language for `Prov G a`, with all seventeen original
rules. The implementation does not use an axiomhood oracle, a formula parser
premise, a provability decider, or a program extracted from an existential
primitive-recursiveness theorem.

## Local checking

`AnnotatedParents.check` compares the entire ordered expected-premise spine
with an untrusted parent-index spine. Its fuel is fixed compiler data; three
steps suffice for every original rule. Every index uses the existing guarded
lookup: missing entries return zero, whereas a found entry carries a successor
marker. In particular, a missing parent cannot match an expected numeric zero.
Both list spines must terminate together. `check_judgments_raw` recovers an
exact finite list of original backward indices from any accepted raw natural
parent code, without assuming that it has already been decoded.

`AnnotatedRuleSide` supplies the exact original side conditions. The
assumption rule requires a guarded lookup of its formula in the validated
context. The other sixteen rules have the original unconditional side value.
The universal equivalence `exists_ofRule_iff` is with `Rule.side`, including
its actual membership test.

`AnnotatedLine` joins these checks to the frozen coordinate validator and
literal rule schedules. Each numeric line uses six fields:

```text
rule tag, coordinate code, coordinate evidence,
side witness, parent-list code, claimed output judgment code.
```

The coordinate evidence establishes actual formulas and a context, with the
required instantiations and shifts. The validator enforces `tag < 17`, the
exact side condition, the ordered backward premises, and equality of the
claimed output with the literal rule-output schedule. `check_sound` recovers
an actual original `Line` whose `Line.valid` value is true, with exactly the
original parent list and output code. `check_complete` supplies numeric
evidence for every original valid line.

The output selector and premise selector each occur once in the supplied
line program, as inputs of small fixed-coordinate checks. The scanner appends
the checked output field rather than computing the selector again.

## Whole logical execution

`AnnotatedLineScan` stores the state
`(remainingProofList, acceptedJudgmentHistory)`. Initially the history is
empty. A successful line consumes one proof-list cell and prepends its checked
judgment. Failure resets the state to zero. Terminal acceptance requires that
the proof is fully consumed and that a nonempty history ends in the claimed
goal judgment. The fuel is an additional untrusted natural input; it is not a
trusted termination assertion. Soundness holds for every fuel, and
completeness chooses the actual original line count.

The supplied program input is `(goalCode,(fuel,proofCode))`. The principal
checked statements are:

```text
program_sound:
  program.eval raw = 1 →
  ∃ j, raw.left = judgmentCode j ∧ Prov j.context j.conclusion

exists_program_iff:
  (∃ fuel proofCode,
    program.eval (goalCode,(fuel,proofCode)) = 1)
  ↔ Prov G a                 where goalCode = judgmentCode ⟨G,a⟩.
```

`scan_sound` constructs the actual typed history only in its proof invariant.
Accepted raw inputs require no external parser hypothesis. `run_complete`
annotates every original valid line execution, preserving the line count and
its exact resulting history. The existing original-calculus fragment theorem
then proves completeness for every actual `Prov G a` derivation. All witness
existence arguments remain in Prop; they do not select data into the executable
program.

The large local line program occurs once in the scanner step. A fixed
argument block stores its result, and the small branch classifier compares
that coordinate with one. The complete program is constructed from supplied
pairing, arithmetic, branching, composition, and primitive-recursion data.
`program_primrec` follows from this actual code value.

## Size and validation

Dedicated checks prove the tree-node counts below with Lean `decide` and
exercise guarded missing references, reversed premise order, extra/missing
parent cells, invalid tags, empty histories, unconsumed input, malformed first
lines, and the actual supplied programs on small rejecting inputs. Universal
proofs provide the positive binder and complete-proof certificates; the huge
canonical numeric evidence is not executed in runtime tests.

| Supplied program | Nodes | Optimized nodes |
| --- | ---: | ---: |
| Three-premise parent checker | 1101 | 1053 |
| Rule-side checker | 597 | 573 |
| Complete local line checker | 24589 | 22715 |
| Complete logical scanner | 24891 | 23017 |

All four main modules and four dedicated checks compile with no errors or
warnings. The checks contain eight proved size equalities, twenty-three
successful runtime controls, and forty-seven printed axiom audits. Every
audit uses only `propext`, `Classical.choice`, and `Quot.sound`, or fewer.

These are exact supplied program-tree sizes, not Diophantine variable counts,
polynomial operation counts, or measured whole sealed-ZFC checker sizes.

## Remaining boundary

This closes numeric logical proof execution, including the actual context and
binder side conditions. It does not yet check that the goal context consists
of sealed-ZFC axioms. The separately checked separation, replacement, and
sealing programs still need a finite axiom-tag dispatcher and complete
context-list validation before this route yields a new numeric sealed-ZFC
refutation checker. No consistency equivalence or new smallest polynomial is
claimed from this checkpoint alone.

All results here concern external natural codes. Interpreting syntax and
these bounded local arithmetic conditions over arbitrary internal omega codes
still requires explicit model-level coding and rule-correctness arguments.
The checked internal semiring operations do not automatically transfer the
external scanner theorems to nonstandard formula codes.
