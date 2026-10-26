# Shared validated coordinates and all seventeen rule schedules

This checkpoint supplies literal primitive-recursive data for checking shared
rule coordinates and computing the exact output and ordered premises of all
seventeen rules in the existing `AnnotatedProofChecker`. Accepted raw
coordinate codes determine actual formulas and an actual context. No formula
or context parser premise is assumed.

## Shared coordinate validation

`AnnotatedRuleCoordinates.Coordinates` has ten natural fields:

```text
G, shiftedG, A, B, C, instI(A), instJ(A), shiftedC, i, j.
```

The names denote codes rather than trusted syntax. `allE`, `exI`, and
`eqRefl` use index `i`; `eqElim` uses both `i` and `j`. Two nested instances
of the frozen six-field row codec encode the coordinates. The final inner
tail is unused, so the soundness theorem also covers noncanonical raw
packet codes.

Five certificates validate a packet:

- The complete context scanner certifies an actual context and its exact
  `map (rename Nat.succ)` output.
- One bound table validates the raw `B` formula code.
- Two instantiation tables certify `A` at indices `i` and `j`.
- One shift table certifies `C` and its shifted code.

The first instantiation table already proves that raw `A` denotes an actual
formula. The `C` shift table does the same for raw `C`. Therefore no additional
bound-table validators for `A` or `C` are introduced.

`check_sound` and `program_sound` prove that every accepted raw packet is
exactly a quotation of some actual `G`, `A`, `B`, and `C`, including all three
claimed rename results. Conversely `check_complete` and `exists_program_iff`
provide accepted finite evidence for every such actual quotation. Witness
existence is established in Prop; no witness is selected into executable
program data.

## Exact literal rule schedules

`AnnotatedRuleSchedules` uses tags in the frozen constructor order:

```text
0 ass      1 impI    2 impE    3 botE    4 lem
5 andI     6 andE1   7 andE2   8 orI1    9 orI2
10 orE    11 allI   12 allE   13 exI    14 exE
15 eqRefl 16 eqElim.
```

`outputBody` and `premiseBodies` are literal natural arithmetic constructor
schedules. `output_quote` proves exact equality with `judgmentCode` of the
original rule output. `premises_quote` proves exact equality, including
order, with the original premise list mapped through `judgmentCode`.
These are universal theorems for every actual context, all three formulas,
and both indices, checked separately for all seventeen tags.

The schedules include the actual shifted-context premise for `allI`; both
the shifted context and shifted conclusion in the second premise of `exE`;
and the `inst i` premise / `inst j` output distinction in `eqElim`.
`ofRule` is a literal Type-valued embedding of every original rule into the
shared coordinate format. It uses bottom in unused formula positions and
proves exact output/premise recovery for every original rule.

`ArithmeticFiniteSwitch` compiles a fixed finite collection of supplied PR
bodies into a literal selector. Untrusted tags outside the supplied range
return zero. Its construction takes actual body-program data; it does not
extract programs from a primitive-recursiveness proposition.

The output and premise selectors are supplied `ScalarPRCode` values.
`programs_sound` connects their actual evaluations on any validated raw
coordinate packet to an actual original rule. `programs_complete` supplies
a successful coordinate certificate and the exact two selector outputs for
every original rule. A separate literal `tagProgram` classifies `tag < 17`.

The schedules alone do not check rule side conditions or parent references.
Their semantic theorems use a validated `Fin 17` tag. A complete numeric line
validator must enforce the tag classifier, the assumption-rule membership
condition, and the required backward parent judgments before applying
`Rule.sound`.

## Certified sizes and tests

Lean `decide` proves these counts for the actual supplied program trees:

| Program | Nodes | Optimized nodes |
| --- | ---: | ---: |
| Shared coordinate validator | 17371 | 15933 |
| Output selector, all seventeen rules | 2537 | 2377 |
| Premise selector, all seventeen rules | 2683 | 2483 |

These are separate program sizes, not a measured full-checker size or a
compiled polynomial size. No consistency equivalence or size improvement
over the closed baseline is inferred from these counts.

Dedicated checks verify the generic finite selector at valid and invalid
tags, raw zero rejection by the coordinate validator, the exact premise
arities of every rule, both actual selector evaluations at all seventeen tags,
and rejection of invalid tags. Universal theorems provide the positive
coordinate certificates; those enormous canonical numeric scans are not
executed in runtime tests.

## Remaining interfaces

Still separate are the rule-side and guarded parent-reference checks,
composition into a whole line scanner, the numeric sealed-axiom dispatcher,
and a complete new primitive-recursive refutation-checker program. The
previous standalone assumption validator already has exact raw soundness
and agreement with the original assumption line.

All theorems in this checkpoint concern external natural codes. Their
interpretation over arbitrary internal omega codes still requires explicit
coding and arithmetic correctness proofs in the model. The existing
internal semiring and polynomial arithmetic results do not automatically
transfer an external formula-code or checker theorem to nonstandard codes.
