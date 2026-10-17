# Instruction proofs for the 252-state permutation candidate

The new candidate's instruction proofs use its literal 252-state table.
The register permutation changes physical selectors while retaining every
logical instruction of the original proof-search program. The complete blank
bootstrap and four register operations are already checked; see the
[frozen candidate](candidate-permutation252/README.md).

[SymbolicPerm252](symbolic_perm252.md) proves the affine symbolic executor
sound for actual binary execution, with arbitrary natural gap parameters and
arbitrary physical spare blocks. Its balanced transition lookup has a proved
identity with the literal table. The checker requires positive literal
progress and retains the final write and head movement of a halting step.

`SitePerm252.lean` constructs the source and target of each logical operation.
Logical registers are mapped through the checked permutation. A decrement
checks both branches, each guarded by the value of that same physical register.
Overflow increases the marker-to-header distance by one; the logical path
keeps its full all-zero suffix. Paths longer than 40 and register operands
outside the nine primary registers are rejected.

The [clean-path and framing proofs](permutation252_simulation.md) turn an
actual dispatch frame into the source representation and recover the entire
successor frame. Consuming a path may extend it with zeros from its existing
gap. The remaining physical file, including every spare block, stays in the
representation. Positive decrement appends a zero spare.

`InstructionPerm252.execute_frame` composes these proofs: an accepted site
and a successful logical instruction imply a positive number of actual binary
steps to the exact logical successor's whole-tape frame. `halt_frame` proves
the halting case. These statements quantify over all admitted files and gaps;
they do not follow from sampling executions.

The site source passed pinned Lean 4.32.0 in 0.66 seconds, and its audit passed
in 2.19 seconds. Eight actual leaf examples cover ten conditional cases,
including every operation and all three overflow cases. Three rejection
checks cover an invalid register, an excessive path length, and a wrong logical
register at an actual increment site. The instruction-composition source
passed in 0.60 seconds. Their axiom dependencies are `propext` and `Quot.sound`.
Exact sources, commands and scope are preserved in the
[site record](results/permutation252-sites-verification.json) and
[instruction record](results/permutation252-instruction-verification.json).

The [global runtime composition](runtime_perm252.md) is also checked. Given
complete decoder coverage, it proves halting equivalence using the clean-path
invariant and positive binary progress. The literal zero-root program has
separate checked equivalences with `C254 F` and native-theory refutation.
The [118-unit integration check](results/permutation252-runtime-integration-verification.json)
composes these with the actual blank bootstrap; its final caller retains the
coverage premise. All imported sources match their scoped successful checks;
the integration freshly checks the umbrella and callers, not all 118 sources.

The complete 6,460-leaf/8,391-guard decoder certificate remains a separate
running check. The standard-ZFC consistency comparison and its arithmetization
remain separate from this conditional machine endpoint.

The site construction and path semantics are adapted from Mira-Cult's machine,
Jeff's verification and Wade's compiler framework at upstream commit
`297ab8df7e5de329605c3875b4934643b371a5e3`. All new proofs here use Lean.
