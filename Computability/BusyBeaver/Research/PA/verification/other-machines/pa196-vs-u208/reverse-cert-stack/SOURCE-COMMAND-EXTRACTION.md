# From source halt toward command-level certificate extraction

The imported PA196 arithmetic scheduler contains substantially more
all-model source/command machinery than the basic forward physical lift.
This note spells out how it could be used in the reverse direction. The
strengthened bounds and reverse implication below have **not** been proved
in PA or exported as theorems in this repository.

For a PA model, write `c` for a coded source configuration, `s` for its
coded four-field command store, and `0` for the halted command state. The
exact relation
[`CommandRelation`](../../jamesyc-upstream/pa196/PA196/Arithmetic/Scheduler/InternalCodedSourceCommandRelation.lean)
says either that both the command state and source control are halted, or
that the source is at encoded root control 26 with a valid clean register
file whose four command registers encode `s`. In particular, if `s != 0`,
only the live root case is possible; this does not rely on an external
standard-number computation.

The imported theorem
[`source_candidate`](../../jamesyc-upstream/pa196/PA196/Arithmetic/Scheduler/InternalCodedSourceCandidate.lean)
refines one whole enumerated command candidate: from a related source root
at candidate index `n`, it produces a model-length source trace and a related
result `candidateRun(n,s)`. When `s != 0`, its proof first invokes
[`root_fresh_command`](../../jamesyc-upstream/pa196/PA196/Arithmetic/Scheduler/InternalCodedSourceRootCommand.lean),
which supplies a **positive-length** source trace, and then appends a
possibly empty consume trace. Thus a useful strengthening of
`source_candidate` is available from the existing proof: add the conclusion
`0 < k` when `s != 0`. This is not claimed as an already-stated theorem.
The separate `candidateRun_halted` theorem states that `candidateRun(n,0)=0`.

[`source_from`](../../jamesyc-upstream/pa196/PA196/Arithmetic/Scheduler/SourceEnumerationSuffixInduction.lean)
already iterates `source_candidate` by full PA induction for a model-valued
number of candidate rounds, starting at an arbitrary candidate index. The
actual entry frame starts enumeration at index 2; this is the same convention
used in [`refutation_root_two_halts`](../../jamesyc-upstream/pa196/PA196/Arithmetic/Scheduler/SourceEnumerationFromTwo.lean).
Let `E_i = fromValue(2,i,s0)`, where `s0` is the command store in the exact
entry frame. If `E_j != 0` for all `j <= i`, the positive strengthening
above suggests strengthening the existing induction to produce a source
trace of length `K >= i` ending in a configuration related to `E_i`. Its
induction formula must explicitly retain the length inequality and the
nonhalt assumption. If `E_i != 0`, all earlier `E_j` are nonzero as well,
because `candidateRun(n,0)=0`; this fact also needs the bounded internal
induction, not an external argument over standard indices.

Suppose an independently obtained coded source trace of length `N` from the
same entry frame ends in source control 0. If `E_(N+1) != 0`, the strengthened
iteration yields a second source trace of length at least `N+1` whose endpoint
is live. But coded source execution uses the function `stepValue`, and
`stepValue` is absorbing at source control 0. PA-internal induction comparing
the two coded sequences would make the later endpoint halted, a contradiction.
Consequently the desired intermediate conclusion is

```
fromValue(2, N+1, s0) = 0.
```

This argument avoids trying to interpret a partial source macro at the exact
halt instant. To make it a PA theorem, one must prove the positive candidate
bound, the length-strengthened source iteration, the initial `CommandRelation`
for the precise startup store, and comparison/absorption for the represented
model-length source sequences. The imported `source_from` theorem does not
itself include the required lower bound or establish the displayed converse.

Finally, unpacking the zero result requires a proof-carrying induction over the
scheduler's actual `candidateRun` and `consume` functions. These execute
`CommandStep.stepValue` on the decoded command atoms; their zero cases and
absorbing behavior must be handled exactly. The
[concrete certificate inventory](imported-checker/README.md) provides the
per-command checker constructors, and the [conditional command note](COMMAND-EXTRACTION.md)
provides the invariant. A represented iteration should retain certificates
through every model-length command run and return an accepted proof of code 1
when the command state first becomes zero. This is still an obligation: the
forward `source_consume` theorem alone does not furnish the reverse
proof-carrying statement, and no PA refutation translation follows merely from
an accepted native checker code.
