# PA-equivalence and ConciseIPRA audit

## Frozen sources

The current BusyBeaver checkout inspected here is at commit
`407cdc356f6b586635e71ac92be394255f4bfea4`.
The ConciseIPRA README fetched through GitHub had blob SHA
`51494028f38efd05a0f76337bd16b4d32c5608fa`.

## What upstream actually proves

`docs/result.md` lists:

- Literal 196-state, 392-row machine.
- Blank startup in 58,154 steps.
- Standard-model nonhalting and a closed Lean nonhalting theorem.
- `PA196.Arithmetic.pa_proves_nonhalting_consistency`:
  PA proves Nonhalting -> Con(PA).
- Two-sided independence, with consistency used for nonprovability of
  nonhalting and standard-model soundness used for nonprovability of halting.

It does not list a PA proof of Con(PA) -> Nonhalting or of the biconditional.
`PA196/Arithmetic/RefutationHalting.lean` confirms the one-direction theorem:
all-model refutation-to-literal-trace correctness followed by completeness.

`PA196/Logic/Soundness.lean` and `FiniteModel.lean` establish external
soundness in hereditarily finite lists; arbitrary pointed separation is
proved by classical list filtering. This is not itself an internal PA
truth definition and cannot simply be quoted as PA proving consistency of
the machine calculus.

## No reflection obstruction to the converse

The missing implication should be proved syntactically. Decode numeric
formula codes, translate membership to a binary-digit relation and equality
to actual equality, and compile each calculus derivation into a PA proof.
Every translated gate has a uniform PA proof built from finite
comprehension using full induction on the formula being filtered. This
compiler is primitive recursive and its correctness is provable in PA.
This does not claim truth of all PA theorems: it asserts only the validity
of generated proof codes.

Full details and code-zero edge case are in `reverse_implication.tex`.
That file is manuscript mathematics and a formalization plan; no new Lean
compiler or checked PA biconditional is supplied by this subtask.

## Required proof obligations for honest reporting

1. Fixed formula translation tau and PR proof compiler J, including the
   exceptional implication code I(0,0)=0.
2. PA verification of all translated heads and the full guarded gate.
3. PA proof-code safety invariant for the actual command interpreter.
4. PA-internal transfer across total command/register/tape macros and
   startup, using positive continuation or an equivalent trace extractor.
5. Exact-table simulation theorem for any state reduction performed later.

The fourth obligation is mathematically elementary once the arithmetic
macro contracts are available: strong induction on a hypothetical halting
length, comparing it to the positive next-boundary trace length. Existing
files explicitly establish external machine/source equivalence and many
arithmetic forward macro contracts:

- `PA196/PhysicalEndpoint.lean`: `blank_halting_iff_source`.
- `PA196/CompilerCorrectness.lean`: `source_nonhalt_to_physical`.
- `M6/PositiveInvariant.lean`: `not_halts_of_positive_invariant`.
- `PA196/Source/Nonhalting.lean`: positive safe command boundaries.
- `PA196/Logic/CommandSoundness.lean`: exact store proof invariant, currently
  using external Derivation soundness to exclude the shift halt test.

## ConciseIPRA relevance

The native scalar core uses equations and Q/D binders; equality reasoning
and logical rules can be derived from a small iterator-based core. Newer
variants fuse evaluation with discharge, restrict transport sources,
reverse equations, and eliminate redundant clause fields. These are
concrete ways to reduce proof-checker branching or share code.

Its ordinary realization, however, has induction only for literal
equations, derives quantifier-free induction, and is bi-interpretable with
iPRA. The README explicitly describes usual iPRA with quantifier-free
induction. That result does not supply a refutation calculus for full PA.
The current PA196 soundness-to-PA translation specifically needs arbitrary
formula finite comprehension, whose proof uses full induction. A smaller
iPRA proof checker cannot therefore simply replace the present checker
while retaining the required PA consistency problem.

## Sources suitable for citations

- https://github.com/jamesyc/BusyBeaver/blob/407cdc356f6b586635e71ac92be394255f4bfea4/docs/result.md
- https://github.com/jamesyc/BusyBeaver/blob/407cdc356f6b586635e71ac92be394255f4bfea4/paper/pa196.tex
- https://github.com/jamesyc/BusyBeaver/blob/407cdc356f6b586635e71ac92be394255f4bfea4/PA196/Logic/Basic.lean
- https://github.com/jamesyc/BusyBeaver/blob/407cdc356f6b586635e71ac92be394255f4bfea4/PA196/Logic/Decode.lean
- https://github.com/jamesyc/BusyBeaver/blob/407cdc356f6b586635e71ac92be394255f4bfea4/PA196/Logic/FiniteModel.lean
- https://github.com/jamesyc/BusyBeaver/blob/407cdc356f6b586635e71ac92be394255f4bfea4/PA196/Logic/CommandSoundness.lean
- https://github.com/VladimirReshetnikov/ProveIt/blob/main/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/README.md
