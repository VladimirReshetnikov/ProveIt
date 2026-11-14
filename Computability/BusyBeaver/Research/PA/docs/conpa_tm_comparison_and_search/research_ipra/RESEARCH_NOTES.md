# Logical review and additional source searches

## Outcome and source pin

**No correct binary blank-tape Turing machine with fewer than 196 working
states was constructed by this branch of the research.** All files describing
a 195-state quotient in `newsearch/` are diagnostics for a rejected table.
They must not be presented as a solution or as an established simulation.

The concrete baseline is `jamesyc/BusyBeaver` at commit
`407cdc356f6b586635e71ac92be394255f4bfea4`. The pinned literal table has SHA-256
`e8bbccd4cfa325251ca95066db116b5aa766e404b0971c33c02772be1c3617a8`.
The inherited checker and source-grammar infrastructure used in these searches
comes from the ProveIt incoming archive `pa_tm_research_2026-11-13.zip`.
The new search scripts and logs in this directory are separate from that
previous research. They are heuristic searches or bounded checks, not lower
bounds on machine size.

## Mathematical contributions

`reflexivity_barrier.md` gives a complete mathematical obstruction to replacing
the equality-existence head by equality reflexivity. An explicit primitive
recursive Boolean interpretation validates every modified head, every
guarded gate, MP and generalization while making contradiction code 1 false.
PA can verify this interpretation and prove the modified calculus consistent.
Thus, assuming PA consistent, its consistency cannot be PA-provably equivalent
to Con(PA). The exact numerical zero alias and code 1 are handled explicitly.

`check_reflexivity_barrier.py` supplies bounded regression checks of the exact
numeric coding. `reflexivity_barrier_check.json` records 384 modified-head
instances, 36 guarded-gate instances, 1024 instances of each constructor identity,
and all 16 Boolean instances of the propositional head, all passing. The largest
tested formula code has 7,681 bits. These computations do not replace the
universal mathematical proof.

`h1_bootstrap_constraints.md` gives a different Boolean countervaluation
showing why several attempted replacements of the first head cannot recover
the old explosion bootstrap. It does not overstate this as a consistency
lower-bound theorem. The note also proves noncircular recoverability of the
safe first-head weakenings used by the search, and explains a concrete
completeness obstacle for the shorter fresh-label head.

`internal_reverse.md` is a detailed **proof strategy**, not a completed new
internal PA theorem. It describes a syntactic PA proof compiler using bounded
bit comprehension for arbitrary inserted formulas, handles the gate's index
collision a=b and its code aliases, and explains positive progress. An
independent review identified four remaining formal bridges: exact syntax and
provability coding; uniform proof-checker correctness; complete source/tape
contract arithmetization; and an internal connection to the repository's exact
padded/beta trace sentence. Standard-model truth equivalence and external Lean
nonhalting do not discharge the last obligation.

The ConciseIPRA README was inspected at blob
`5526b516e20d61d89c1a1575744d35742f669efd`. Its compact equation-induction
theories cannot simply replace the PA checker while preserving the target
consistency statement. An all-formula-induction extension remains only a
suggested research direction.

## Physical rotations and the rejected195-state quotient

`newsearch/rotation_search.py` enumerated 56 local pure-selector rotations;
40 preserved the exact resolved source control-flow graph. A rotation at
native states 1362 and 1361 makes the two rows of 1361 equal to those of 1324.
The resulting 195-state quotient is incorrect.

There are two distinct issues:

1. The first rotation creates a seven-zero address run. Its universal check
   has 95 failing primitive contracts, beginning at site 3502.
2. A second rotation at 1363 and 1362 fixes that scanner issue but leaves 93
   failing contracts, beginning at site 3584. Reader 1355 represents logical
   roles x23 and x55 using the preceding bit; the new x55 paths no longer have
   the required history class. Some x23/x55 paths cannot be distinguished by
   any suffix of six preceding bits.

The first patch and all 95 failures are in `newsearch/rotation1362.json`.
The two-rotation raw table and new source sites are in
`newsearch/repairbase.json`. The independently rerun all-contract rejection is
`newsearch/rejected195_audit.json`: 4,959 contracts examined, 93 failures,
unchanged resolved source CFG, and 195 states after the identical-row quotient.

The error is in the unvalidated tree rotation, **not** in the ordinary
identical-row quotient operation. Quotienting two genuinely identical rows
preserves the behavior of that altered machine; it does not make an already
incorrect alteration implement the desired source program.

`newsearch/safe_rotations.py` fully checked 13 eligible CFG-preserving rotations
outside the AX area. Only `(100,174,0)` passed all 4,959 contracts. Its subsequent
bounded search through depth 4 did not produce a reduction. The passing first
rotation is listed in `newsearch/safe_rotation_receipt.json`; the log records
the depth frontiers. This is not an exhaustive search over arbitrary source
reassociations or table changes.

## Logical-word and grammar searches

The unchanged part of the architecture costs 134 states. A score below 62 for
the AX area would therefore be a reason to attempt a 195-state table.
The reported score is a **screening score**, not a validated implementation
count: it is the raw AX DAG node count minus a maximum matching of advertised
single-step history folds, with path-length penalties. Joint fold compatibility
and full symbolic checking must still be established. No new logical word
scored below 62, so none produced an accepted smaller physical table.

| New family | Screened words | Best original-dictionary cover | Best observed AX score | Search status |
|---|---:|---:|---:|---|
| Insert I(0,X) at one gate-subformula site |53|69|63|Completed 150 annealing cycles of 1,200 trial slots after transport |
| Equivalent gate conjunction arrangements and internal antecedent swaps |96|68|62, attained by original gate; best changed word63|Stopped after 101 complete annealing cycles |
| Safe h1/h5 weakenings with parameter permutations |612|69|64|Stopped after 56 complete annealing cycles |
| Exact PUSH0 padding, selective nonempty subsets |255|72|No competitive assembled candidate|All dictionary screens completed |

The original-dictionary cover is only the result of a bounded beam heuristic,
not a minimum grammar size. A globally transformed tree can have a smaller
cover in another dictionary. In particular, replacing every PUSH0 leaf by
PUSH0;PUSH0;C has 70 raw nodes under direct transport of the original tree, but
violates the existing six-zero path bound in the tested association.

The numerical padding identity is exact: after PUSH0, the accumulator is 0;
the added PUSH0 stores 0, and C pops it and computes I(0,0)=0, restoring the
same accumulator and stack. The safe logical weakenings retain the original
first head through pure implicational proofs before using its explosion
lemma. Their exact recovery arguments are in `h1_bootstrap_constraints.md`.

Scripts, logs and per-word receipts are in `newsearch/`; machine-readable
word inventories are in `newsearch/wrappers/`. A preliminary double-negation
wrapper search reached score 64 and was discontinued in favor of the fuller
subformula and conjunction searches. No claim of exhaustive optimization is
made for these local annealing searches.

## Reproduction and packaging

The mathematical regression checker uses only Python's standard library.
The source searches use the inherited `core.py`, `grammar.py`, `layout.py`, and
`logical_variant_search.py`, plus the pinned BusyBeaver source files. In the
assembled deliverable these dependencies are supplied under `support/`;
source paths must resolve to that pinned snapshot. The raw working scripts
were initially run against the shared research workspace, so the packaging
step must rewrite their import roots. The complete report's offline entry
point is the preferred reproduction interface.

`STATUS.json` records the bounded search outcomes and the rejected candidate.
Nothing in this directory supplies the user's requested sub-196 construction.
