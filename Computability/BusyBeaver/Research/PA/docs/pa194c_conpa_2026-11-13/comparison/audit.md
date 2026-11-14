# PA194C: comparison and mathematical audit

## Scope and repository identity

The audit is pinned to ProveIt commit `b88235336c63a247852fe8ec7f931d51f953632d`.
The earlier PA194 packet contains a comprehensive census pinned to
`5ed5a41fa5932433111eea096311364c6087e8e3`. GitHub's exact comparison between
these revisions reports 24 commits, no changed direct PA `.tm`/`.txt` tables,
and precisely two net incoming-archive additions: `pa194_conpa_2026-11-13.zip`
and `pa195_followup_research.zip`. All 32 earlier archives remain byte-identical.
The complete changed-file list is retained in `commit_range_comparison.json`.
This is a commit-range comparison, not an inference from modification dates.

The current inventory is therefore computed incrementally: retain the frozen
baseline inventory and freshly parse both added archives. Each new archive's
bytes match its Git blob SHA and listed size. The script uses exactly the
baseline's numeric-table recognition and graph serialization conventions.
The earlier 32-archive scan was not rerun in this audit.

| Quantity | Inherited baseline | Current snapshot |
|---|---:|---:|
| Top-level archives | 32 | 34 |
| Distinct archive byte payloads | 45 | 47 |
| Archive references, including nested copies | 73 | 75 |
| Member occurrences in distinct payloads | 25,069 | 25,742 |
| Complete numeric binary table occurrences | 2,360 | 2,473 |
| Byte-distinct complete tables | 582 | 594 |
| Classified root-free action-labelled graphs | 421 | 430 |

The fresh delta contributes 113 table occurrences, 12 new byte strings, and
nine graph classes. These totals include ancestors, experiments and rejected
tables. They are not counts of proved consistency constructions. Two
disconnected synthetic controls are outside the graph classification.
Tables appearing only inside code or JSON are outside the recognizer.
The two controls smaller than 194 states in the inventory are synthetic,
not consistency constructions.

At 194 states the current corpus contains five literal tables representing
three graphs: PA194, PA194_AD, and the explicitly rejected scanner194.
At 195 states it contains 17 literal tables representing eleven graphs.
The latter extend the old nine classes with M195S8 and the supplementary
`search/quotientcross.best.tm` endpoint. The supplementary table is included
in the inventory without treating it as a newly reverified PA endpoint.
`archive_ledger.csv` covers all 34 archive contributions and distinguishes
inherited descriptions from the two freshly inspected additions.

## The important frontier

| Family | Fixed controls + AX readers - folds | Source sites | Source outcomes | Blank startup |
|---|---:|---:|---:|---:|
| Original PA195 | 134 + 68 - 7 | 3,700 | 4,815 | 58,154 |
| 195S | 134 + 67 - 6 | 3,673 | 4,780 | 58,154 |
| 195C | 134 + 67 - 6 | 3,649 | 4,749 | 57,922 |
| M195S8 | 135 + 68 - 8 | 3,700 | 4,815 | 59,164 |
| PA194 | 134 + 67 - 7 | 3,673 | 4,780 | 58,154 |
| PA194_AD | 134 + 67 - 7 | 3,673 | 4,780 | 58,122 |
| New PA194C | 134 + 67 - 7 | 3,649 | 4,749 | 57,922 |

The complete hashes and graph fingerprints are in `frontier_comparison.csv`.
The new dense PA194C table has SHA-256
`d759313c03b515293fe06b12769fa1771d3829a2bad89febaa9b4391990f3a4b`.
Its root-free graph fingerprint is
`b79f4d344740679b87dace02fe3f211565c2cd4513f346812570d90caa3d9a3f`;
the fingerprint after left/right reflection is
`71527a184939733fbe62da7989ffbdedbecadf4e279d100b01018c93145aaf35`.
Neither occurs among the current corpus's 194-state classes, including the
rejected table. Every one of its 194 working controls reaches the full graph.
Thus it is distinct under arbitrary control renaming, redesignating the root,
and global tape reflection. This is graph novelty within the stated corpus,
not a claim about all uninspected constructions elsewhere.

## Why the new design is materially different

PA194 and PA194_AD implement the same 3,673-site source; their difference is
physical register placement. PA194C instead composes the successful PA194
reader allocation with the cached-head controller previously implemented
by 195C. It changes two command functions and removes 24 primitive source
instructions. Its full 3,649-site source graph agrees with 195C's graph.
The change therefore has an operational explanation beyond a new control
numbering or storage permutation. The axiom calculus remains the same.

Write a command store as `(t,w,d,h)`, with Cantor stack projections `hd,tl`,
and let `I(a,b)=4 pair(a,b)`. PA194C's Shift is

    S(t,w,d,h) = halt                          if h = 1,
                (h,tl(w),d,hd(w))              otherwise.

For `y=d+x`, its MP command is

    MP_x(t,w,d,h) = (0,w,0,y)                   if I(t,y) = h,
                   (0,w,y,0)                   otherwise.

Neither MP branch pushes a stack entry. Only Shift halts. In particular,
Shift tests the cached formula alone instead of the old `t+h=1` predicate.
On the store `t=1,h=0`, the old predicate halts while this Shift does not.
Such a difference in the command function cannot be explained by mere
renaming while preserving this register interpretation.

## Command correctness and the ten-entry emitter

The full source is preserved in the supplied
`independent_verification/composite_command_audit.tex`; the selected copies
and exact hashes are in `proofs/provenance.json`. The separate-head AX emits
ten entries including the saved top. Above that saved top are the separately
pushed diagonal axiom, the six ordinary heads, the dominated propositional
head, and `U(d,h)`. All generated entries and the guarded gate differ from
code one: their tags are zero or two modulo four. AX clears `d,h`.

The correct ten-entry stack words are:

    Push    = AX(0,0,0); S^9; MP(0)
    Pop     = AX(0,0,0); S^11
    Discard = MP(1); AX(1,0,0); S^10; MP(0)
    Gen_i   = Push; Offset_i; S; AX(i,0,0); S^10.

Here Offset_0 is empty, and Offset_i is MP(i) for positive i. Push saves
the old top and clears the visible top and caches. Pop preserves its top
and removes one underlying entry, except that it halts exactly when that
preserved top is one. Discard clears the top from zero-cache stores.
Gen_i maps `(a,w,0,0)` to `(U(i,a),w,0,0)`, including the case `a=1`.
The nine-entry selectors cannot be reused with their old exponents.

The new MP suffix is `S;S;MP(b);S`, with exact precondition

    (0,[a,I(a,b),0;w],0,0).

It halts if `a=1` or `b=1`; otherwise it returns `(b,w,0,0)`.
The dummy zero entry is essential: it is consumed by the final Shift.
Omitting it consumes part of the protected underlying stack.
All identities use total Cantor projections and explicitly include the
alias `pair(0,0)=0`. They do not assume a syntactically stored stack length.

Induction on a proof tree yields a primitive-recursive compiled word W_p
which, from any top and underlying stack with zero caches, either halts
or returns its conclusion with that same underlying stack and zero caches.
For an MP node, Discard followed by Push supplies the dummy zero; compiling
and pushing the major and minor premises establishes the suffix precondition.
For a proof of code one, `AX(0,0,0);W_p;Pop` halts from every incoming store.
This universal incoming-store property allows the existing exhaustive
scheduler to retain arbitrary stores between unsuccessful command trials.

For soundness, annotate the top, cache, and canonical decoded stack entries
with numerical-calculus derivations. The offset needs no annotation. A
single fixed derivation of code zero handles every requested zero padding
entry. AX emits axioms or generalizations of the old proved cache; successful
MP derives the new cache; failed MP returns zero; Shift moves derived
formulas and halts only when the cache is a derivation of one. Consequently
source halting is equivalent to a numerical-calculus refutation.

This command algebra was freshly replayed: 164 symbolic cases for the
nine-entry variant and 188 for the ten-entry variant passed, including
opaque arbitrary stack tails, zero aliases, all selectors, and early halts.
These finite symbolic checks support the written universal proof and do
not replace it.

## Binding the changed commands to the source

For the separate cached controller, the source has N=3649 instructions.
The MP success entry is 3634, the fetch return is 3637, and Shift begins
at 3638. The prefix before 3634 agrees with the old separate source except
for three retargeted exits: site 48's zero branch, the AX return at 3553,
and the MP-prelude return at 3633. The source-binding checker was freshly
replayed and passed for both the diagonal and separate layouts.

The 15-instruction tail has elementary arbitrary-value loop proofs.
Successful MP transfers `D=y,H=0` to `D=0,H=y` in `3y+1` instructions,
then returns to fetch in one more. Failure returns directly in one.
Shift clears the old top in `2t+1` instructions, copies H to T and scratch
X in `4h+1`, then restores H from X in `3h+1`. Thus `(T,H,X)=(h,h,0)`
after `2t+7h+3` instructions. Two final instructions set X=1 and enter
the unchanged guard; that guard tests H=1 and otherwise calls the total
Cantor decoder. These are inductions on arbitrary natural values, under
the inherited zero-scratch command-boundary invariant.

For new PA194C, the full source graph equals the supplied 195C graph.
The first physical checker passed all 4,749 source outcomes, all 28 local
fold cases, and whole-tape initialization after 57,922 steps. Its symbolic
counter was 1,507,397, maximum 506 per case. Independent literal verification
is recorded separately by the construction owner; this memo does not infer
its result from the first checker.

## Arithmetic calibration and its scope

The command transformations, source loop traces, finite table checks and
positive physical instruction simulations admit primitive-recursive trace
or proof constructors with PA-verifiable correctness. A finite source halt
therefore produces a literal tape halt. Conversely, if a literal halt
occurs at time T but the source has not halted among its first T+1
instructions, positive simulated segments produce a longer nonhalting tape
prefix, contradicting deterministic execution. This supplies the reverse
finite-trace direction without assuming eventual nonhalting.

Composing with the inherited separate-head calculus's two syntactic
PA-refutation translations gives the ordinary mathematical PA biconditional.
No new complete Lean or Rocq kernel endpoint is claimed. The repository's
still-open iPRA reductions are a stronger formalization objective and do
not alone refute this ordinary PA-preservation argument.

## Rejected reductions and related ideas

The follow-up scanner194 has valid local folds and an unchanged source CFG
but fails its physical source contract at ordinal 1003: a seven-zero source
address is mistaken for the separator. A one-control scanner repair yields
M195S8. This is why all simultaneous folds, the source CFG, arbitrary-register
physical contracts, and complete initialization are checked separately.

The ZFC `candidate-k217/research/cache-return/README.md` describes the same
useful architectural idea: replace a successful-MP suffix by a transfer of
the conclusion into the cache. Its documented experiment keeps 217 controls
and explicitly lacks a fresh full modified runtime; it is not an independent
state saving available to subtract. PA194C uses the already documented PA
cached controller and supplies the fresh physical composition checks.
Concise iPRA proof-checker size is a different objective from binary-TM state
count, and replacing the PA calculus by iPRA would require a new PA calibration.

Concrete further questions are whether the changed helper rows allow eight
compatible folds with 67 readers, whether 66 readers can retain seven folds,
whether a joint helper-and-reader replacement beats pairwise contractions,
and whether the existing source/quotient proof libraries can internalize the
exact new table with a small reusable certificate checker. A shorter scanner
must be justified on every source and transient runtime frame, not merely
on interior AX addresses.

## References

- Exact repository delta: https://github.com/VladimirReshetnikov/ProveIt/compare/5ed5a41fa5932433111eea096311364c6087e8e3...b88235336c63a247852fe8ec7f931d51f953632d
- Current PA overview: https://github.com/VladimirReshetnikov/ProveIt/blob/b88235336c63a247852fe8ec7f931d51f953632d/Computability/BusyBeaver/Research/PA/README.md
- PA194 packet: https://github.com/VladimirReshetnikov/ProveIt/blob/b88235336c63a247852fe8ec7f931d51f953632d/docs/incoming/pa194_conpa_2026-11-13.zip
- Cached-controller source and proof: https://github.com/VladimirReshetnikov/ProveIt/blob/b88235336c63a247852fe8ec7f931d51f953632d/docs/incoming/PA195_ConPA_research_2026-11-14.zip
- Scanner follow-up: https://github.com/VladimirReshetnikov/ProveIt/blob/b88235336c63a247852fe8ec7f931d51f953632d/docs/incoming/pa195_followup_research.zip
- ZFC cache-return study: https://github.com/VladimirReshetnikov/ProveIt/blob/b88235336c63a247852fe8ec7f931d51f953632d/Computability/BusyBeaver/Research/ZFC/candidate-k217/research/cache-return/README.md
