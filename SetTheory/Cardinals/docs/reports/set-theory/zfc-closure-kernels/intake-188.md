# Batch 188: K218 and its source-context reduction

Source 144, **K218: a 218-state ZFC consistency machine**, is the priority
submission from `c4568161bf0eafeabc9e6f5a4a5c8c0a90c22f70`. It reduces the
complete blank-start machine to **218 working states and 436 rows**, retaining
the accepted classical calculus. **It is now the primary contender after fresh verification.** The new proof is ordinary and
formalizable in ZFC; an exact-table Lean or internal PA endpoint is not claimed.
The requested next target is **217 states or fewer**.

## Intake and provenance

The archive is `K218_Construction_2026-10-20.zip`, pinned to the exact K219
parent archive in `26d5de6d21fa354d50e0b84fe851c289925b8d72`. Placement
**`6ffbe92305`** accounts for all **99 members**: 64 new payloads, four existing
aliases, 18 batch aliases, one historical parent-archive alias and 12
archive-only main manuscripts, article inputs, PDFs or delivery README.
The [placement map](data/intake188-placement.json) gives every original name,
new `144-k218-` target and introduction-tree binding. New payloads comprise
three root files, 16 code files and 45 data files, copied from a fresh extraction
separate from execution copies. The longest Windows-prefixed path is 144.
The archive was retired in that same placement; its complete original remains
recoverable from Git.

This is an addition to the existing finite-refutation/encoding report, using
its reconciliation-note procedure. The host now has **144 sources**, while the
collection remains **290 reports**. The two failed-218 research arrivals
`253b3ff50e` and `f8ec6158f3` remain queued for batch 189: the user's explicit
priority for this claimed complete construction determined the intake order.
The host article and labels are unchanged. No existing correctness claim is
retracted; the smaller verified ordinary result supersedes the size benchmark.

The [attribution](144-k218-ATTRIBUTION.md) credits ChatGPT-assisted research
for Vladimir Reshetnikov's ProveIt project and distinguishes the new source
allocation/fold from the unchanged predecessor chain. Its inherited licences
and credits remain in the original archive. No new priority or relicensing
claim is added. The [reproduction guide](intake-188-reproduction.md) restores
all article inputs, including the formalism supplement, and the complete
nested predecessor chain. Flattened archival scripts and historical receipt
paths are not standalone reproduction paths.

## How the state is saved

The source is a tree of increment, guarded decrement, break, continue and halt
instructions. K219 has 4,744 primitive occurrences represented by 206 distinct
subtrees. The supplied intermediate grammar represents the **same instruction
word and complete guarded ordinal control graph** with 205 subtrees. This is
checked literal construction data, not an optimizer whose output is trusted.
Three different graph resolvers—address arithmetic, subtree intervals and
explicit continuation stacks—agree on every primitive and guard. Primitive-step
induction therefore gives identical register vectors and halt behavior for
all initial natural-register vectors.

That first allocation still needs 219 machine states: it separates two roles
previously sharing native 188. The decisive change reassociates five copies of
`((A,B),C)` to `(A,(B,C))`, where the blocks contain 26, 19 and 7 primitives.
All three have no escaping break or continue and contain no halt; closed
sequencing associativity preserves their behavior. The five intervals are
`[568,620)`, `[1260,1312)`, `[1935,1987)`, `[2892,2944)` and `[3208,3260)`.
Exactly 260 leaf addresses change. The DAG count stays 205, but native 188 now
has rows `0 R 166` and `1 R 12`, exposing a useful existing continuation.

In this unfolded 219 checkpoint, native 85 and 212 agree on scanned 0, both
performing `0 R 98`. On scanned 1,85 goes right to 12 and 212 goes right to 150.
Their unique incoming transitions write their identity on the preceding cell:
`155/0 = 0 R 85` and `177/1 = 1 R 212`.
The final construction redirects the latter to 85, deletes 212, and changes
`85/1` to `1 L 190`. Existing rows then recover the old continuation:

| Preceding bit | New route on scanned 1 | Old action reproduced |
| --- | --- | --- |
| 0 | 85 → 190 → 188 → 12 | 1 R 12 in three steps |
| 1 | 85 → 190 → 189 → 156 → 176 → 150 | 1 R 150 in five steps |

Both routes read only the preceding and current cells and write back their
original bits. The head ends one cell right; the entire exterior tape is
unchanged. The scanned-zero case agrees in one step. Unique incoming writes
establish the marker invariant on **every tape from state 0**, including startup.
An old prefix of length n with u uses of 85/1 and v uses of 212/1 expands to
exactly `n+2u+4v` steps. These nonempty, nonhalting blocks give both halting
directions by induction and determinism.

This global all-tape fold compares the **unfolded checkpoint** with K218.
It does not assert that all preceding allocation edits preserve arbitrary-tape
behavior of the original K219. The broader blank comparison uses source
control-graph equality, final runtime and complete startup separately.

| Accounting item | K219 | Intermediate | K218 |
| --- | --- | --- | --- |
| Distinct source subtrees | 206 | 205 | 205 |
| Internal subtree types | 183 | 182 | 182 |
| Physical state/source-role pairs | 184 | 183 | 183 |
| Physical decoder states | 169 | 169 | 168 |
| Additional shared roles | 15 | 14 | 15 |
| Other working states | 50 | 50 | 50 |
| Total working states | 219 | 219 | 218 |

There are 23 primitive types. The inherited open subtree `(CD6,CC2)` still
has two physical entries, 13 and 108; physical states and logical roles are not
interchangeable counts. Relative to the parent, 32 retained rows change,
state 212 disappears, and no state is added. All 4,743 internal source prefixes
have explicit decoder bindings, a separate obligation from arithmetic runtime.

## Verification and consistency calibration

The final runtime obligation has 6,167 guarded cases on 4,744 sites, including
both guards of each decrement. It quantifies independent arbitrary natural
primary registers, gap and first spare, and an arbitrary finite spare tail.
The exact whole tape, head, source successor, resource changes and absence of
premature halt are checked. The symbolic rules use literal transitions and
induction on unary runs and finite lists; the 4,000-rule proof-construction cap
does not restrict represented inputs or running time. The compact case JSON
is a receipt; full replay regenerates the derivations.

The fresh runtime has 1,515,158 rules, all 436 rows used and minimum duration
constant 12. Its fresh blank startup is 312,909 steps, reaching native 84 /
canonical 23, head −5, header 139, gap 80, registers `[3,0,0,0,3,0,0,0,0]`, and 130
value-one spares. Exactly 277 cells are one and all others zero. The earlier
clean-looking frame at 92,808 steps has a nonzero source PC and is not a valid
root-start endpoint.

All **six selected fresh jobs pass**: construction/source proof premises,
independent source/fold audit, native-sparse/canonical-dense startup, separate
blank startup audit, full final runtime, and independent runtime audit. The
[actual record](data/intake188-fresh-k218/actual.json) and
[evidence review](data/intake188-fresh-k218/review.json) preserve exact commands
and results. The full runtime took about 143 seconds. Source, machine,
canonicalization and case-array bytes reproduce the delivery. Runtime metadata
differs only in elapsed time and Python version; the first author-side evidence
reader's overstrict metadata comparison and its correction are preserved.
No submitted checker or evidence was altered to obtain the passes.

The [independent mathematical review](intake188-source144-review.md) is separate
from runtime execution. No omnibus wrapper, manifest suite, ancestor replay
or proof assistant was run. The parent calibration is an accepted dependency,
not a claim of a newly rebuilt recursive proof chain.

The exact source-step comparison transports the unchanged finite-refutation
calibration. Complete blank startup supplies the frame invariant's base;
positive finite primitive simulations supply its induction step and preserve
infinite source execution. Hence blank halting of K218 is equivalent to blank
halting of accepted K219 and then to existence of a finite ZFC refutation.
Negation gives **ZFC-provable blank nonhalting iff Con(ZFC)**. The equivalence
itself assumes no consistency statement or set model. No unconditional
nonhalting, minimality, ≤217 result or new exact-table kernel endpoint follows.

Canonical SHA-256:
`06d7a91c583739e17f8b33ce3e03d0aeaf9e1faa186c76d596418942fe2a8730`.
Native SHA-256:
`2dfaba6da09b78291e534777cd30c5f0d68bd84faa670e868e779c396aeb308f`.
Source SHA-256:
`b0169f2d477d0584ac70f9bdb79c3a78ef2bc700d080b3cd80976210235b80d9`.
Canonical states 0–217 work, 218 halts; the native start/dispatcher/halt are
0/84/254. The alphabet is 0/1, blank 0, moves L/R, one two-way infinite tape,
and initial state/head are 0. Initialization is included in the state count.

## Other retained ideas and their limits

The K/S-only implication experiment produced 204 and then 203 source nodes and
exposed the useful 85/212 pair. Its consistency calibration remains open.
The successful construction transfers its **encoding idea** to the original
classical calculus; no unfinished K/S premise enters the K218 theorem.

The supplement proves useful qualified logical facts. K plus retained B6
`¬Q_a¬Q_a A → A` yields explosion, and existential equality plus theorem
necessitation yields seriality. Double-negated persistence yields stability;
the native negative bundle supplies this for membership atoms. The merged
equality row supplies equality reflexivity and persistence without assuming
Peirce or an instantiation rule. These are ordinary derivations reviewed at
intake, not new proof-assistant declarations.

Atomic stability does not suffice to complete the proposal. The product of
two three-element Heyting chains provides a normal, serial B6 quantifier
with `¬¬(A→QA)=top` but unstable QA. A separate nine-element upset algebra
has commuting quantifiers whose double-negation Booleanizations fail to
commute on regular elements. The finite diagnostics refute those particular
proof steps, not consistency calibration of every K/S theory or the entire
native set-theoretic bundle.

In ordinary first-order logic, a witness-container scheme, existence of an
E-predecessor and one membership-congruence orientation imply E-reflexivity
and arbitrary Leibniz substitution. Apply the container scheme first to
`E(u,x)` and then to `E(u,x)∧θ(u)`; support transfers θ through selected
members. This does not justify deleting native equality machinery, which
also bootstraps the ordinary substitution and quantifier rules used by that
argument. The unresolved deletion proposal is retained as a research question.

The recorded finite search families remain scoped historical evidence:
all `6^8=1,679,616` parameter permutations in eight fixed logical rows have
minimum 205 subtrees, attained twice; 97 template nodes are root-reachable.
There are 40,320 axiom orders with 12 prescribed parses each, 1,024 bundle
rewrites with 12 parses and 16 antecedent-swap combinations with 12 parses.
None of these fixed families improves 205. They are not grammar or machine
lower bounds, and were not rerun merely to re-report their old measurements.

The rejected runtime-only 218 construction is also retained. Its valid-frame
runtime did not establish blank initialization: its literal blank prefix
reaches state 35/head 7 with ones only at −3,−2 after 85 steps, and `35/0=1R35`
then gives an infinite writing ray by induction. This is a proved failure of
that other table. It is not an objection to the separately checked final
K218 source/table/startup combination.

## Combinations and the next state saving

The row157 continuation rewrite carries over to K218. A fresh unchanged
independent checker passes 1,009,191 radius-seven contexts, including 1,408
nontrivial ones, with maximum old/new positive blocks 2/3; its initial-halt
negative control is rejected. This yields an additional 218-state layout,
with all-initial-tape halting equivalence, not another state saving or a
separate complete primitive replay.

The Source141 zero-terminal and 81-retag source transformations also fit the
new source and leave 205 subtrees. Their selected physical patches are
disjoint from the 32 K218 changes. That is a promising compatibility check,
not a proof that literal patch union implements the transformed source.
Full source/address and binary obligations remain necessary before adopting
those combinations. Deleting 301 with the earlier three-row helper patch
would give 217 states but retains the identical bad 85-step blank prefix;
it is explicitly rejected, not counted as a contender.

The [candidate publication](../../../../../../Computability/BusyBeaver/Research/ZFC/candidate-k218/README.md)
contains the readable construction and exact machine artifacts. Subsequent
searches toward 217 have their own fixed families and acceptance checks;
neither a small source count nor a bounded search hit substitutes for the
complete blank-start consistency comparison.
