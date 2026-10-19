# Prior-art and incoming audit — 18 October 2026

## Scope and pin

The current ProveIt checkout is pinned by the root at
`c539ed64bfad3fa5a059bf040b06b6c91ded680e`. The six incoming packages
were read from `sources/incoming/archive1` through `archive6`.
This is a source review and research synthesis, not a fresh execution of their
large search suites. Notes below distinguish current-tree facts from inherited
delivery-time facts.

The requested endpoint in this conversation is
`ZFC |- (not Halt(M,blank) <-> Con(ZFC))` with at most 245 working states.
The current repository README's allowance for stronger theories belongs to a
different prior clarification and does not replace this user instruction.

## Public upstream

Mira-Cult's 254-state table, formally verified by Jeff Ketchersid in the
`zf-254` branch, has external Rocq end-to-end theorems
`zf254_halts_iff_ZF`, `zf254_halts_iff_ZFC`, and
`zf254_halts_iff_SIR`. The upstream README reports no axiom dependencies
for those three results. The proof runs the final binary table directly;
it does not infer the result from the pre-fold table.

The wiki's opening bound still says 432 although its history table includes
254 (13 October 2026). Do not repeat the stale opening upper bound.
The wiki is secondary; use the explicit table and theorem sources as the main
technical sources.

## Present ProveIt baseline

The permutation252 table has a closed external Lean equivalence with
Con(ZFC). It is not by itself a serialized proof inside PA or a generic proof
that the Lean statement can be internalized in ZFC.

The 246-state context/pulse construction is genuinely distinct. Relative to
prefix250, surviving rows change:
- old60/read0: `0 R 0 -> 0 R 20`;
- old255/read0: `1 L 97 -> 1 L 255`.

Old states0,1,3,97 disappear. Start becomes old95; dispatcher is old96;
halt old254; old255 is a working state. Count working labels, not max label.
Canonical table: 246 states,492 complete rows, one separate halt action.

The ordinary fold map excludes old pairs
`(0,0),(1,0),(1,1),(3,0),(3,1),(97,0)`; it cannot transport the old blank
initialization. The new 410,735-step bootstrap is therefore essential.
It reaches old96 with head-5, marker-6, header176, gap181, primary physical
vector `[0,0,0,3,0,0,3,0,0]`, and167 value-one spares. Logical seed:
`(N,T,W,A,D,H,X,Y,L)=(3,0,0,0,3,0,0,0,0)`.
The existing six-nonformula-field theorem covers this seed.

The CURRENT README has advanced beyond the source63 intake:
- exact246 table and fast lookup are checked in Lean;
- logical seed is calibrated in Lean;
- pulse, unbounded boxes, and all nine selector contracts are checked;
- complete410735-step bootstrap and complete frame identification are checked;
- symbolic executor, per-site/frame/instruction soundness are checked;
- conditional binary/register runtime equivalence is checked.

The remaining exact246 formal runtime gap is the complete actual-decoder
coverage certificate, followed by final endpoint composition. Do not list the
already completed bootstrap/ports as still missing. Complete internal PA
comparison remains open; current internal arithmetic work reaches actual MP,
with AX/full internal interpreter/Enum/calibration still open.

## The six incoming packages

| Archive | Positive contribution | Exact sub246 obstruction/status |
| --- | --- | --- |
|1, below246 (2)| Root interval certificate; full unbounded direct replay; nine-state local arithmetic core; valid source reassociation | No new smaller machine. Nine-state arithmetic integration consumes PC return; blank enters a closed left trap after3 steps. Rotation 178=(23,(24,206)) to ((23,24),206) removes208 using16 but breaks borrowed binary contexts; one retiming preserves boot and still fails runtime. |
|2, below246 (3)|202-pair source with maximal zero run6; valid250 realization with shorter scanner, blank407983. Valid colored246 with unchanged410735 boot; obstruction count18->15.| Shortened colored245 fails30 guarded cases (both guards at15 decrement leaves). Separately source-certified protected frontier reduces obstruction count to5 but does not preserve all borrowed terminal handlers. |
|3, below246| Universal decrement-only245 macro; partial244 forward arithmetic; alternate full246 detector with blank409449 |245 removes255 but breaks increment at minimal marked file. Partial244 loses the decrement branch through an exact full-configuration collision. |
|4, beyond246| Strong invariant/source analyses, scoped pair/action searches, exact scanner and state204 witnesses, detector synthesis framework | No sub246. Pair merges120540, separately inferred-register conjugacy120540, 2-incoming action family44539776 are scoped; no global lower bound. |
|5, sub246| Sound finite-source-block simulation with workspace/gap/spares existentially hidden; quiet/arithmetic endpoints; closed failure certificates | No sub246. Tail deletion blank traps after3 steps. Short detector gives wrong source frame from a state actually reached at reference blank step6012481; W differs10 vs0, so PC-only repair is insufficient. |
|6, under246|201-source-node graph; alternative fully certified246 binary with unchanged410735 boot; commutation proofs and optimization | Direct201 compilation fails borrowed decoder contracts. Restoring a distinction yields246. Complete3-row repair family is exhausted only relative to its bounded affine check;4-row family capped and incomplete. |

No incoming package claims a validated machine with fewer than246 working
states. Some source transformations improve a grammar count while their
concrete binary implementations tie246 or reach250.

## Strongest concrete frontier

Archive6's201-node graph and archive2's colored-scanner constraints are the
best completed restart points. For the201 graph, introduce
`J=(N48,N79)`, set
`N99=(N43,J)`, `N59=(N99,I1)`, `N74=(N48,N63)`,
`N83=(N63,J)`, and remove49,73,82.
Its certificate preserves all6460 instructions and8391 guarded cases.

Archive2 preserves54 borrowed rows and transported preceding-bit contexts.
Its positive colored246 reduces bad decrement suffixes18->15. Its protected
source frontier reaches5 but lacks terminal-handler compatibility. Combining
these dimensions has a concrete goal: zero remaining offending suffixes while
keeping all shared entry contracts, so that scanner74 can be deleted.

A further apparently untested dimension is INDEPENDENT selector retargeting
under a physical-register permutation, together with these source layouts.
Archive4's conjugacy search only inferred a possible map after each pair merge;
it explicitly did not enumerate independently retargeted register permutations.
Target the alias equations around218/23/105 instead of indiscriminately
enumerating9! choices. Any resulting table needs its own safe blank startup.

## Arithmetic collision: precise limit

The partial244 mutation changes255/0 to1L63 and255/1 to0R95, deleting112/131.
Increment and positive decrement work; zero decrement returns via the positive
interface and appends a value-one spare.

For arbitrary prefixA and nonempty suffixS, marked inputs zero withS and one
withS+[1] reach exactly the same complete configuration:
state48, head0, tape `left 1 B(A+[0]+S+[1]) blank`.
The collision exists even when all spares are1. It blocks any common
deterministic return event from recovering opposite branch outcomes.
It does NOT refute every possible many-step existential relation or prove
both inputs reachable on the actual blank orbit. An additional count/phase
invariant is substantive and must be enforced and read by the machine.

Thus do not accept an arithmetic proof merely because it updates numerical
registers correctly: the zero/nonzero control distinction must survive.

## Proof checklist for a new candidate

1. Exact literal table, total binary rows, working-state count, separate halt,
   explicit initial state, blank initial tape.
2. Source transformation: full instruction/register/guard successor graph,
   including break/continue operands, halt, and dirty-root domain.
3. Universal register macros: arbitrary values and exterior contexts, exact
   prefix/header movement, nonempty spare suffix preserved forever.
4. Shared decoder contexts: every borrowed entry contract, not only passive
   subtree denotations. Preceding bits and transient phase words matter.
5. Full PC/gap target including overflow and trailing-zero rebasing.
6. Positive literal progress for every nonhalting macro; full-tape output.
7. Complete coverage of all admitted guarded instruction cases, with proof of
   any unreachable exclusions, and correct selected physical register.
8. Exact complete-support blank prefix into a safe root; neither a long run
   nor a window comparison is a substitute.
9. Finite induction for both halting directions. A target frame needs a
   positive segment; first return to dispatcher is not automatically correct.
10. Specific set-coded ZFC calibration: countable-language completeness,
    nonextensional quotient, internal well-founded domain and constructible
    submodel. No transitive-model assumption or universe truth predicate.
11. State the proof-assistant boundary honestly: conventional ZFC proof may
    satisfy this user target without a serialized PA object, but an external
    Lean theorem alone does not supply that internal proof.
12. Independence: consistency gives non-provability of nonhalting via GodelII;
    failure to prove halting requires suitable Sigma1 soundness, not mere
    consistency. The equivalence theorem itself assumes neither consistency
    nor soundness.

