# Independent review: framed control contracts for K215

Review target: ProveIt commit `cbf94cb552a3b49509e0eee80e7455d4eb5974c6`.
This review distinguishes checked finite data, proposed generic theorems, and the
still separate full endpoint integration. No proof compiler was invoked by this
reviewer. The companion `audit_left_frames.py` imports no repository Python.

## Exact finite findings

`audit_left_frames.py` independently parses the maintained K215 table and decoder,
expands the decoder's 202-node acyclic source DAG, checks its equality with every
one of the 4,751 published leaf records, and follows all 234-role routes to the
primitive entry. It compares all 430 rows of `KTable215` with the native machine
under native 301 -> formal 102, 302 -> 120, halt 254 -> 230.

The leaf census is 1,900 increment leaves, 1,425 decrement leaves, 98 breaks,
1,327 continues, and one halt. Decrement has two register guards, so the total is
1,900 + 2*1,425 + 98 + 1,327 + 1 = 6,176 outcomes.

The saved assignment data partitions all 1,425 control leaves into 1,422 template
uses and three literal fallbacks. The template uses are 1,326 continues and 96
breaks. Every one of the 35 templates is used. The exact fallbacks are `001/CB1`,
`1000111/CC3`, and `11011/CB1`. There are 721 accepted prefixes ending in zero,
so an extra ends-in-one restriction would incorrectly discard valid sharing.

The 35 bodies have exactly 444 symbolic steps, with maximum 39. Every step is
replayed by an independent transcription of maintained `sstep`; all intermediate
inputs avoid the forbidden active-empty-left case. Every body terminates exactly
at `(2, true, [], R')`, and its right list normalizes to the claimed result word,
gap, header and untouched register box. No native-label/formal-label substitution
is left implicit.

Thus the proposed expensive replay count is

    35 + 3 + 1900 + 2850 + 1 = 4789,

which is 1,387 fewer than 6,176 (22.4579%). This is a count of candidate distinct
expensive local replay obligations. It is not a source-size, memory, wall-clock,
or endpoint build improvement. All 6,176 guarded source outcomes still need
coverage and exact binding proofs. A template occurrence additionally needs a
short routing, frame, source-action, scanner and gap instantiation.

## The guarded frame theorem is the correct abstraction

For symbolic configuration `s=(q,on,L,R)`, write

    frame(F,s) = (q,on,L ++ F,R).

Let `safe(s)` mean `not (on=true and L=[])`. The proposed equation is:

    safe(s) and sstep(M,br,s)=Some(t,m)
    imply sstep(M,br,frame(F,s))=Some(frame(F,t),m).

It holds for an arbitrary segment list F. Its proof is an exhaustive algebraic
analysis of the existing step function. The runtime's run-skipping and register
oracle cases append or preserve the same left list; the run-peeling helpers
commute with append. No tape equivalence, model quotient, normalization algorithm,
or new trusted executor is required.

The excluded case is indispensable. At `(q,true,[],R)` the original executor
reorients by introducing a blank on the right. With frame `[bit true]`, it instead
reads that true cell. `audit_left_frames.py` checks this explicit counterexample.
It is insufficient to prove only that the *final* left fragment is empty: the
guard must hold before every local step. It is also wrong to trim trailing zeros
from a left fragment before appending a nonblank frame. For example `[false]`
and `[]` describe the same unframed blank exterior, while `[false,true]` and
`[true]` have different distances to the marker after appending `[true]`.

Induct on the number of successful guarded local steps and use the existing
`KRuntimeCore.sstep_sound` for each framed input. The resulting theorem is
`Reach`, not `Reach1`, and quantifies over every natural gap parameter and every
register list satisfying `Valid br`. This is sufficient: the subsequent existing
Home theorem supplies `Reach1`, and `Reach.trans_reach1` composes them. Requiring
the local trace itself to have a true progress flag is unnecessary.

## Whole-tape statement and arithmetic

Factor the actual consumed source word as Q=P++S, with S nonempty. Let the
template change S to E and leave registers unchanged. For every natural n and
valid register list vs, the primitive port is

    state q,
    left reverse(init(S)) ++ reverse(P) ++ [true],
    right last(S) :: 0^(n+16) ++ [true] ++ sepsR(vs).

The frame is exactly `reverse(P).map bit ++ [bit true]`. After the local body it
is a Home configuration with empty explicit left fragment and this frame intact.
If `KHome.scanBound 0 (reverse(P).map bit)=Some(k)`, the existing Home result gives

    Reach1 to state 84,
    left [true],
    right P ++ E ++ 0^(n+16+|S|-|E|) ++ [true] ++ sepsR(vs).

This is equality of whole canonical zipper configurations, including the gap,
markers and register file. The far-left exterior is blank, as required by Home's
boundary theorem. The arbitrary frame theorem by itself should not be advertised
as an arbitrary nonblank far-left Home theorem.

For an actual KSim site with parameter a, use

    n = a + (48 - |Q|).

Since |Q| <= 48, n+16 = a+(64-|Q|). Since |E| <= |S|, the output gap is
a+(64-|P++E|). These inequalities are needed for Lean's natural subtraction.

The source-action side conditions are independent of the runtime frame guard:

* Continue k: S contains at least k ones and strip(true,k,S)=E.
* Break k: S contains at least k zeros; put T=strip(false,k,S). The fixed-width
  increment of T has no overflow and equals E.

Then stripping cannot enter P, and break's carry cannot enter P. Consequently
continue(k,P++S)=P++E or break(k,P++S)=P++E, respectively. The finite audit checks
both these sufficient side conditions and the exact complete-word equality for
every occurrence. Matching output strings for a single concrete P would not
replace the generic side conditions.

## Current integration boundary

The current maintained `KSim.Covered` still requires

    checkEdge M (consume P d) e = true.

`KEndpoint` takes that Boolean coverage theorem explicitly, and `KEndpoint215`
supplies `KSites215.covered`. A semantic Reach1 theorem does **not** imply a
bounded symbolic-executor success equation: the reverse completeness theorem
does not exist, and would generally be false for an arbitrary fuel limit.
Therefore replacing `KSites215` directly with semantic template theorems is a
type-level error, even if the underlying mathematical executions are correct.

Preferred integration route:

1. Adopt the already proposed semantic `KSim.EdgeSpec` / `SemanticCovered`
   interface, keeping `edgeSpec_of_checkEdge` and old `halts_iff` as compatibility
   wrappers. Its checked component exists in the `proof-contracts` and
   `semantic-coverage` proposals; inspect current sources before rebasing it.
2. For each literal source leaf use `KDecoderPrefix215.leaf_prefix`. This gives
   the exact maintained table, routed state, last bit, full consumed word and
   concrete zipper run. Use `routed_control_unique` (or an exact computed route
   fact) to identify the template's q. Physical q alone is not a decoder role.
3. For a framed control occurrence compose that prefix run, the instantiated
   local frame theorem, and Home, yielding the corresponding `RunToSpec`.
4. For the remaining 4,754 outcomes use the existing whole-site checker as a
   semantic producer, or an independently checked residual checker if available.
   Here 4,754 = 1,900 + 2,850 + 3 + 1. Keep the halt-port terminal rows separate.
5. Prove total `SemanticCovered` by the existing source tree / walk coverage
   interface. Add a semantic endpoint wrapper with the same final statement.
6. Rebuild the actual affected closure and inspect the final assumptions before
   declaring a shorter K215 endpoint. Until then this is a verified reusable
   component, not a replacement certificate for the whole machine.

An alternative is to add a sound template branch to a new per-edge Boolean
checker, prove that either branch produces EdgeSpec, and use mixed coverage.
This can make occurrence binding cheap by reflection, but it still needs the
semantic consumer. Proving a template branch returns true in the *old* checker
would recover the original expensive computation and defeat the purpose.

## Current status versus historical prose

The round13 proposal describes 35 bodies as uncompiled. Current maintained
KRuntimeCore has no frame constructor/theorem, and current KSim still consumes
Boolean coverage. These are genuine remaining proof obligations.

Some other proposal status summaries are stale: current KEndpoint already
imports `KSeedDirect222`, and KEndpoint215 explains direct C222 compilation.
Thus fresh-label/direct-seed and direct-compiler fusion must not be presented as
new findings solely because the proposals index still labels them pending.

The round13 README cites an older all-leaf residual packet and a 51-module
compilation receipt. The referenced `shared-invariants/decoder-residual` source
directory is absent from tracked files at this pin. The review therefore does
not independently certify that historical component. The current prefix theorem,
current old checker, and visible semantic-interface proposal suffice for the
integration plan without relying on that missing packet.

## Recommended wording for the final article

"We turn the earlier 35-template proposal into a checked reusable frame core
and validate its exact literal-table instances. An independent finite audit
reconstructs all 1,422 intended uses against the pinned source and decoder.
The current contribution does not replace the entire KSites215 endpoint; the
semantic-coverage integration and final endpoint rebuild remain explicit next
steps. The potential 22.46% reduction counts expensive residual replay bodies,
not total logical obligations or measured compilation time."

Adjust the first sentence to the actual compiler results obtained by the Lean
agent. This independent reviewer did not run that compiler.
