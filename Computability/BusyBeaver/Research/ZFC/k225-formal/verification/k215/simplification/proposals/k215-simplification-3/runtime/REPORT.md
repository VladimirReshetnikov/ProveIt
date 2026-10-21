# K215 runtime simplification: reuse the fast table at symbolic sites

## Result

The smallest trustworthy next refactor is **not a new tape representation**. It is to run the existing symbolic site checks against the **already proved balanced transition tree** and transport their results back to the literal table.

The bootstrap already has both a fast transition trie and a list zipper. The expensive site checks do not: all nine latest site batches still pass the linear-list transition function `tm215` to `KSim.checkEdge`. This is a concrete, currently unimplemented opportunity, independent of source-CFG equality and context memoization.

An independent Python replay of the exact literals passed:

- All **4,751 leaves**, giving **6,176 branch-sensitive symbolic executions**.
- Equality at every one of **2,442,801 symbolic steps** between the linear-table and balanced-tree executions, including the complete symbolic configuration and progress bit.
- **1,635,510 transition lookups**. The Python operation model counts **100,886,942 list-cell visits**, versus **13,084,080 trie branches**: 7.71 list-cell visits per trie branch. This is **not a Lean instruction count or a measured speedup**; arithmetic, reductions, sharing, and elaboration costs differ.
- The complete **95,714-transition bootstrap**, all **13 exact list checkpoints**, and whole-tape finite-support equality between a Core-like sparse-list tape, the raw list zipper, and a bounds-checked integer bitset.

No Lean or Rocq compiler is installed here. The proposed Lean helper and patch are **uncompiled research drafts**, not new formally checked proofs. The Python replay is not a theorem of machine correctness.

## Source and identity

Targeted current sources are pinned to `e0b8f9cb8c496ff2d6e43f478021fc14d42bbfad`. They were fetched with the GitHub file connector, and their local contents were verified against the returned Git blob hashes. See `git_blob_verification.json` and the three `latest*_fetches.json` files. The exact original dense table remains SHA-256:

`fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090`.

The prototype compares all 430 dense transitions to the current Lean `rows215`, checks the complete dense-to-sparse label mapping against `table215`, then checks every trie entry, including absent/terminal states. The 13 checkpoints are copied from the earlier pinned source snapshot at `b6fb232916d008383e7cf2990d68ddb30fded7db`; their exact contents are replayed against the current literal table. That is not a claim to have rebuilt the earlier or current proof closure.

The published original successful site batches took **1,692.447 seconds**, while the bootstrap's 14 modules took **111.374 seconds**. These are historical component costs, not expected savings or measurements of the proposed patch. Source: [published attempt ledger](https://github.com/VladimirReshetnikov/ProveIt/blob/b6fb232916d008383e7cf2990d68ddb30fded7db/Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/lean/actual/attempts.json), independently summarized in the adjacent Lean investigation.

## 1. What the runtime actually computes

There are three distinct tape layers. Confusing them leads to the wrong optimization.

1. `Core.Config` has an absolute integer head and a list of integer positions containing 1. This is the public Rado-machine semantics, but it is **not the interpreter used for the bootstrap or symbolic-site kernel decisions**.
2. `KZip.Conf` has a state and two Boolean lists, normalized by removing trailing blanks. `KBoot.LConf` deliberately keeps trailing blanks and executes list-head/tail operations without renormalization. `KBoot.lstep_sound` and `lblock_sound` already refine this cheap representation to `KZip` semantics.
3. `KRuntimeCore.SConf` has symbolic tape segments: a literal bit, a run of `a*n+c` identical bits, or an abstract register box. The gap parameter and register values range over arbitrary naturals. Its step soundness uses self-loop scan lemmas and the four `BoxLemmas` contracts; it does not unfold the whole register tape.

Relevant exact definitions: [KZip](https://github.com/VladimirReshetnikov/ProveIt/blob/e0b8f9cb8c496ff2d6e43f478021fc14d42bbfad/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KZip.lean#L22-L59), [KBoot](https://github.com/VladimirReshetnikov/ProveIt/blob/e0b8f9cb8c496ff2d6e43f478021fc14d42bbfad/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KBoot.lean#L20-L76), [symbolic segments and execution](https://github.com/VladimirReshetnikov/ProveIt/blob/e0b8f9cb8c496ff2d6e43f478021fc14d42bbfad/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KRuntimeCore.lean#L102-L172).

The bootstrap's `TT.look` follows eight low-order state bits. `fastOf` rejects states at least 256; the finite checked `fast_lt` and a general out-of-range argument establish `fast215 q b` for **all** natural states and Boolean inputs. The bootstrap already uses this fast function. Source: [KFast215](https://github.com/VladimirReshetnikov/ProveIt/blob/e0b8f9cb8c496ff2d6e43f478021fc14d42bbfad/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KFast215.lean).

By contrast, `tm215 = tmOf table215`; `tmOf` uses `t[q]?`, a list lookup. The symbolic step queries this function for literal-bit steps, run scans/peeling decisions, and a box fallback. All nine site batches still use it. Sources: [tmOf](https://github.com/VladimirReshetnikov/ProveIt/blob/e0b8f9cb8c496ff2d6e43f478021fc14d42bbfad/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KTableCore.lean#L19-L22), [representative site batch](https://github.com/VladimirReshetnikov/ProveIt/blob/e0b8f9cb8c496ff2d6e43f478021fc14d42bbfad/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSites215Batch006.lean).

## 2. Minimal Lean change

`KFastSites215.uncompiled.lean` contains two small helper theorems:

1. Turn existing pointwise `fast215` into `fastOf tt215 = tm215` using Lean's existing function extensionality theorem.
2. Transport `allSites (checkEdge (fastOf tt215)) prefix tree = true` to the identical statement with `tm215`.

Each existing block proof changes from `by decide +kernel` to an application of the second helper whose argument is proved by `decide +kernel`. Every block's public statement is left unchanged. The included `fast_sites.uncompiled.patch` adds the helper and updates all nine batch imports and 105 proof bodies. The source-only audit checks that **all 105 statements remain byte-identical**.

This preserves, without reproving:

- `KRuntimeCore.sstep_sound`, `exec_sound`, and `sMatches_conc`;
- the four all-natural register `BoxLemmas` contracts;
- `KSim.runTo`/`checkEdge` semantics and branch validity conditions;
- `SiteCoverage.allSites_sound`, the exact coverage assembly, and `KSites215.covered`;
- `KDense215.commutes` and the public literal-machine endpoint.

No machine transition, state count, path, target, fuel bound, register assumption, or coverage requirement changes. There is no new evaluator to certify and no new axiom. Function extensionality is an existing theorem in Lean; this does not ask to postulate it. The computation stays under `decide +kernel`, not `native_decide`.

The patch is deliberately independent of the separate import-hygiene proposal. It retains the original `KSource215` import, making table acceleration measurable on its own. The two changes can subsequently be composed: narrowing the source-data dependency and accelerating table lookup address different costs.

### Required acceptance test

Compile the helper, a small site batch, and a large site batch first. Then compile all nine batches, coverage, and both closed endpoint clients using the pinned compiler. Verify the original public types and axiom reports. Compare serial clean and incremental runs on the same machine/compiler, retaining logs. The 7.71 operation-shape ratio cannot replace this experiment, and a trie can have overhead that Python does not model.

## 3. Why a bounded bitset is not the first refactor

The prototype uses an explicit interval `[-1024,1024]` and checks the head bounds before every read/write; it does not wrap indexes or assume out-of-range bits are zero after an unchecked access. It compares **complete finite supports**, not only the currently scanned cell or a window. The sparse list has no duplicates, every one-position lies in the bitset interval, and the entire integer bitset equals the sum of the corresponding powers of two. Every omitted cell is zero by the representation definitions and blank initialization.

Observed bootstrap facts:

- Head and write range: `[-18,199]`.
- Maximum simultaneous 1-cells: 157.
- Final head: -8; sparse state 84, dense state 83.
- Exact final raw zipper: left `[true] ++ 9 blanks`; right the specified 65-cell gap plus boot registers and 40 spare registers.
- All 13 raw checkpoint tuples agree, not merely their trimmed tapes.

These establish a useful regression test and concrete boundedness witness. They do **not** establish a Lean refinement theorem or any all-input invariant.

A proved bitset runner would need a representation relation equating reads at every integer cell, bounds-checked one-step simulation, failure on an out-of-bounds read/write, and a run induction. It could reuse Core's read-after-write lemmas or target the already simpler `KZip` layer and use the existing dense/zipper bridge. Equality must be extensional: Core's sparse-list order can change without changing the tape.

However, the existing bootstrap zipper already has constant-shape tape-head operations and no per-step trimming. A big-integer shift/mask implementation adds proof obligations without evidence that it beats the existing kernel evaluator. More importantly, a **fixed bounded bitset cannot replace the symbolic site's arbitrary-natural tape semantics**: unbounded register boxes and `a*n+c` runs must remain symbolic. A hybrid bitset for the finite decoder prefix would still need separation/frame, overflow-marker, and box-boundary lemmas. Reusing `fast215` avoids all of those obligations.

## 4. Can symbolic bootstrap certificates reuse existing lemmas?

Yes, but elementary self-loop compression is not yet a compelling simplification.

`KZip.scanR` and `scanL` already prove arbitrary-length uniform scans. `KRuntimeCore.sstep_sound` uses these lemmas for symbolic runs, and `exec_sound` composes the results. Thus a bootstrap certificate can contain constant runs (`a=0`) and general scan/step blocks instead of replaying every concrete transition. This is genuine reuse of existing all-natural mathematics, not a proposal to trust a generated trace.

The exact trace contains **62,699 self-loop transitions**, arranged into **6,874 maximal same-row scans**, plus **33,015 non-self-loop transitions**. Replacing every such scan with one entry leaves **39,889 entries**, with the longest scan only 65 cells. That is a 58.3% reduction in abstract entries relative to 95,714 individual transitions, **not a source-size or time saving**. It is still much larger certificate scaffolding than the present 13 chunk statements if emitted as explicit proofs.

To improve on this, keep scan certificates chunked and prove a small checked RLE/block evaluator once, or prove a repeated initialization-loop contract that summarizes more than a single scan. Do not emit 39,889 handwritten-style links. Do not merely recognize scans by walking long concrete lists again and assume the kernel computation disappeared.

Two subtleties matter:

- `scanR`/`scanL` currently yield existential `Reach`, not an exact clock equation. That is sufficient for the existing public `KBoot215.boot` interface, but an optimized proof using only those lemmas would not by itself re-establish the advertised exact 95,714 count. A counted version of the scan lemmas and additive clock composition would preserve that stronger fact.
- `exec_sound` is parameterized by `BoxLemmas` and a valid register vector even when a proposed bootstrap trace uses no boxes. Either instantiate the already proved engine contracts without creating an import cycle, or factor a box-free specialization whose soundness needs only scans and literal transitions. Do not use a fictitious empty-register oracle. The current exact bootstrap does not need these additional imports/contracts.

Given the historical 111-second bootstrap cost versus 1,692 seconds for sites, leave the existing bootstrap proof intact for the first optimization pass. The experiment is a grounded reason to prioritize the site table change, not a claim that bootstrap cannot improve further.

## 5. Rocq: same diagnosis, less immediate reuse

Current `Boot230.v` already uses a list zipper, binary recursion on the exact positive step count, a closed `vm_compute` check, and a soundness theorem. It does not use the Core sparse-list representation. Current `TM230.tmn` first checks 15 disabled labels and then uses `nth_error table230 q`. Both concrete bootstrap and symbolic `Runtime230Core.sstep` call this function. Sources: [Rocq bootstrap](https://github.com/VladimirReshetnikov/ProveIt/blob/e0b8f9cb8c496ff2d6e43f478021fc14d42bbfad/Computability/BusyBeaver/Research/ZFC/k225-formal/rocq/rocq-extension/coq/215/Boot230.v), [TM230](https://github.com/VladimirReshetnikov/ProveIt/blob/e0b8f9cb8c496ff2d6e43f478021fc14d42bbfad/Computability/BusyBeaver/Research/ZFC/k225-formal/rocq/rocq-extension/coq/215/TM230.v#L94-L102), [runtime executor](https://github.com/VladimirReshetnikov/ProveIt/blob/e0b8f9cb8c496ff2d6e43f478021fc14d42bbfad/Computability/BusyBeaver/Research/ZFC/k225-formal/rocq/rocq-extension/coq/215/Runtime230Core.v#L135-L184).

A corresponding lookup optimization would:

1. Build a balanced table that directly incorporates disabled-state `None` rows, and prove pointwise agreement with the literal `tmn`, including terminal and out-of-range states.
2. Parameterize the computational `lstep`/`sstep`/`exec` definitions by a lookup function, or add checked fast wrappers.
3. Prove fast/old pointwise step equality by case analysis and fast/old execution equality by fuel induction. Then reuse `lrunp_sound`, `sstep_sound`, `exec_sound`, and the existing site theorems.

Unlike Lean, Rocq's current functions are specialized to `tmn`, so there is not yet a drop-in existing `fast215` theorem. **Do not introduce a functional-extensionality axiom** just to mimic the Lean helper; pointwise rewrite lemmas and induction suffice. Also benchmark representation choices: a naive conversion of unary `nat` states to binary on every lookup can consume the intended gain, and Rocq's VM has different cost behavior from Lean's kernel. The Python counts are not a Rocq performance result.

For both assistants, preserve the established assumption reports and full endpoint audit. Neither Python acceptance, `vm_compute` timing alone, nor a focused module check is a replacement for the repository's required final kernel closure verification.

## Artifacts and replay

- `profile_runtime.py`: standalone standard-library parser, whole-tape bootstrap differential check, and exact symbolic-site differential executor.
- `profile_result.json`, `replay.log`: actual successful run results.
- `input_hashes.json`, `git_blob_verification.json`: pinned local data identities.
- `KFastSites215.uncompiled.lean`, `fast_sites.uncompiled.patch`: proposed two-theorem helper plus 105 proof-body substitutions.
- `patch_static_audit.json`: source-only statement preservation audit, not a compiler result.
- `latest/`, `latest_rocq/`, `inputs/`: necessary source and data snapshots.

Run `python profile_runtime.py` in this directory. Assertions must be enabled. `-O`/`-OO` are rejected, as are modified pinned inputs. No network, compiler, upstream executable, historical-worktree mutation, commit, or push is required.
