# Machine audit and new predecessor-specific deletion search

## Outcome

The smallest fully specified blank-tape construction located in the cited public lineage is the **existing 253-working-state machine** by mira-emmy, based on Mira-Cult's 254-state machine and Jeff's Coq verification. This investigation did not construct a smaller machine. It did independently check the exact two literal tables, reproduce both entire blank-tape bootstrap endpoints, and conduct a new bounded family of nonuniform incoming-edge transformations.

The distinction between an externally verified equivalence and an arithmetized equivalence provable inside ZFC is material. The public 253-state proof explicitly claims the former; it does not claim an internal proof compiler or a formalized independence theorem.

## Immutable inputs and authorship

- Jeff's baseline proof and table:
  https://github.com/jeff87654/busy-beaver/tree/c132d7eae8158cd3a9850ea3eb7251158c3dd821/ZF/m254
  Relevant commit dated 2026-10-14.
- Attributed 253 reduction and proof:
  https://github.com/mira-emmy/busy-beaver/tree/0d544f2a2e3c18f12278441a74b7879f31cbe856/ZF/m253
- Public submission:
  https://github.com/jeff87654/busy-beaver/pull/20
  At retrieval on 2026-10-16 it was open and its head was the pinned commit above.
- ProveIt comparison snapshot:
  https://github.com/VladimirReshetnikov/ProveIt/tree/2c74914bdfc98920ddcc3ff7c092cce10db4d709
- Mira-Cult's original repository is linked by the authors at https://github.com/Mira-Cult/turing-machines, but direct access through the available GitHub connector returned 404. The retained attributed baseline table and proof sources were accessible.

The compiler framework is Andrew James Wade's. No authorship of either published machine or the reused source04 affine-checker adapter is claimed here.

| Table | Working states | Binary rows | Blank | Start | Separate terminal | SHA-256 |
|---|---:|---:|---:|---:|---:|---|
| Mira-Cult baseline | 254 | 508 | 0 | 0 | 254 | d655ce2cf8cccebd21caa21a49f0f9f010960a44b95c17aae6cc425c518954eb |
| mira-emmy reduction | 253 | 506 | 0 | 0 | 253 | 84a21f714017c1d491008d86e9bd19c43cc6c5c9ae99a538b4f2314387827d95 |

The convention is one bi-infinite binary tape with all cells initially zero. Every ordinary transition writes a bit and moves left or right. The distinct terminal control is uncounted; the final write and move are retained.

## Existing 253 reduction

In the original 254-state labels the entire transformation is:

| Source/read | New transition |
|---|---|
| 3/0 | 0 L 48 |
| 5/0 | 1 R 97 |
| 5/1 | 1 R 64 |
| 49/1 | 0 R 5 |

Old state 8 is deleted. Old 5 becomes compact start 0; old dispatcher 96 becomes compact 33; old terminal 254 becomes compact terminal 253. The unchanged public generator includes the full state bijection. The saving shares old 5 between the blank initializer on zero and a guarded runtime helper on one.

The machine's source-order registers are nextproof, topwff, wffstack, axiomcode, param1, param2, scratch1, scratch2, prooflist. The physical tape order is wffstack, param1, axiomcode, scratch2, scratch1, prooflist, nextproof, topwff, param2.

The published bootstrap at 312,975 literal steps reaches old dispatcher 96, absolute head -17, PC 000 followed by 37 zero padding cells and the header at position 23. Its physical register values are [0,2,0,0,0,0,5,0,0], followed by 158 spare blocks, exactly two of which have value one (indices 2 and 8). All other spares are zero. There are 178 one-cells in the entire tape; the marker is at -18.

This is the original register program's 330th configuration. The proof transports register halting across that finite prefix before invoking the unchanged program/calculus/set-theory layers.

## Independent finite checks performed here

Run `python3 audit_baselines.py` in this directory.

The resulting `baseline_audit.json` records:

1. Literal parsing, totality, target closure, state and transition counts for both tables.
2. Agreement of the original 254 table with its retained Coq literal `Table254.v`.
3. Byte-for-byte regeneration of the public 253 table from the original 254 table and the four published edits.
4. Agreement of every 253 transition with ProveIt's independently retained Lean literal.
5. Literal execution of all 264,982 baseline boot steps and all 312,975 public253 boot steps.
6. Equality of the **entire** finite one-cell sets with independently constructed expected frames, including every spare block and the blank exterior, not merely the primary registers or the number of one-cells.
7. All working states are reachable in the control graph, and the write/move-preserving deterministic state quotient is discrete for both tables (13 refinement rounds). Those graph properties are not semantic minimality statements.

The baseline endpoint is old96 at head -8, with 62 zero gap cells, physical registers [0,0,0,0,0,0,2,0,0] and 136 zero spares.

Coq, Rocq, Coqtop, and Opam executables were not installed in the available runtime. No new local kernel build is claimed.

## Public formal verification evidence

GitHub's check-runs endpoint for the exact submitted 253 commit reported `zf253` as **success**, completed 2026-10-16T00:45:27Z:

https://github.com/jeff87654/busy-beaver/actions/runs/38829452130/job/116744580063

The PR and source README report rebuilding 160 source modules, obtaining 194 closed assumption reports, and passing recursive `coqchk`. The endpoint file states:

- `zf253_halts_iff_SIR`: blank halting iff the encoded nonextensional theory has a classical refutation.
- `zf253_halts_iff_ZF`: blank halting iff the library's universally closed ZF presentation has a refutation.
- `zf253_halts_iff_ZFC`: blank halting iff that ZF presentation plus the choice-set axiom has a refutation.

These exact theorem statements, the authors' successful build report, the current success status, and the local finite checks are distinct evidence.

### Foundation and the meaning of the ZFC endpoint

The library's `ZFc` leaves regularity separate. Consequently the named `_ZFC` endpoint literally means ZFc + AC without regularity. This does **not** create a consistency-strength gap. The upstream file

https://github.com/jeff87654/busy-beaver/blob/c132d7eae8158cd3a9850ea3eb7251158c3dd821/ZF/stdzf_r3/zfc/Z_main.v

contains:

```coq
Theorem ZFCReg_equicons :
  (fun phi => (ZFc phi \/ phi = ax_reg') \/ phi = ax_ac) ⊢TC ⊥
  <-> ZFc ⊢TC ⊥.
```

Thus the full external endpoint with regularity follows by composing `zf253_halts_iff_ZF` with the reverse of `ZFCReg_equicons`. This is a composition of refutation equivalences, not an assumption that either theory is consistent.

The internal ZFC theorem requested by the user still requires arithmetization of the machine relation, a chosen effective proof predicate, and a proof that ZFC verifies the relevant proof/program translations. The absence of axioms in a Coq dependency report does not by itself supply such an interpretation of Coq into ZFC.

## Avoiding repeated searches

Before the new search, the following ProveIt notes at the pinned snapshot were read:

- `Computability/BusyBeaver/Research/ZFC/public253_fold_search.md`
- `Computability/BusyBeaver/Research/ZFC/public253_context_search.md`
- `Computability/BusyBeaver/Research/ZFC/public253_macro_search.md`
- source04's engineering README
- source25's machine engineering notes

They already report all direct noncore folds, a symbol-wise fusion family, the old107 two-edge family, and the radius4/radius5 global-window macro searches. They also isolate the prepared 252-state runtime body obtained by deleting old5. All its blank starts reduce to either a proved blank-ray loop or one unresolved small orbit; no valid gap40 frame appeared in the cited two-million-step trials. None of these constitutes a 252-state blank-tape solution.

## New search family

The new experiment changes different incoming edges of a deleted state differently. It is not constrained to one global state map, and its second version may also change the written bit and movement direction at the incoming edge.

### Context acquisition

`edge_contexts.py` uses the attributed, hash-pinned source04 adapter to the original Jeff affine symbolic executor. It checks all 8,391 cases of the original 6,460-leaf register program, with both branches of every decrement and arbitrary affine gap at least 40.

At each explicit non-box incoming transition it extracts a finite neighborhood of the tape. For an affine run of length a*n+c, n=0,...,window-length suffices to enumerate every relevant finite prefix: coefficients are nonnegative integers, and once the total prefix exceeds the window length it is truncated. Taking left and right possibilities independently only enlarges the context set. A register-box suffix is treated as unconstrained after its known first zero. Exact contexts from all 312,975 boot steps are added.

The retained search excludes the register-box source states, all of their direct successors, the dispatcher, deleted old8, and any candidate state having a self-loop. The self-loop restriction avoids treating a single bulk scan observation as an inventory of every interior literal scan position.

There are 218 remaining candidate deleted states and 407 incoming edges. Old5 is among these; deleting it would additionally require a new start-state certificate. Because no deletion passes even the incoming-edge stage, this missing final obligation cannot create a positive result.

### Two replacement families

1. `edge_macro_search.cpp` retains each incoming edge's original write and move and chooses an independent replacement target among the other 252 working states.
2. `edge_action_search.cpp` chooses an independent write bit, move direction, and replacement target at each incoming edge: 2*2*252=1,008 possibilities per edge.

The terminal is not a candidate replacement target in these searches. All original table labels are retained for auditing; no reduced table is emitted.

For each recorded window the checker follows the original block and the proposed block for at most 64 literal steps each. Neither path may read outside the known window. A join requires identical control, head, and the complete known window, with strictly positive progress on both sides. The join control cannot be the removed state. Two terminal endpoints may join without comparing final head or tape. Candidate paths are stopped before they execute the removed state or re-execute an edited incoming edge using its old transition.

A state can pass this diagnostic stage only when **every** incoming edge has at least one replacement satisfying every retained window. A survivor would still need complete candidate construction, all 8,391 affine checks, full blank initialization, and the proof-calibration chain.

### Results

| Radius | Known cells | Collected incoming edges | Total post-edge patterns | Eligible deletions | Checked incoming edges | Target-only choices tested | Whole-action choices tested | Complete deletions |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 4 | 9 | 418 | 15,534 | 218 | 407 | 102,564 | 410,256 | 0 |
| 6 | 13 | 418 | 50,653 | 218 | 407 | 102,564 | 410,256 | 0 |

The 418 context-bearing edges include edges for self-loop states removed before the final search, explaining the 407 checked edges.

At both radii the target-only search found 40 partial edge rewrites; the whole-action search found 52. No choice exists simultaneously for all incoming edges of any eligible deleted state, so no new candidate required a blank bootstrap test.

One new guarded local option is old92/read0 -> 0 R 144, for attempts to remove old107. The earlier family only allowed 0 L 104 or 0 L 129 at that edge. The second incoming edge old130/read0 still has no local replacement in this bounded family. This partial option must not be presented as a 252-state construction.

The negative result is limited to the exact two finite families, context overapproximation, radii, and step bound. A failure can reflect unreachable abstract contexts, too small a window, a longer required matching computation, a need to alter protected register operations, or a transformation outside the family. It is not a state-count lower bound.

## General correctness interface for a future positive result

Let p be a deleted state, and let edited incoming transitions be indexed by e. Suppose:

- the unchanged machine's actual reachable configurations at each e satisfy a guard G_e;
- for every configuration satisfying G_e, the original and transformed machines take finite, strictly positive blocks to exactly the same whole configuration whose state is not p, or both terminate;
- the blocks do not apply an unaccounted edited transition;
- the blank starts agree, or an independently verified finite initial bridge brings them into this relation.

Then blank halting is equivalent. Determinism aligns successive blocks. If the original run is infinite, the transformed run takes at least one step per aligned block and is infinite. If the original run terminates, positive progress in the original prevents infinitely many alignment blocks before its finite halting time; the transformed run terminates with it. Whole-tape agreement at each join carries the guards from the original reachable execution.

This elementary simulation argument is suitable for formalization in ZFC and weak arithmetic once the finite guards and their invariance are certified. The present Python/C++ diagnostic implementation is not itself a kernel proof of these hypotheses.

## Reproduction

From this directory:

```sh
python3 audit_baselines.py
python3 edge_inventory.py
python3 edge_contexts.py --radius 4
python3 edge_contexts.py --radius 6
g++ -O3 -std=c++17 edge_macro_search.cpp -o /tmp/edge_macro_search
g++ -O3 -std=c++17 edge_action_search.cpp -o /tmp/edge_action_search
/tmp/edge_macro_search edge_contexts_r4.txt 64 > edge_macro_r4.txt
/tmp/edge_macro_search edge_contexts_r6.txt 64 > edge_macro_r6.txt
/tmp/edge_action_search pre_contexts_r4.txt 64 > edge_action_r4.txt
/tmp/edge_action_search pre_contexts_r6.txt 64 > edge_action_r6.txt
```

The Python scripts require only the standard library. The C++ searches require a C++17 compiler. No network access or proof compiler is used.

The `upstream/`, `upstream253/`, `proveit/`, and `support/` subdirectories contain only selected attributed source inputs needed by these audits or inspected for the report. They are not a complete Coq build tree. Preserve the upstream notices when incorporating source inputs. The new independent scripts and reports are those at this directory's top level.
