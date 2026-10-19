# Core reductions and a certified bootstrap obstruction

**No machine with fewer than 245 working states was established in this subproject.** The deliverable contains broader finite reduction searches, a universally verified runtime resource variant, and a complete proof that the same variant has unsuitable behavior from every available blank-tape startstate. Every table uses the ordinary binary, single-tape, two-way blank-tape model with L/R moves.

The strongest result is the bootstrap obstruction, not a successful state reduction. Change only old255/read0 from `1 L255` to `0 L255` in the routed245 machine. This lets the increment routine append a spare block ofvalue0 rather than1. The universal local macro contracts still hold. A complete whole-frame symbolic replay also passes all 8,391 guarded instruction cases, using 2,312,645 symbolic rules and covering all 490 transition rows. It quantifies independent arbitrary primary register values, arbitrary gap 64+n, and an arbitrary nonempty spare suffix; minimum progress is 13 steps. The proof is an auditable mathematical symbolic check, not a new proof-assistant endpoint. Nevertheless, from start95 the machine reaches state42 after78 steps, with head4 and one-cells exactly `{-3,-2,2}`. Since `42/read0 -> 1 R42`, it then moves right forever, always reading a fresh zero. All245 startstates have been classified:243 enter a certified blank-ray self-loop, while starts73 and83 halt after5380 and5379 steps, respectively. The complete classification has no timeout or unresolved case.

The induced nonhalting proof for start 95 is unconditional in elementary arithmetic. This does **not** make the external truth-value equivalence with consistency false whenever ZFC is consistent: both statements are then true. The relevant failure is the requested *provable calibration*: assuming ZFC is consistent and its usual arithmetization, Gödel's second incompleteness theorem prevents ZFC from proving the target equivalence for a machine whose nonhalting ZFC already proves. The finite-prefix and blank-ray proof itself does not assume consistency.

## Inputs and provenance

`inputs/routing245_old.tm` is the maintained routed245 table in its old labels. It has245 working states, start95, dispatcher96 and halt254. `inputs/spare0_245_old.tm` differs in exactly the single write specified above; its SHA-256 is `d29d053e4bc1dc41a57bd2ae983ef5033438b350be75c26f06b1eb62718e61b3`.

The original8385 concrete instruction fixtures come from the incoming archive `zfc245-proof-20261018.zip`, path `inputs/state_reduction/candidate245-literal-cases.txt.gz`. Their maximum baseline runtime is2686 transitions. This fixture count must not be confused with the8391 universally guarded instruction cases: the archived concrete fixture set is a separate finite regression artifact. The compressed local copy is `inputs/cases.txt.gz`; its raw contents preserve the original records. The spare-zero fixture file changes exactly2599 increment targets by removing the last one-cell of the appended B(1) block. Inputs themselves remain unchanged, including their arbitrary finite concrete sparelists.

The primary upstream work is attributed to Mira-Cult, Jeff Ketchersid, and Andrew James Wade, with ProveIt's subsequent permutation, prefix, and routed encodings. Bitset tape replay in the new C++ searches is adapted from the archive's `code/state_reduction/resource_merge_search.cpp`; the search families and diagnostics here are new. The universal word/list proof adapters use the attributed exact baseline drivers. Inherited MIT No Attribution license texts are retained in `licenses/`.

Relevant repository inputs:

- <https://github.com/VladimirReshetnikov/ProveIt/tree/main/Computability/BusyBeaver/Research/ZFC/candidate-routing245>
- <https://github.com/VladimirReshetnikov/ProveIt/blob/main/docs/incoming/zfc245-proof-20261018.zip>
- <https://github.com/jeff87654/busy-beaver/tree/zf-254/ZF/m254>

## Completed finite search families

All results below have zero survivors. Exact terminal logs and structured records are in `results/search_summary.json`.

| Family | Work completed | Scope |
|---|---:|---|
| Single incoming edge, exact endpoint |133,712 row rewrites|137 states; arbitrary incoming write, move and target|
| Single incoming edge, flexible frame|133,712 row rewrites|Allows different safe gap, tape translation and any nonempty sparelist|
| Contextual incoming edges|161,040 individual screens plus1,908,120 composed rewrites|States with2–6 nonself incoming edges; each incoming edge may use a different replacement|
| Three-state endhandler, full instruction interface|595,777 partial-table nodes|Resynthesizes75,112,131; removes255; five successor choices|
| Same endhandler with broader runtime reuse|7,534,057 partial-table nodes|Seventeen successor choices|
| Three-state return core, left-moving|231,420 partial-table nodes|Resynthesizes48,112,131; removes63; retargets75/read1|
| Same return core with L/R movement|8,312,852 partial-table nodes|Allows different intermediate head positions and tape edits|
| Spare-zero single incoming and contextual searches|Same row-screen and composition counts as above|Separate exact output targets appendingB(0)|
| Spare-zero endhandler resynthesis|811,877 partial-table nodes|Full instruction endpoints with appendedB(0)|

The exact single-edge family excludes deletion of start 95 or dispatcher 96. For every eligible erased state, all nonself incoming edges are counted from the literal table. A single incoming edge is replaced by any writebit, either motion, and any of 244 remaining working-state targets. This gives 137×244×4=133,712 candidates. Self-loops in the deleted state do not prevent deletion because the rewritten table has no remaining nonself route into it.

For the contextual family, each incoming edge is first screened alone while the erased state remains present. All combinations of surviving individual rewrites are then tested together; after all incoming edges are redirected, the erased state is unreachable. This family intentionally misses synergistic changes for which neither edge edit works individually. The twelve states with nonempty per-edge survivor sets are 2,30,39,42,48,67,69,122,161,180,215 and 240. Their composition counts sum to 1,908,120.

The single/contextual quick screens permit 6000 moves; full affected-case screens permit 10,000. The baseline check permits 20,000. New execution stops at an exact dispatcher frame or expected halt, not merely the first visit to the dispatcher state. Unaffected baseline traces remain unchanged because none encounters a modified row before its checked endpoint. Concrete tape coordinates lie in[-64,1983]. A bound or tape escape is a rejection by this search policy, not a proof of eventual incorrectness.

The flexible-frame screen recognizes a safe header at distance at least 64, the same normalized instruction-prefix one-cells, the same nine primary register values, and any finite nonempty sparelist. It permits a translated frame. This is a broader finite diagnostic, not a substitute for a new symbolic frame theorem.

The endhandler resynthesizer replaces four microstates by three completely fresh two-row implementations. The narrow successor pool is 75,112,131,48,63. The broader pool additionally contains 7,2,4,20,95,109,73,83,42,14,10 and 6. Every row may choose either writebit and direction. The only symmetry reduction exchanges the two internally named states 112 and 131 at their first use. Full instruction screens use 4000 moves per case and retain arbitrary intermediate tape changes. The separate 56 end-macro contexts permit 120 moves and accept an appended spare ofvalue 0 through 4.

The return-core search removes63 and permits new rows for48,112,131 with successors among48,112,131,7. It also chooses the target of75/read1 among the three retained states while preserving that caller's `1 L` action. Both the all-left and two-way families completed.

These experiments are **not minimization proofs**. Finite register values, finite time and tape bounds, frozen source instructions, limited successor pools, and the compositional prefilter all restrict the search. No global lower bound follows.

## Replay

Python 3 and a C++17 compiler suffice. No solver or proof assistant is required for these diagnostics. First decompress the archived fixtures, for example:

```sh
python3 -c "import gzip,pathlib; p=pathlib.Path('inputs/cases.txt.gz'); pathlib.Path('/tmp/core-cases.txt').write_bytes(gzip.decompress(p.read_bytes()))"
g++ -O3 -std=c++17 code/edge_bypass.cpp -o /tmp/core-edge
/tmp/core-edge /tmp/core-cases.txt /tmp/core-survivors.txt
```

Substitute `contextual_bypass.cpp`, `edge_bypass_relaxed.cpp`, `synth_full.cpp`, `synth_full_wide.cpp`, `synth_return.cpp`, or `synth_return_two_way.cpp` and give the same fixture argument and a fresh survivor filename. The macro-only programs instead use decompressed `inputs/end_cases.txt.gz`. To reproduce their fixed-row mode, add the argument `fixed` to `synth_end`.

Run the independent blank certificate and simulator sanity controls:

```sh
python3 -B code/verify_blank_escape.py
g++ -O3 -std=c++17 code/fixture_sanity.cpp -o /tmp/core-sanity
/tmp/core-sanity /tmp/core-cases.txt
```

The positive controls are the original table and a simultaneous permutation of states131 and255. The negative controls inject premature halting and replace the halt action by an absorbing loop. `results/fixture_sanity.json` records their actual outcomes.

For the universal local proof, recover the original incoming archive and pass its package root:

```sh
python3 -B code/verify_spare_zero.py --package /path/to/zfc245-proof-20261018
python3 -B code/verify_spare_zero.py --package /path/to/zfc245-proof-20261018 --whole-frame
```

The adapter changes one occurrence of the expected appendedB(1) toB(0), with explicit occurrence-count checks. Actual table execution, arbitrary-length induction rules, interval-input validation, guard handling and exact instruction sites remain unchanged. The local proof establishes all four block inductions, the list-word identity, the three register-operation macros and the marking cases. The complete blank certificate is deliberately a separate obligation—and fails in the mathematically explicit way proved above.
