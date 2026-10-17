# Intake 153, source 35 — independent mathematical, Lean and executable review

Reviewed 2026-10-16. Placement verdict: **ordinary addition to the existing ZFC closure-kernels host; no current asserted result is refuted.** The main mathematical statements and the finite rewrite criterion are sound at their stated scopes. All advertised functional suites were reproduced. No new ≤252-state consistency-equivalent blank machine is delivered.

## Delivery and handling

Arrival `4e720ccbbfaa836b95be3b2f3f268a737b48c6d1`, archive `docs/incoming/zfc_consistency_research_2026-10-16.zip` (2,325,732 compressed bytes). Inventory records 80 delivered files / 3,530,203 expanded bytes. Wrapper `zfc_consistency_research_2026-10-16/`. Main title: **Small Turing Machines for the Consistency of ZFC: Source audit, formal scratch absorption, and certified transition synthesis**. ProveIt pin `426592ce97e52d309bfb8f0132411556650b7ac1`; upstream `297ab8df7e5de329605c3875b4934643b371a5e3`; attributed public253 head `0d544f2a2e3c18f12278441a74b7879f31cbe856`.

Untouched extraction: `/tmp/zfc-intake-153-ow_22toz/original/zfc_consistency_research_2026-10-16/zfc_consistency_research_2026-10-16`.
All execution and PDF work used the separate copy `/tmp/zfc-review153-source35-5edb6uxi/bundle` and sibling output directories. No delivered source was edited, no Coq was built, and no manifest or line-ending verification was performed. The adapter `/tmp/zfc-review153-source35-5edb6uxi/skip_bulk.py` removes exactly the `for e in manifest['sources']` loop from each of the quick/build drivers in memory. All individual functional input/certificate/table pin guards remain. The quick driver's unchanged final print still says “source hashes”; that portion was intentionally **not** reproduced.

Read in full: README, 1,110-line report, optimization section, all three substantive notes, all new Lean sources and statement audit, builder, quick driver, dirty-prefix interpreter, all search/verifier/test code, and runtime diagnostic. The duplicate optimization TeX differs only in formatting the input pin/hash; its substantive section is the same. Existing dependency imports are the pinned first-order/calculus/enumerator/structured-runtime closure; the fresh build checks them as actual source.

## New checked results and exact boundaries

1. **Arbitrary abstract enumerator starts.** `EnumSafeStart254.safe_start_iff` states `∀s, Inv s → (HaltsFrom s ↔ C254 F)` for all six fields. `complete_from` has no invariant premise: a numerical refutation makes the enumerator halt from every starting state. Soundness retains theorem-valued current formula, retained formula and every formula-stack tail. `reach_ge` first drains the initial list and then reaches each sufficiently late candidate unless already halted. The reset prefix `.ax 0 1 1 u` leaves the compiler's required contract intact, and `pad_code_ge` puts its code beyond any initial cutoff. The terminal DROP/NIP/NIP sequence is checked. There is no finite-test inference of cofinality.

   The report correctly attributes the ordinary argument to existing intake source09, rather than calling it a new mathematical discovery. Current `intake-144-source-09-theory.md:25` already says: “Tail universality” and explicitly checks arbitrary retained data, cutoff and padded reset. The new contribution is its exact Lean proof.

2. **Dirty selector/scratch absorption at the literal root.** For source-order registers `[N,T,W,A,D,H,X,Y,L]`, set `(N',X',n)=(N+X+1,0,N)` if `L=0`, otherwise `(N,X,L−1)`; set `(u,v)=unP(P(X',Y)+n)`. The virtual state is `[N',T,W,0,D,H,0,0,P(A+u,v)+1]`. Both executions of fetch133 then read174 end at `[N',T,W,A+u,D,H,0,0,v]`.

   `DirtyRoot254.root_equiv` quantifies every structured exit and exact final infinite register file. `iter_equiv` preserves iterated-root halting. All nine initial numeric fields are unrestricted for these exact continuation statements; all registers ≥9 are the zero tail imposed by `L2.enc`. The generic `node_transfer` correctly preserves continue-1 restarts from the common intermediate file. It does not restart either execution from its original dirty input. The formula invariant is required only for subsequent consistency calibration, not for this prefix equality. The explicit original scratch seed and additive selector are necessary; the negative controls confirm the obvious incorrect alternatives fail.

   `virtual_enum_iff` deliberately names the **abstract enumerator** and is not a disguised full DAG/enumerator theorem. Safe starts allow all six nonformula fields `N,A,D,X,Y,L` to vary while `T,W,H` remain safe. This does not allow an arbitrary interior PC, arbitrary exterior tape, or an unvalidated binary register frame. Physical spare blocks are also a separate binary-frame resource, not permission to alter the logical zero register tail.

3. **A sound finite-block rewrite criterion.** Abstract windows overapproximate the original blank run by freely filling each newly exposed boundary bit. At every modified incoming row, both executions must take positive steps to an identical full local configuration; writes are confined to the window, so this extends to the entire tape for every exterior. A matching head may finish outside the window if that exterior was never read/written. A pair of terminal outcomes need only agree on halting. The replacement block stops before executing another modified row or entering the deleted state. Thus the separate choices compose. Determinism and positive progress prove blank-halting equivalence; they do not prove a global state lower bound. The old side may traverse other old rows, which is harmless: only the replacement side needs to avoid subsequently executing a row whose implementation will change.

4. **Concrete same-count direction rewrite.** The two literal 253-state tables differ exactly at compact `(131,1)`: `(0,L,20)` becomes `(0,R,22)`. A standalone parser/reachability/interpreter checker, importing no search code, recomputes 3,530 abstract configurations and covers all relevant modified-row windows with 12 local cases (8+4). The guard is that cell −1 or −2 is one. Old/new blocks take 2/4 or 3/5 steps and rejoin in state22 at relative head−2 or−3 with the complete same tape. The variant is not smaller or faster. It removes one caller of20, retaining that state and four other callers. This is an ordinary mathematical correctness argument plus executable finite certificate, **not** a Lean-checked rewrite theorem.

5. **Bounded synthesis/diagnostic work.** The 597,080 count means transition-alternative checks over two radii plus staged variants, not that many different whole machines. No nonstart deletion has a certificate in this separable family. Spatial exits and modified-row barriers are first obstructions; no first rejection exhausted fuel128. The short-gap record is a literal prefix, a reconstructed-frame literal instruction, and an accelerated continuation using prototype register-box summaries. Its first affine failure is not a demonstrated tape collision, but neither fixed-gap success nor a million register instructions proves a smaller machine's blank correctness or nonhalting.

## Current-tree reconciliation

The report's missing-clean-Lean-bridge caveat is historical, tied to its input pin. Current `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/L2Root254.lean:206` already states `iter_iff (s : Enum254.St)`, equating actual structured-root iteration with `∃n s', run n s = some s' ∧ enumStep s' = none` for every clean six-field state. At `:285`, `program_halts_iff` joins the initial structured program to `C254 F`. Thus the new two modules can now be ported and composed with an existing Lean clean-root bridge; the source's “missing AX/clean root” paragraph must not be repeated as a current gap.

Current `RMEquiv254.lean:60` proves `path_halts_iff_iter (R)` for the 219-node DAG's path semantics, and `:66` joins that path program's specified boot registers to numerical falsity. This still must not be confused with an identification with the separately listed 6,459-node literal `Prog254` path program.

Current `NativeTheory254.lean:76` states `C254 F ↔ BProv NativeAx [] fBot`; `:91` states actual structured-program halting iff refutation of the exact sealed native-equality CP/all-native-Form-GIC/IR theory. These strengthen the source's pin-era logical model comparisons. They do not finish Foundation/Choice/refutation internalization or binary runtime calibration. The source's caution about no silent all-ZFC-proof reflection or set model of all ZFC is correct.

Current `ZeroSite253.lean:1477` states `bootstrap_matches_rm331`: actual binary time313429 corresponds to RM331 with complete `DispatchFrame`, gap38 and all158spares. The source's 312975/RM330 frame remains correct and useful but is no longer the latest finite endpoint. Neither endpoint is a general runtime theorem.

Current `QuotientZF0.lean:78` supplies only `c254_of_zf0_refutation`; it is not a full formal calibration with full ZFC. The newly documented quotient-IR obstruction means rawIR cannot simply be transported through the bisimulation quotient. Nothing in this submission contradicts that obstruction: it retains the original numerical/native IR contract and does not claim a new quotient-IR proof.

The source already distinguishes the existing public253 protected folds, old5/84 additional folds, 148368symbol-wise fusion, old107recipes and radius4/5 macro checks. Its incoming **write/direction/target** synthesis is a new bounded sufficient-criterion family. No historical finite negative result becomes a minimality theorem.

## Fresh execution results

All commands below used `uv run --no-project python`; output paths are scratch. All exits were zero.

| Suite | Actual result |
|---|---|
| Quick driver (bulk loop omitted in memory) | 5,096 exact prefix cases (4096 exhaustive +1000 seeded); maximum dirty559/virtual30895 primitive leaf steps; wrong-map detections4645/792/4048. |
| Standalone direction variant | 3530 abstract configurations;12 local windows;8+4 cases; exact one-row table difference;253working states. |
| Adversarial unit suite | All9 pass: valid direction-changing deletion, altered tape, other changed-row barrier, deleted target, zero progress, missing window, forged steps, blank-run abstraction and malformed table. |
| Fresh Lean builder (bulk loop omitted in memory) | All19 transitive modules built from sources, official Lean4.32.0 commit8c9756b28d64dab099da31a4c09229a9e6a2ef35; summed module times55.983s;9 exact printed axiom audits. |
| Radius6 /128 regeneration | 335369abstract configurations;252nonstart targets;263source rows;266156alternatives;43passing alternatives in11rows;0deletions;18.905s. |
| Radius7 /128 regeneration | 1129505abstract configurations;252targets;263rows;266156alternatives;43passing alternatives;0deletions;28.549s. |
| Staged regeneration | 64certified partial-rewrite253-state variants;64768alternatives;0deletions;42.382s. |
| Independent literal R6 ledger replay | 266113negative witnesses;43positive alternatives;9984positive local-window witnesses;263complete1012-alternative sets;252nonstart obstructions;17.319s. Shares parser/window abstraction only. |
| Shortgap full advertised limit | Exact999186-step blank prefix; affine stop at instruction641; reconstructed-frame literal instruction succeeds in2794steps; fixed-gap model completes1000000instructions/124local cases, no root or overflow. |
| Functional evidence comparison | All7 generated JSON objects match delivery after removing only timing/provenance-hash fields; every decompressed ledger row matches exactly for266156+266156+64768rows. No manifest verification is involved. |
| PDF | Three pdfLaTeX passes PASS;23pages,18embedded fonts; zero warnings/errors/overfull/underfull boxes; rendered physical pages10,12,14,15,16 inspected clean, including theorem statements and census tables. |

The axiom audit has `pad_code_ge` depending on `[propext, Quot.sound]`; each of the other eight reported theorems depends on `[propext, Classical.choice, Quot.sound]`. No `sorryAx`, newly declared axiom, native-decision oracle, or copied `.olean` dependency is used. Full exact types and axiom output are in `lean-build/BusyBeaver/ZFC/CheckTheory254.log`.

The independently replayed report retains its announced limitations: this review did not recompile upstream Rocq or independently reproduce its reported CI job. PR20's open/unmerged status and external CI statistics are dated source-audit observations, not a fresh current-web verification by this intake reviewer. Historical table and theory claims overlap earlier accepted primary-source audits; no new historical refutation was found.

## Documentation issue and nonclaims

`notes/THEORY-NOTES.md:239` gives `python3 verify_theory.py --repo ...`; that legacy script is **not in this archive**, and the relative standalone module paths at239–254 are for an earlier layout. This is a minor stale reproduction instruction. The actual top-level README correctly gives the portable `formal/build.py` command; that advertised build was freshly reproduced. Preserve the note and reconcile the command in host commentary instead of editing the delivered file.

The new variant is exactly253states. There is no new252blank machine, no proof that the runtime252 blank orbit reaches a safe root, no proof of its formula-stack invariant at the reported interior PC, no all-future short-gap invariant, no global minimum, and no internal-ZFC theorem for the target machine. These are explicitly disclaimed. Consistency alone is correctly separated from any soundness/reflection hypothesis used to discuss what ZFC can prove about halting.

## Useful next work

The immediate finite Lean step is to port the two new theorem modules, identify `virtual st` with `toAS (enumOf (virtual st))` using its three zero fields, and compose `iter_equiv`, current `L2.iter_iff` and `safe_start_iff`. This yields a checked dirty-root consistency-search contract retaining the exact `Inv` and zero tail; it needs no new logical kernel.

For a new binary initializer, accept an exact full frame at the genuine root with safe `(T,W,H)`, rather than requiring six other fields to be zero. Preserve all spare data and exterior cells and keep physical frame and logical register invariants distinct. The source's short-gap PC is not such a root, so it is not an accepted endpoint merely because its registers resemble an admissible state. A future interacting-row rewrite needs a whole-tape invariant and positive-progress simulation, not only larger finite fuel.

## Evidence paths / exact replay commands

Master result `/tmp/zfc-intake-153-ow_22toz/source35-review.json`; scratch root `/tmp/zfc-review153-source35-5edb6uxi`.

From its `bundle` directory:

```sh
uv run --no-project python ../skip_bulk.py code/quick_checks.py --output-dir ../quick
uv run --no-project python ../skip_bulk.py formal/build.py --lean /home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean --build-dir ../lean-build
uv run --no-project python optimization/edge_replacement_search.py machines/zfc_253.tm --radius 6 --steps 128 --output ../search/r6.json
uv run --no-project python optimization/edge_replacement_search.py machines/zfc_253.tm --radius 7 --steps 128 --output ../search/r7.json
uv run --no-project python optimization/staged_replacement_search.py machines/zfc_253.tm ../search/r6.json --output ../search/staged.json
uv run --no-project python optimization/verify_edge_evidence.py machines/zfc_253.tm ../search/r6.json --output ../search/r6-verified.json
uv run --no-project python notes/runtime252_short_gap.py --upstream vendor/busy-beaver --limit 1000000 --output ../shortgap.json
```

PDF commands were three sequential `pdflatex -interaction=nonstopmode -halt-on-error report.tex` calls in a further scratch `pdf` copy. Full functional artifact comparison: `uv run --no-project python ../compare_functional.py`. Original extraction remained untouched throughout.
