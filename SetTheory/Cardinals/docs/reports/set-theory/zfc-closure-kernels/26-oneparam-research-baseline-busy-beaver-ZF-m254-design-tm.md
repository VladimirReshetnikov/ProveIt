# zfc_254: Turing-machine layer (design, estimate, prototype)

Target: `halts tm c0 <-> rm_halts p254 ([], R0)` for the literal table `../inputs/zfc_254.tm`
(sha256 d655ce2c…, checked by `tools/gen_table.py`). Here `rm_halts` is Wade's path semantics
from `zf/v335/coq/RM.v`, reused unchanged, and `p254` is the decoder tree given by `paths.json`.
`RMEquiv.rm_halts_iff_iter` (generic in the program) then gives the structured big-step
semantics `iter_halts p254 R0` at no cost.

**Status (2026-10-14): DONE.** `coq/Main.v` proves, with no axioms (Coq 8.20, busycoq TM.v):

```coq
Theorem tm254_rm : halts tm c0 <-> rm_halts p254 ([], R0).
Corollary tm254_iter : halts tm c0 <-> iter_halts p254 R0.
```

`python check_tm254.py` checks the whole chain. It verifies the input hash, re-parses the table
independently, regenerates `Table254.v` and `Prog254.v`, does a clean rebuild, and checks the
statements and `Print Assumptions`. `p254` and `R0` are frozen in `coq/Prog254.v`
(module `M254.Prog254`, load path `-Q zf/m254/tm/coq M254`).

## 1. Key decisions

1. **Verify the final 254-state table directly, using a certified symbolic run-length executor.**
   We do not go through the 261-state named table and the four context-merge layers. The executor
   runs the literal table, so the contextual folds, routers, quotient merges and the changed
   `return_1_2`/read0 path are covered without being modelled. Section 7 gives the reasons for
   rejecting the alternative.
2. **Right-hand side: RM.v path semantics on the tree from paths.json.** The machine really does
   implement Wade's path arithmetic:
   * `inc` / positive `decnz` go to `inc_path Q`;
   * zero `decnz` goes to `brk 1 Q`;
   * `_break.k` goes to `brk k Q`, and `_continue.k` goes to `cont k Q`;
   * the marker moving left is RM.v's overflow to the root.

   I checked all 8,390 control edges against `CONTROL_GRAPH.json` `graph` (`tools/paths_check.py`):
   6,340 match exactly and 2,050 match after following `goto` chains, which `graph` short-cuts.
   There are 0 mismatches. The tree is a complete prefix code: 6,460 leaves, 6,459 internal nodes,
   depth at most 34. It satisfies RMEquiv's `wf`: the root has break level 0 and continue level 0
   (`tools/wfcheck.py`).
3. **Registers are numbered in source.py declaration order in the statement.** nextproof 0,
   topwff 1, wffstack 2, axiomcode 3, param1 4, param2 5, scratch1 6, scratch2 7, prooflist 8.
   The TM layer applies the physical permutation internally. This is the numbering Wade's
   TMBuilder gives, so `p254` and the logic layer's 219-node DAG (`../logic/m254_wade.tm`) use the
   same register indices.
4. **Initial vector.** `R0 = upd regs0 0 2`: nextproof = 2, all others 0, at PC `[]`. This is
   where the boot actually lands. The logic layer's `enum` must start from `np = 2` (or bridge to
   it). Its current draft `s0 = all zeros` does not match.

## 2. What the machine does (from tracing the final table; state numbers are zfc_254.tm's)

**Dispatch configuration.** State 96 (`main().0`) has the head on the first PC cell:

```
0^∞  1  P 0^k  1  sepsR(v_0 … v_8 ++ ext)  0^∞          sepsR vs = concat (0 1^(v+1))
     ^marker      ^header
```

* `P` is the PC (Wade path, MSB first, implicit trailing zeros).
* `|P| + k = D`, the gap between marker and header. Boot leaves D = 62. D never decreases, and
  grows by 1 when the PC overflows: the carry runs into the marker, and the new marker is one
  cell further left.
* The blocks are in physical order: wffstack, param1, axiomcode, scratch2, scratch1, prooflist,
  nextproof, topwff, param2.
* `ext` is an arbitrary list of extra blocks (136 zeros after boot). It grows by one zero block
  on every positive decrement.
* Zipper form: `zc (st 96) [true] (P ++ zeros k ++ true :: sepsR (phys R ++ ext))`.

**One instruction reads the PC three times.** In each phase the dispatcher scans left, turns
after 9 consecutive zeros, comes back to the marker, and the decoder re-reads `P`. The leaf state
then reads the two cells after `P`, which tell it the phase:

| cells after P | phase | action |
|---|---|---|
| `0 0` | A, prepare | prep (42) fills the whole gap with 1s up to the header; back to dispatcher |
| `1 1` | B, select | leaf writes 0; skip states (60,44,31,56,38,40,28,64,69) cross the 1-run and `j+1` blocks; state 0 erases the target's first 1 (the **mark**); back to dispatcher |
| `0 1` | C, execute | seek (73 inc / 43 dec) runs right to the `00` of the mark, then performs the operation |

After the operation, the return states scan left to the first `00`, which is the two cells after
`P`:
* return_0 (63/48) leads to `6.break.0` (7), which increments the PC from its last bit;
* return_1 (1/3) leads to peek3 (5), which strips one 0 and then increments.

Next, cleanup (10/14) erases the gap 1s, including the header cell. boot2 (20) rewrites the header,
continue (2) scans the zero gap left, and the dispatcher brings the head back to 96. Control sites
(`_break`/`_continue`) are folded into decoder states that jump into these engine states.

**Register operations** (Box.v, all proved):
* increment: after the mark is restored, 95/109 shift every later block one cell right.
* positive decrement: 85/97 run to the end of the file, then 112/131 shift every later block one
  cell left. This shortens the target and appends a new block `0 1` (value 0).
* zero decrement: 75 → 0 → 1 → 3 restores the mark. Nothing else changes.

## 3. Proof architecture (`coq/`, logical root `M254`, build with `python build.py File.v`)

| File | Content / main statement |
|---|---|
| Table254.v | generated: the 254 rows of zfc_254.tm |
| TM254.v | states `bnat 254`, busycoq `Ctx`, `tm`, numeric `tmn`, `tm_st`, `tm_halt` |
| Zip.v | zipper `zc`/`zl` (from v335 SimBase), padding, `scanR`/`scanL` (self-loops, possibly rewriting) |
| SymExec.v | the executor and `exec_sound` (section 3.1) |
| Box.v | the four register lemmas (section 3.2) |
| Site.v | `check_site`, `site_run` (any non-halt site), `site_halt`, and `site_inc` / `site_dec` |
| RM.v, RMEquiv.v | copies of zf/v335/coq (RMEquiv: `zf2_wf` removed) |
| Prog254.v | generated by tools/gen_prog.py: `p254` (DFS preorder, node indices stored as `N`), `R0`, `p254_wf` |
| Leaves.v | `leaves`, `walk_leaves`, `leaves_root` (generic) |
| Check254.v | `phys_of`, `vregs`, `check_edge`, `all_leaves_check` (vm_compute, about 22 s), `leaf_check` |
| Boot.v | `boot : c0 -->* zc (st 96) [true] (zeros 62 ++ true :: sepsR boot_regs)` |
| Sim.v | `Inv`, `inv_boot`, `inv_step`, `inv_next`, `inv_halt`, `reach` |
| Main.v | `tm254_rm`, `tm254_iter` |
| Demo.v, Sites254.v | the earlier prototype demo, not on the path to Main.v |

### 3.1 The executor (SymExec.v, done)

* **Segments:** `SB b` (one cell), `SR b a c` (`a·n + c` cells of `b`, where `n` is the free gap
  parameter), and `SBox x` (the register file, only as the last segment on the right).
* **Configuration:** `(q, onl, L, R)`. It denotes `zc`/`zl (st q) (flat L) (flat R)` for every
  `n` and `vs`.
* **Box states:** `BPlain (ENone | EInc r | EDec r)` and `BMark r`. They denote `sepsR vs`,
  `sepsR (incr r vs)`, `sepsR (decr r vs ++ [0])` and `sepsM r vs`.
* **Rules of `sstep`:**
  * a concrete step;
  * a whole-run self-loop (`tmn q b = (w, d, q)`; the run may have length 0);
  * peeling one cell off a run, which needs `c ≥ 1`;
  * a box oracle at the register file: skip state → mark; 73 → inc; 43 → dec, with the branch
    chosen by a `branch` argument;
  * reading the file's first cell (always 0) while moving left.
* **Check:** `exec` stops at the first configuration that `matches` the target, after normalising
  runs and dropping trailing left zeros. It never stops at the first visit to state 96.

```coq
Lemma exec_sound (box lemmas) f br tgt s m0 s' n vs :
  exec f br tgt s m0 = Some s' -> valid br vs ->
  tgt s' = true /\ conc n vs s -->* conc n vs s' /\ (m0 = false -> conc n vs s -->+ conc n vs s').
(* valid br vs := 9 <= length vs /\ (zero / nonzero assumption of the decnz branch) *)
```

### 3.2 Register lemmas (Box.v, done, about 300 lines)

```coq
box_mark : skip_target q = Some r -> 9 <= length vs ->
           zc (st q) l (sepsR vs) -->* zl (st (if r =? 0 then 2 else 6)) l (sepsM r vs)
box_inc  : r < 9 -> 9 <= length vs -> zc (st 73) l (sepsM r vs) -->* zl (st 48) l (sepsR (incr r vs))
box_dec0 : r < 9 -> 9 <= length vs -> nth r vs 0 = 0 -> zc (st 43) l (sepsM r vs) -->* zl (st 3) l (sepsR vs)
box_decp : r < 9 -> 9 <= length vs -> nth r vs 0 <> 0 ->
           zc (st 43) l (sepsM r vs) -->* zl (st (if r =? 0 then 63 else 48)) l (sepsR (decr r vs ++ [0]))
```

They are built from generic forward and backward block scans parametrised by a state pair, the
skip chain, and the two shift loops. `tools/boxcheck.py` also checks them by simulation on 3,600
random files.

### 3.3 Per-site theorem (Site.v, done)

```coq
Definition D0 := 40.   (* the executor needs D >= 38; the boot gives 62 *)
site_inc : check_site Q (OInc r) = true -> forall n vs, 9 <= length vs ->
  zc (st 96) [true] (Q ++ zeros (n + (D0 - |Q|)) ++ true :: sepsR vs) -->+
  zc (st 96) [true] (inc_path Q ++ zeros (n + (D0 + ovf - |inc_path Q|)) ++ true :: sepsR (incr r vs))
  (* ovf = allones Q *)
site_dec : the two branches: (brk 1 Q, vs) if nth r vs 0 = 0, else (inc_path Q, decr r vs ++ [0])
(* todo, same proof: OBrk k -> brk k Q;  OCont k -> cont k Q;  OHalt -> reaches state 254 *)
```

### 3.4 Simulation glue (Sim.v, Main.v, done)

* **Invariant.** `Inv N T := exists P R k ext, rm_run p254 N ([], R0) = Some (P, R) /\ D0 <= |P| + k /\
  T = zc (st 96) [true] (P ++ zeros k ++ true :: sepsR (phys R ++ ext))`, where
  `phys R = map R [2;4;3;7;6;8;0;1;5]`.
* **Step.** Take `walk p254 … P = Some (e, d)`. Then:
  1. `In (pd P d, e) (leaves p254)` gives a passing check.
  2. `RMEquiv.no_stray` together with v335's `conf_split` gives
     `P ++ zeros k = pd P d ++ zeros (|P| + k - d)` (needs `d ≤ 34 < D0`).
  3. The site theorem applies with `n = |P| + k - D0` and `vs = phys R ++ ext`. Its output
     re-establishes `Inv (S N)`, with `|P'| + k' = |P| + k + ovf`.
  4. `incr`/`decr` on `phys R ++ ext` equal `phys (upd R …) ++ ext`. This is a 9-case
     computation.
* **Halt.** `at_halt` gives the halt site, then state 254, which is `halted`.
* **Final theorem.** Copy v335 `tm_halts_iff_rm` (`progress_halts`, `halts_evstep`).

## 4. Interface for the program / logic layer

```coq
From M254 Require Import RM.          (* = zf/v335/coq/RM.v *)
Definition p254 : prog.               (* Prog254.v, generated from paths.json; registers in declaration order *)
Definition R0 : regs := upd regs0 0 2.   (* nextproof = 2 *)
Theorem tm254_rm   : halts tm c0 <-> rm_halts p254 ([], R0).
Corollary tm254_iter : halts tm c0 <-> iter_halts p254 R0.   (* RMEquiv.rm_halts_iff_iter, p254_wf *)
```

`p254` is the program the TM really runs. It is the TMBuilder tree of source.py after the third
party's decoder-grammar rotations and their 339 commuted increment pairs. `../logic/` plans its L2
on Wade's own 219-node compile (`m254_wade.tm`) and a bisimulation-up-to-commuting certificate
(their option 1). That certificate should be stated between two RM.v programs:
`rm_halts p254 ([], R0) <-> rm_halts dag219 ([], R0)`. It is a stuttering bisimulation on
(path, path, pending-increment) triples, checked by computation; their estimate is about 4.5k
pairs. Because both sides use RM.v and the same register numbering, nothing else is needed. If the
logic layer prefers a flat CFG (`graph` with gotos), a corollary from `tm254_rm` is cheap
(about 100 lines: leaf ↔ site index, `goto` chains).

## 5. Measured (prototype, Coq 8.20, Idle priority, machine at 100% load)

* `all_sites_check` (8,391 symbolic runs) takes 23.7 s wall / 16.8 s CPU in vm_compute. The
  table lookup is a plain `nth_error` on a 254-element list, so this is not optimised.
* The boot (264,982 steps, `lrunp` binary step count) takes 1.5 s in vm_compute.
* Python model (`tools/symexec.py`): 1.94 M abstract steps in total, at most 331 per case.
  State 96 is visited at most 4 times before the target. Outcomes: 8,387 normal, 3 overflow
  (marker moves left), 1 halt. This matches the audit's 8,387 / 3 / 1.
* The minimum gap the executor accepts is D ≥ 38 cells between marker and header (H = D + 1 ≥ 39).
  With D0 = 37 it fails on 15 cases, where cleanup would have to peel a 1-run of length `n + 0`.
  The audit claims H ≥ 37, using its optional-empty rule (a case split on n = 0). This does not
  matter here: the boot gives H = 63 and H never decreases. We use D0 = 40.
* Also checked in the Python model: state 8 (bootstrap helper) is never entered from a dispatch
  configuration, and peek3 (5) only ever reads 0, only on zero-decrement branches.

## 6. Effort (actual)

The design estimate was about 1 agent-day for the glue. The actual cost was well under one
session: about 200 lines of Sim.v, 60 of Leaves.v, 50 of Check254.v, 40 of Main.v, plus the
generators.

Optional: a binary-trie lookup for `tmn` would cut the 22 s check. It is not needed.

## 7. Alternative considered: prove the 261 named table, then 254 ↔ 261 via certificates

Rejected, for four reasons:

* **The named table is not a clean DAG either.** It already contains contextual folds and
  routers: `extra.router.5/6`, decoder nodes jumping into return and cleanup states, and
  `node_45.0` doubling as the preparation entry. So it would need per-site symbolic execution
  anyway.
* **The certificates would need a new verified checker.** On top of that, we would have to
  formalise a checker for the four context layers (7-cell window invariants, local simulations of
  up to 17 steps), the exact quotient maps, and the composition of these simulations from the
  blank tape.
* **The direct approach covers more with less.** It needs a ~450-line executor and its soundness
  proof, and it checks the literal final table, including the merged leaf states
  (`3.X.inc`/`3.X.decnz` → 18/47/65) and the changed return path.
* **The data volume is the same.** The audit's own method is per-site affine execution, the same
  amount of data as ours.

## 8. Risks and how the design handles them

* **"Optional-empty scan rule".** It is not needed. A self-loop over `SR b a c` is one rule, valid
  for all lengths including 0 (`scanR`/`scanL` with n = 0). Peeling requires a constant `c ≥ 1`.
* **Arithmetic prefixes pass through `main().0` before they complete.** This is harmless: `exec`
  checks for the exact target configuration (PC, gap, box state), not the first visit to 96.
* **Changed `return_1_2`/read0 → peek3 path.** It is executed literally. All 1,931 zero branches
  go through peek3/read0. The bootstrap helper (state 8) is never reached from a dispatch
  configuration; if it were, the executor would simply have run it.
* **Spare tail grows unboundedly.** `ext` is arbitrary; `box_decp` appends `[0]`. Only the first
  9 blocks are ever targeted (`r < 9`).
* **Gap.** It is non-decreasing, and the overflow case is handled by the `ovf` flag of the target.
  The PC depth is at most 34 < D0 = 40 ≤ 62, so the decode never reaches the header.
* **Stray PC bits.** These are handled by RMEquiv's `no_stray` (already proved generically).
* **busycoq notation pitfalls.** `&&` means sumbool (use `andb`); use `Defined` decidability for
  `vm_compute`.
* **Trust anchor.** `Table254.v` is generated from the file, with its hash printed. `check_tm254.py`
  must re-parse the file and compare it with `table254` (as v335's `check_zf.py` does).

## 9. Tools (`tools/`, own code; nothing from drive_mike is executed)

* `tmlib.py`: parser and sparse simulator.
* `trace1.py`: phase trace.
* `boxcheck.py`: register lemmas by simulation.
* `paths_check.py`: paths ↔ graph under Wade semantics.
* `wfcheck.py`: RMEquiv `wf`.
* `symexec.py`: Python model of the executor (all sites, min-gap search).
* `gen_table.py`, `gen_sites.py`: generators for the Coq data files.
