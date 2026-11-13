# A startup-preserving 197-state candidate

This experiment produces **no state-count improvement** over the 196-state baseline. It preserves the exact 58,154-step blank-tape startup and passes executable symbolic checks for every instruction of the zero-transfer specialization starting from all supported root frames with header offset at least 48. These computations are not Lean kernel certificates or proofs inside PA; they do not establish a new `Con(PA)` equivalence or a smaller machine. The external consistency proof and the missing proof-transport direction for PA196 remain separate questions.

The candidate has 197 reachable working states and 394 rows. Its native SHA-256 is `9f8c37af1f206f17c5e6773df07a82d694b09454f295f53621fbb8ce00079f66`. Relative to the pinned native PA196 table, the only changed old row is `(164,1)`, which formerly wrote 1, moved right, and entered state 98 and now writes 1, moves right, and enters the new state 2000. The two rows of 2000 are new. The candidate is emitted with all other original rows unchanged.

## How the checks fit together

`check_startup.py` independently executes both concrete tables from the all-zero tape and compares their entire configurations after **every** transition. It checks both end in native state 84 with the same tape after step 58,154. It decodes that exact tape: source path `100000`, offset 48 from the root head to the header delimiter, nine physical registers `[0,0,0,0,0,0,2,0,0]` (source registers `[2,0,0,0,0,0,0,0,0]`), and 26 spare blocks, each of value 1. The first spare and its remaining 25-block tail satisfy the runtime checker's nonempty finite-spare condition. Site 25 is path `100000`, operation `CD 8`, in both the original and the specialized source. The source JSON files are independently checked against the pinned Lean program by `../allocator-screen/independent_inputs.py`.

`../verify_zero_transfer.py` independently checks the zero/positive invariant at source level and both ordinal CFG resolvers: the initial register vector forces the deleted test at old site 3773 to take its zero branch, with old sites 3774 and 3775 unreachable. The deletion yields the 3,809-instruction source in `../allocator-screen/one.json`, with the original site 25 retained unchanged. See `../ZERO-TRANSFER.md` for the proof and its scope. This is a computed certificate, not a formal PA derivation.

`check_runtime48.py` rederives the inherited U208 symbolic engine's contracts against the exact candidate and the specialized source at header offset **48**, matching the concrete startup rather than merely the previously explored offset 56. It covers arbitrary primary register values and arbitrary nonempty finite spare lists, for all 3,809 source instructions and all 4,955 zero/positive branch cases. It covers all 394 candidate rows, counting the separate generic block lemmas. Every contract verifies a positive duration. The checker reports an executable induction over unary blocks, not an independently kernel-checked proof. Its gap-48 control on the unmodified PA196 table covers all 3,812 instructions, 4,959 branch cases, and 392 rows. The resulting reports are `runtime48.json` and `runtime48-baseline.json`; `runtime56.json` is the earlier, weaker candidate check.

## Reproduction

Run from this directory with Python 3.13.14 (the checks do not need Z3). Do not use `python -O`, since the inherited symbolic engine relies on assertions. Each full runtime check took about two minutes on the original host. Reports include elapsed time, which naturally varies.

```sh
python ../allocator-screen/independent_inputs.py
python ../verify_zero_transfer.py
python check_startup.py
python check_search_inputs.py
python check_runtime48.py --machine candidate.native.tm --sites ../allocator-screen/one.json --mapping ../allocator-screen/legacy_mapping.json --output /tmp/pa197-runtime48 --expected-states 197
python check_runtime48.py --machine ../allocator-screen/pa196.native.tm --sites ../allocator-screen/original.json --mapping ../allocator-screen/legacy_mapping.json --output /tmp/pa196-runtime48 --expected-states 196
```

`check_runtime48.py` adapts `../allocator-screen/check_runtime.py` only by setting the runtime engine's `HEADER_BASE` to 48, checking/reporting that value, and loading its pinned engines from the sibling directory. The original engine bytes are unmodified; the wrapper checks their SHA-256 hashes. Upstream credits, licenses, archive pins, and inherited code provenance are preserved in `../allocator-screen/README.md` and `../allocator-screen/provenance/`; none of the upstream authors is implied to have endorsed this new experiment.

## How the candidate was found

`protected-startup.txt` contains the 237 distinct original transition rows exercised by startup together with the 98 core rows from the preceding allocator screen; their union has 238 rows. `check_search_inputs.py` independently regenerates this set from the literal baseline table. The allocator then adds compatible decoder-helper rows, yielding 259 protected rows in this run. The recorded run used Python 3.13.14, `z3-solver==4.15.8.0`, 20 seconds of solver timeout, feasibility mode, and one available fresh state. Reproduce the restricted search (different models can be returned) from this directory with:

```sh
python ../allocator-screen/allocate_current.py ../allocator-screen/one.json /tmp/pa197-allocation --protected protected-startup.txt --seconds 20 --feasible-only --fresh 1
```

`allocation.json` records the actual original result, including source hash and assignments. Its path points to the original scratch run and is descriptive only. With zero fresh states, the same startup-protected restricted model produced an empty domain; that says nothing about other allocation strategies.

## Local-fold screen

`dense.tm` is a dense-label conjugate of the exact candidate, with starting state 0 and halt 197. `dense-map.json` records dense-to-native working-state labels, and `check_search_inputs.py` validates every transition and the SHA-256 `4ba0c5f88f9898d7765ce8107c25db65588f231a7825175037b077b3f4982db4`. The preserved `scan197.py` is `../../search/scan_local_folds.py` specialized to 197 working states and the dense table hash, with its docstring and domain error updated; its two-predecessor screen tested 59,954,980 one-row patches across 76,085 prefiltered fold/read cases, allowing up to 16 transitions on each five-cell context. It found no direct fold, nontrivial bisimulation class, or one-row-patch survivor. The radius-4 blank-window variant reached 26,019 abstract configurations, with abstract halt reachable, and tested 59,971,528 one-row patches without a survivor. See `folds-two-predecessor.json` and `folds-window4.json`. These are narrowly defined negative screens, **not** lower bounds against other folds or constructions. Reproduce with:

```sh
python scan197.py --table dense.tm --invariant two-predecessor --output /tmp/pa197-folds.json
python scan197.py --table dense.tm --invariant blank-window --radius 4 --output /tmp/pa197-folds-window4.json
```
