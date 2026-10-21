# History returns, a shallower 215-state machine, and new source calculi

Date: 2026-10-21.

This packet supplies **two explicit 215-working-state, two-symbol, blank-tape Turing machines**, including initialization. It also supplies a complete source-level proof for a **201-subtree three-command transfer/cache enumerator**, and a theorem allowing **every membership-atom code** to trigger a refutation alarm.

**No accepted 214-state machine was obtained.** Source subtree counts, structurally smaller trial tables, and allocator prefix passes are kept separate from verified physical machine counts.

## Main result and proof status

For both supplied machines, ordinary mathematical reasoning formalizable in ZFC proves

    ZFC proves: not Halt(M, blank) iff Con(ZFC).

The consistency predicate and numerical-calculus calibration are inherited from the accepted repository K215 at commit

    75716498437bfc7291d5900cab2983a11fd54bac

in `VladimirReshetnikov/ProveIt`, directory `Computability/BusyBeaver/Research/ZFC/candidate-k215`.

The new proofs consist of exact local whole-tape transition blocks, literal source reconstruction and complete guarded-graph equality, fresh all-natural symbolic primitive derivations, and independently replayed complete blank prefixes. They are **not newly compiled Lean/Rocq exact-table theorems**. They do not prove unconditional nonhalting or assume Con(ZFC) in order to prove the equivalence.

## The two machines

| Artifact | Working states | Source subtrees | Source leaves | Maximum address depth |
|---|---:|---:|---:|---:|
| Pinned accepted K215 | 215 | 202 | 4,751 | 47 |
| `machine/k215-context.native.tm` | 215 | 202 | 4,751 | 47 |
| `machine/k215-shallow.native.tm` | 215 | 202 | 4,751 | 46 |

The shallow-decoder version is the principal alternative implementation. Its source changes 1,042 primitive addresses through one reassociation of three closed blocks; total address length decreases by 416. It combines this source with the five history-dependent return rewrites. It differs from the old table in 191 rows, although part of that delta is allocator relabelling. Its rooted, read-labelled, write/move-preserving transition graph is independently proved nonisomorphic to the old one.

The simpler context version is a useful proof bridge. It changes exactly these native rows:

| State/read | Old action | New action |
|---|---|---|
| 13/1 | 1 L 31 | 1 L 81 |
| 27/1 | 0 L 40 | 0 L 302 |
| 83/1 | 0 L 42 | 0 L 57 |
| 156/1 | 1 R 176 | 1 R 52 |
| 198/0 | 1 L 40 | 1 L 54 |

One- and two-transition incoming histories force the marker bits needed for six exact local blocks. Every corresponding block ends at an identical state, head, and entire tape. Strict block interiors contain no modified row. All durations are positive. This gives a composable stuttering proof from the blank start.

The completed engine census decreases from **144 to 142 protected rows**, both across 80 states. Precisely `31/0` and `42/1` lose their engine obligation; they can still be used as decoder rows. These are complete final census counts, including late primitive cases and structural blocks.

### Machine convention

- Two-way infinite binary tape, initially zero everywhere.
- Native start state 0; native halt state 254 has no outgoing rows.
- Each native table has 215 working labels and 430 rows.
- Dense tables use states 0 through 214, start 0, and separate halt 215.
- Every row writes a symbol, moves L or R, then enters its target.
- Dense dispatcher is 23; native dispatcher is 84.
- No uncounted initializer or externally supplied program tape is used.

### Exact verification

Both machines reach the same complete frame after **95,740** transitions: native state 84, head −8, header 57, gap 1, logical registers `(4,0,0,0,0,0,0,0,0)`, forty one-valued spare registers, exactly 95 one cells, and zero elsewhere. The original table reaches this frame after 95,714 transitions. Thirteen visits to one slower block account for the extra 26 steps.

Both fresh runtime runs prove all **6,176 guarded primitive cases**. The contracts cover all natural primary values consistent with each guard, arbitrary natural gap, and an arbitrary nonempty finite spare list with arbitrary tail. Unary scans and list blocks are proved by induction. Every affine duration is positive; the minimum constant term is 6. Independent receipt audits account for all 430 native rows and check exact table/source/checker hashes and complete guard coverage.

| Table | SHA-256 |
|---|---|
| Baseline native | `9683d6ed9628e6ce407c315b08f5da3d063da94e92706f275ca0f33e8272e4b2` |
| Context native | `da20914ad9bda3f75de0381f2c05a7b5e67d26199b57b870a5ea3b72511ab627` |
| Shallow native | `7dafe445beb74f66b24d4e540136b5a47d0dfc6c1b877dcb8edce1526a608537` |
| Shallow dense | `ec6091fd0d1a3b726c3134d61dd493af25907116ae050666918dc01defc88e26` |

## Source-level research results

### Transfer-pop with cache-return MP: complete source theorem

At a command boundary `(t,w,d,h)`, let `[x;v] = P(x,v)` and `I(a,b)=4P(a,b)`.

- `S` tests `h=1`; otherwise it maps `(t,[x;v],d,h)` to `(h,v,d,x)`.
- `MP(x)` sets `Y=d+x`. Success `I(t,Y)=h` returns `(0,w,0,Y)`; failure returns `(0,w,Y,0)`.
- `AX` is the unchanged dominated-calculus axiom command.

The strong compiler's new MP block reserves a zero beneath the premise work:

    DISCARD; PUSH; B_(I(A,Y)); PUSH; B_A; PUSH;
    S; S; MP(Y); S

After the premise transfers it reaches `(A,[0;w],0,I(A,Y))`; successful MP gives `(0,[0;w],0,Y)`, and the final S either detects `Y=1` or returns `(Y,w,0,0)`. This works for arbitrary natural input top and stack, including the zero aliases `I(0,0)=0` and `P(0,0)=0`.

The proof covers soundness on all raw candidate words, all axiom blocks, generalization, truth/reset, cofinal candidate encoding above the actual cutoff 4, and strictly draining candidate readers. Direct versions have **201 subtrees, 4,709 leaves, depth 44**. All eight supplied parenthesization/opcode variants have exact source reconstruction and independent CFG audits.

The physical 215-state allocation attempts for these sources did not succeed. Four individual protected-row relaxations (`26/0`, `26/1`, `37/0`, `302/0`) identify concrete selector/return obstructions, but those relaxed tables are not accepted implementations. This source theorem is kept distinct from the two verified 215-state machines above.

### Membership-atom alarm: complete semantic theorem, physical target unmet

Replacing the exact falsity test `h=1` with `h mod 4 = 1`, while retaining the same nonhalting command effect, preserves consistency-sensitive halting. Every accepted raw number is a membership atom `Rel(i,j)`. In any nonempty irreflexive native model, a constant variable assignment falsifies every such atom. Under Con(ZFC), soundness therefore rules out every new alarm value. Every old halt remains a new halt, so completeness transfers as an early-halting refinement.

The exact all-natural four-phase scanner yields a **206-subtree** source. No accepted 215- or 214-state binary implementation is supplied for it.

The separate **205-subtree parity/disequality experiment is uncalibrated**. Its negative equality code introduces variable 0 syntactically through the false witness. Its support-sensitive bundle and binder obligations remain open; it is explicitly excluded from the accepted equivalences.

## Reproduction

Use Python 3.10 or later, **without `-O` or `PYTHONOPTIMIZE`**, because some inherited and source checkers use assertions. Standard-library verification needs no solver or network access.

```sh
python3 code/verify_context.py
python3 code/audit_shallow.py
python3 code/audit_runtime_receipts.py
python3 research/verify_cache_transfer.py
python3 research/build_cache_transfer.py
```

The last command reruns labelled finite full-command regressions; their successful results supplement the separate all-natural proof. Runtime receipts contain all per-guard records, not every intermediate symbolic trace. To recompute the quantified derivations:

```sh
python3 code/runtime-inputs/validate_native.py \
  machine/k215-context.native.tm machine/sites215.json \
  reproduction/context-runtime

python3 code/runtime-inputs/validate_native.py \
  machine/k215-shallow.native.tm machine/sites-shallow.json \
  reproduction/shallow-runtime
```

Run `make pdf` to build the paper. `make check` runs the quick finite checks. `make runtime` reruns both full symbolic runtime derivations. The allocation research is optional and additionally requires NumPy/SciPy. The frozen tables do not depend on rerunning a nondeterministic MILP search.

To reproduce the final restricted physical search, including all 336 rejected structural214 trials:

```sh
python3 research/search_contextual_fusions.py \
  --table upstream/k215.native.tm \
  --sites machine/sites215.json \
  --engine evidence/engine-baseline.json \
  --mapping code/runtime-inputs/inputs/legacy_mapping.json \
  --witnesses research/engine_row_witnesses.json \
  --support-dir code \
  --runtime-dir code/runtime-inputs/runtime \
  --output reproduction/fusion-search
```

This search takes roughly a minute or two on the construction environment. It emits a hash-bound receipt; rejected tables are not written unless `--keep-trials` is explicitly supplied. A symbolic-filter rejection is not a lower bound or proof of impossibility by every other method.

The historical `__main__` demonstration in the verbatim upstream runtime helper is not a portable entry point; use `code/runtime-inputs/validate_native.py` as shown above. Its imported proof routines are unchanged and hash-bound.

## Packet map

- `report.tex`, `report.pdf`, `sections/`: paper, mathematical proofs, and generated complete dense transition table.
- `machine/`: exact native/dense tables, source sites, and dense-label bijections.
- `code/`: independent finite checkers, allocator, and the unchanged upstream symbolic runtime implementation.
- `evidence/`: exact local blocks, complete compressed startup traces and per-guard records, input hashes, census, and independent verification receipts.
- `research/`: complete source proofs, source builders/auditors, clearly scoped experiments, and finite-search records.
- `upstream/`: frozen accepted table/source and inherited proof/calibration material. Original relative repository links in verbatim upstream documents refer to the pinned repository layout.
- `licenses/`, `LICENSE`, `NOTICE.md`: inherited terms and contribution provenance.
- `SHA256SUMS`: hashes for the complete archived packet, except the manifest itself.

## Provenance and novelty scope

This is an additive research contribution, prepared with AI assistance. The numerical calculus, its calibration to ZFC, the runtime framework, and the existing cache-return/transfer-pop antecedents are inherited and credited. The exact new engine rewrites, shallow allocation/source combination, protected-zero compiler composition, semantic-alarm theorem, and supplied independent finite checks are the contributions of this packet.

The newest incoming binary ZIP submissions could not be inspected through the available GitHub text interface. Novelty comparisons are therefore limited to the integrated source material inspected at the pinned commit. In particular, this packet does not claim global priority, a new axiomatization of ZFC, an achieved 214-state machine, or a lower bound ruling one out.
