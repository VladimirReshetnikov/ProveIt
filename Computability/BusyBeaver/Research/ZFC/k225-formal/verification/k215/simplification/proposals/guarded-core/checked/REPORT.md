# Review: K215 Checked Simplifications

## Bottom line

The new packet closes three previously open formalization gaps. It records a concrete 1,426-entry normalized Rocq source proof, Lean arbitrary-tape decoder-block refinement and chain composition, and a concrete Cantor-codec zero-credit injection. The first result includes a completed recursive source-closure check, unlike the earlier compact ordinary Rocq packet. It does not rebuild the full production endpoint, replace the complete runtime proof, or establish a 214-state machine.

This review independently verified source/log bindings and reimplemented finite data/decoder checks. It did not rerun a proof assistant or execute any received program.

## Exact intake and source scope

- Repository: VladimirReshetnikov/ProveIt.
- Intake commit: `aa66d0a33f1f8237a348899eb8095b045a502832`.
- Archive: `docs/incoming/K215_Checked_Simplifications_2026-10-21.zip`.
- Git blob: `5e489899fef825c91bcbf2889d68ece6238f2251`.
- Archive SHA-256: `18ec63a7a07bb5614e5002261fe1ce02f219ae0925e7b713df67868663bdb60b`.
- Size: 1,845,732 bytes; 194 members; 2,752,810 uncompressed bytes.
- The package itself used the older repository pin `53269bcab1efc0f82d3022645bd7cf0c22d84959`.

[Verified intake commit](https://github.com/VladimirReshetnikov/ProveIt/commit/aa66d0a33f1f8237a348899eb8095b045a502832) adds exactly three incoming ZIPs. The parent also verified the complete `0359ebda60aaf52758358e1450a04988136db67e` to `aa66d0a` comparison: one commit, exactly those three added ZIPs, and no other files. Production Rocq therefore remains unchanged from the already-reviewed phase-five matrix. The checked packet's arrival is not source integration. [Exact archive](https://github.com/VladimirReshetnikov/ProveIt/blob/aa66d0a33f1f8237a348899eb8095b045a502832/docs/incoming/K215_Checked_Simplifications_2026-10-21.zip).

The GitHub text connector could verify the blob but not decode the binary. After the parent materialized it through an authorized read-only route, this review independently recomputed the Git object hash and SHA-256, checked paths and member types, and extracted only as data. All 193 entries of its `SHA256SUMS` match; the manifest appropriately does not hash itself. Earlier sealed files were not modified.

## 1. The normalized Rocq port is now an existing checked result

Members `normalized_rocq/NormalizedBisim.v`, `NormalizedCert215.v`, and `NormalizedSource215.v` implement the previously proposed 2,240-to-1,426-entry reduction in Rocq. `p215_dagPerm_normalized` proves, for every register file R:

`rm_halts Prog215.p215 ([],R) <-> rm_halts DagPerm.dagPerm ([],R)`.

This is ordinary register equality, one finite check, and an automatic mirrored reverse proof. `ibeq_ok` proves trailing-zero equivalence; the soundness proof uses existing `hn_ipeq` only on completed segment endpoints. Break/continue and increment operations still act on the original interpreter's consumed leaf paths. There is no arbitrary suffix erasure or physical tape compression.

`verification/result.json` records Coq 8.18.0, twelve fresh source/dependency compilations, and recursive `coqchk NormalizedSource215` exit 0. It records 80.632 summed compiler seconds and 521.235 seconds for the separate recursive check. `verification/interface-result.json` separately records successful compilation of the same-name `K215F.Source215.p215_dagPerm` facade and explicit typed client, each closed under the global context. These are focused measurements, not controlled speedup comparisons.

Independent binding established:

- All twelve delivered source hashes match. The private Coq 8.18 `RMEquiv.v` differs from the supplied Rocq 9.1 original by exactly the disclosed `Require Import Compat818.` addition, and the reconstructed compiled-source hash matches.
- All thirteen primary step/log pairs and both facade/client source/log pairs match; each recorded exit is zero.
- The additional generic recursive-check log and driver hash also match.
- Every one of the 1,426 Rocq rows decodes to the exact corresponding JSON paths and successors. Lean-style and Rocq-style path bit orders differ, so direct integer equality would have been the wrong test.
- Supplied `Prog215.v` and `DagPerm.v` are byte-identical to the independently fetched prior production snapshot and current intake-commit production. Fresh connector reads at `aa66d0a` returned Git blobs `c74df29d0e0d3c9c91d46b3cda73c3563b7f2058` and `74a1715ff35e2b1abbf0cb5f58efdf2aafb1ef6b`, respectively; both recompute exactly from the packet copies. `BisimMirror.v` and `PathCodec.v` match the already inspected compact-source proposal.
- Normalized certificate plus retained codec measure 109,958 bytes, versus the earlier 173,003-byte compact ordinary data/codec pair. This is source-data size only.

Important source SHA-256 values:

- `NormalizedBisim.v`: `54e6dd78fce3a0621f64008d48bd4bb7eeb9bd3394e00865ad8f7b868372e38c`.
- `NormalizedCert215.v`: `5744d146fe58f5cb4d59db06e140003522d23f72990513d4f01e28cabec07bfd`.
- `NormalizedSource215.v`: `6b62e09e3b7e227c82fb9a565b0d911d1efa5532e01c32523304db562400aecd`.
- Shared normalized JSON: `6d30d89253629525b0af3066c7fec67b052c07413938fc7a94dd96ab1ff406e2`.

### Remaining gates

The next task is integration, not another port: preserve the exact public facade, update maintained generators/load paths/manifests, replay on production Rocq 9.1, rebuild `Correct215` and `CorrectDense215`, and inspect final endpoint assumptions. The receipt is for Coq 8.18, not proof that the unexecuted 9.1 branch builds. Neither this source-layer receipt nor the typed client is a full binary-machine-to-ZFC rebuild.

## 2. Decoder contracts are stronger than the older finite proposal

Three Lean 4.32.0 modules record successful fresh compilation:

- `FramedWindow.lean` proves that a bounded local execution, which rejects unspecified reads, refines arbitrary integer-indexed tapes and restores the entire exterior tape.
- `DecoderCertificate.lean` proves positive local blocks and generic finite `Chain` composition.
- `K215Decoder.lean` instantiates all 281 blocks and 234 guarded roles. `all_blocks_checked` is recorded axiom-free; semantic results use only `propext`, `Classical.choice`, and `Quot.sound`.

All three source/log hashes match their receipt. Independent parsing and replay also bound all 430 literal machine actions, 202 source nodes, 234 roles, 371 internal edges, 97 primitive-entry edges, and expansion to all 4,751 source leaf occurrences. Every one of the 281 blocks passes. Four independent malformed variants for every block are rejected: zero duration, wrong exit, one fewer step, and missing leftmost known cell, for 1,124 rejections.

Key hashes:

- `FramedWindow.lean`: `bb804582294e23ee8fd731fd522612a366d25fb86078db499cd67448dc536494`.
- `DecoderCertificate.lean`: `659d68c03a190f049719051f33e875f8295ffbb930d0d100fb04599a4f970006`.
- `K215Decoder.lean`: `8e7c09265fd32217ccedc822138572345b4f8add667d114443a4209666a2ac91`.
- Native table: `9683d6ed9628e6ce407c315b08f5da3d063da94e92706f275ca0f33e8272e4b2`.

### Genuine next simplification: derive the Chain witness

The current compiled `chain_sound` assumes a `Chain`, including each window premise. It does not derive that witness from `structuralCheck`. The finite structural checker already enforces a strictly decreasing source-node number on every edge, and every internal block restores the tape while advancing exactly one cell. Consequently the next theorem can construct the witness by induction on that node number rather than exposing `Chain` as another caller obligation.

For a role with a matching suffix behind the current head, select the edge using the current tape bit. Its block word is a suffix of the stored suffix plus that bit, so the local window premise follows. The target suffix is the last two bits of the same word, and restoration preserves the needed facts. Strict node decrease provides well-founded termination. Starting at role 0 requires only q84 and the preceding true bit; a source path determines the leaf and exact first primitive transition.

This review additionally replayed all 4,751 expanded source paths with precisely that root guard and the source path bits. It independently checked 170,627 literal transitions. The exact maximum is **56 steps through the first primitive transition**, comprising at most 55 internal-block steps; source path lengths range from 3 to 47. A separate weighted role-DAG dynamic program agrees with the exhaustive path maximum. The two worst paths and distribution are saved in `DECODER_PREFIX_RESULT.json`.

This is ordinary finite evidence supporting the theorem plan, not a freshly compiled universal theorem or a whole-runtime bound. The first primitive transition is not full primitive semantics. Full source-path binding, primitive contracts, register boxes, changed path data on return, and complete site coverage still need proof. The 281 blocks do not replace the 6,176 original runtime obligations.

### Relationship to our pending proposals

The 180-role quotient remains an additional possible reduction, but it must retain the union of suffix guards and refine this existing checked 234-role interface. Arbitrary-tape block soundness and generic chain composition should no longer be listed as entirely missing. The q2 home scanner is complementary: it compresses long returns, whereas these blocks share small dispatch segments. Derived DAG summaries, named lower calibration, and relaxed terminal-drain hypotheses are not supplied by this checked packet.

## 3. Concrete zero-credit proof, not just a generic injection hypothesis

`zero_credit/TagLowering.v` constructs the actual Cantor pair codec, executable parser and both inverse laws. It proves the tag-lowering map strictly decreases the scheduler index and is injective on NIP occurrences, then derives zero credit for every finite scheduler prefix and strictly positive available credit immediately before any NIP. This is stronger than the old generic proof that assumed those map properties.

The source hash is `c5074d499f176bfaac8b0a19c5823a96061b42193af00b65b28efaf4c8d7c133`; it matches the receipt. The supplied compilation log contains five closed assumption reports, and the receipt records both compiler and recursive-check exit 0 under Coq 8.18. No project premises or AX-credit hypotheses are needed for these counting theorems.

The useful next proof is an adapter from the actual ZC215 scheduler/refill semantics to this parser/prefix model, retaining the opaque tail and correct top/cache/physical frame. It is not another proof of an assumed abstract injection. The theorem does not by itself show command correctness, exhaustive search, binary simulation, whole-tape initialization, or ZFC calibration. No unconditional nonhalting or state reduction follows.

## 4. Search evidence remains a bounded negative result

The archive records two merged pairs with one new selector, allowing temporary tags and revisits of changed controls, across eighteen frozen 215-state inputs. The exact recorded scope is radius 5, 64-step old/new traces, 10,088 families and 213 squared provider choices per family: **457,682,472 assignments, zero accepted folds**.

This review bound all eighteen table and uncompressed invariant hashes, verified the count arithmetic, and matched all thirteen extension log hashes. It did not rerun the exhaustive search or independently reprove its invariant domains. Its zero is not a nonexistence result for 214 states, unrestricted selectors, longer traces or larger windows. The synthetic 11-to-10 positive control is not a ZFC machine.

## Recommended priority changes

1. Move normalized Rocq from “formalize the port” to “production integration and endpoint audit”. Keep the existing Lean normalized lane separate from current ordinary phase-five production until deliberately integrated.
2. Reuse the checked finite-window library and prove the source/role-driven Chain construction. Then evaluate the 180-role quotient and q2 scanner against the same exact runtime interface.
3. Use the now-concrete zero-credit theorem as an input to a source-scheduler safety adapter, not as proof that the physical ZC215 machine is already verified.
4. Keep the DAG-summary fold, named-calibration reduction and terminal-drain API as independent candidates. This ZIP does not supersede them.
5. Do not repeat the same bounded 214-state synthesis family without a materially changed search grammar or invariant precision.

## Artifacts and limits

`INDEPENDENT_AUDIT.json`, `SEARCH_RECEIPT_AUDIT.json`, and `DECODER_PREFIX_RESULT.json` contain this review's results. `audit_received.py` and `check_decoder_prefixes.py` are new independent data-only checkers, not received scripts. `FILE_MANIFEST.json` inventories every extracted member. `COMMIT.json` and `INTAKE_STATUS.json` bind the intake.

No incoming executable was run, no compiler was installed or invoked, no object hash was reproduced, and no repository mutation occurred. All compiler/kernel success statements above describe recorded evidence with verified source/log bindings, not an independent compiler rerun.


## Portable replay and fail-closed controls

The owned `audit_received.py` and `check_decoder_prefixes.py` reject `-O`, `-OO`, and every nonempty `PYTHONOPTIMIZE` setting before checking or writing results. The main audit pins the received manifest; the prefix audit pins its three exact inputs. Four prior comparison snapshots are bundled in `comparison_inputs/` with their original commit, path, verified URL, Git blob and SHA-256 identities. The audit no longer accesses any earlier research directory.

`test_portability.py` copies this entire component to an isolated temporary directory and runs only the owned checkers from an unrelated working directory. `PORTABILITY_VALIDATION.json` records four successful relocated/recovered runs, twelve explicit optimization-mode rejections (including `-E` with an optimization environment variable), and six changed-input rejections. Rejected runs leave existing outputs unchanged. The changed-input controls operate only on temporary copies. All 194 original extracted archive members were rechecked against `FILE_MANIFEST.json` after testing and remain unchanged.
