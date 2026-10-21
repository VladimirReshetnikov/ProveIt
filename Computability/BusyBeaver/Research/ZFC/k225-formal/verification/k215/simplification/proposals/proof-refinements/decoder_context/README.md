# Automatic decoder-context propagation for K215

## New checked result

`K215Context.every_internal_source_path` closes the **intermediate window-witness** obligation left open by the incoming checked decoder packet. It proves a complete arbitrary-tape statement for every internal path of that packet's concrete 202-node source DAG. The caller supplies only the start marker and the actual pointer bits; no `Chain`, `Route`, or per-edge tape-window witnesses are required.

Let `p` be any bit list whose traversal from source node 201 ends at an internal node `m`. Let `t : Int → Bool` be an arbitrary complete tape, `a` an arbitrary integer, and suppose:

1. `t(a - 1) = true`;
2. the successive cells `a, a + 1, ...` contain the bits of `p`.

Then there exist a decoder role `f` and a number `n` such that:

* `f.node = m`;
* the exact supplied native K215 table runs from `(84, a, t)` to `(f.state, a + length(p), t)` in `n` steps;
* the suffix context required by `f` holds at the endpoint;
* if `p` is nonempty, `n > 0`.

The final tape is literally the **same whole function** `t`. Cells outside the inspected windows are unrestricted. Empty paths have the expected zero-step case. `prefix_sound` is the lower-level interface for successful finite role lookup.

## What is new relative to the incoming packet

The following three files are inherited without a byte change from `docs/incoming/K215_Checked_Simplifications_2026-10-21.zip` at repository commit `aa66d0a33f1f8237a348899eb8095b045a502832`:

* `FramedWindow.lean`;
* `DecoderCertificate.lean`;
* `K215Decoder.lean`.

That packet already proved restoration by 281 local blocks and composition of a `Chain`. Its `Chain.more` constructor required the caller to prove a translated window fact separately at every edge. Its README explicitly left source paths producing those window witnesses open.

The new `DecoderContext.lean` defines a tiny, finite **cell-inclusion check**. At a role `r` and current bit `b`, the known cells are the stored suffix immediately before the head, together with `(0,b)`. For each internal edge, two inclusions are checked:

1. these known cells imply the selected block's execution window;
2. they imply the successor role's preceding cells, translated back by one position.

`covers_sound` proves that finite inclusion implies the corresponding whole-tape fact. `internal_context_sound` then composes the inherited block theorem with the two inclusions. Induction gives `route_sound`; the executable `follow` function has a proved `follow_route` theorem, so callers do not construct routes by hand.

Finally, `sourceCheck` checks the linkage between internal source children and decoder roles. `source_path_follow` proves that every path ending at an internal source node has a successful role traversal. The concrete `K215Context.lean` kernel-checks both finite checks and composes them with the exact inherited block proof.

## Scope and production integration boundary

This is a new, compiled universal theorem for the supplied concrete source DAG and native table. It is not a rebuilt ZFC endpoint and does not replace `KSites215` yet.

The remaining production adapter must bind the standalone native/source data to the upstream `KTable215`/`KSource215` definitions in the kernel, transport the full-tape statement to the production tape representation, and attach primitive dispatch, register-box semantics, pointer-return contracts and complete site coverage. In particular, this theorem stops at an internal decoder role; the edge entering a primitive and the primitive's return remain outside its statement. The original `KSites215` proof remains available throughout migration.

The supplied finite audit independently compares all source occurrences with the pinned `sites215.json`. That byte/data binding is ordinary executable evidence, not the missing in-kernel production identity. No Lean kernel speedup, full-checker workload reduction, or state reduction is claimed.

## Counts and verification

The new finite checks inspect 234 roles and 468 role branches. There are 371 internal role edges, hence 742 semantic cell-inclusion obligations; 97 primitive role edges are deliberately excluded from these new semantic obligations. The source expands to 4,750 internal occurrences and 4,751 primitive occurrences. There are 4,749 internal occurrence edges. The finite audit finds a maximum internal prefix of 46 bits and 55 concrete machine steps.

A final **fresh, serial build** compiled six modules: the three inherited foundations, the two new modules and the typed `Audit.lean` client. It used Lean 4.32.0, commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`, and took 37.079 summed compiler seconds in this environment. This is an absolute build observation, not a performance comparison. All six invocations returned zero with zero warnings. The principal new semantic theorem depends only on `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` or native evaluator is used. The input block-acceptance theorem remains axiom-free.

Five concrete malformed controls are kernel-checked: missing predecessor fact, false predecessor fact, wrong successor suffix, missing successor role, and treating a primitive source node as a parent. The Python audit independently rejects the first four and validates the source linkage globally.

`verification/fresh-build.json` binds each source, compiled object and compiler log. The compiled objects are deliberately omitted from the deliverable; they are regenerated by the build script. `verification/context-audit.json` records independent parsing, context checks and all source occurrences. An audit parser initially treated the halt-node's numeric placeholder as a meaningful argument; correcting its comparison to the supplied `CH, null` schema resolved that parser-only mismatch. It did not change a Lean source or theorem.

## Reproduce

From this directory:

```sh
python3 audit_context.py
python3 build.py --lean /absolute/path/to/lean --out /tmp/k215-context-fresh
```

The build output directory must contain no preexisting proof objects. The script uses only this packet's sources plus Lean's installed standard library, compiles serially, records all results and rejects nonzero exits, warnings or `sorryAx`. It does not import the existing project cache.

## Frozen source identities

| File | SHA-256 |
| --- | --- |
| `DecoderContext.lean` | `2fe8e5c38afe3bbb22cb6b98b7b65425d30d917d2f2ffc896264d2b0080c4a53` |
| `K215Context.lean` | `c31abe4c595cc4b970dfff745ffaf8eba23a03f96323c0030c251cb7ba8c74be` |
| `Audit.lean` | `cb14ee581fa4e2b0a107653e95d7731a61b007fdb67ca8f41f9654804f5b9774` |
| inherited `K215Decoder.lean` | `8e7c09265fd32217ccedc822138572345b4f8add667d114443a4209666a2ac91` |
| inherited decoder-product JSON | `9dc3d2fb25020992de466b2d91eb15f00539da585d9e6219bb372e6352c7beff` |
| pinned `sites215.json` | `17af207195179b2508bf91154cd00739374f8862207ca21b9a3cb9098aa6f5ba` |
