# Source-path soundness for the shared K215 decoder

This component closes two obligations left in the `K215_Checked_Simplifications_2026-10-21` decoder packet:

1. A source-DAG path now *constructs* every local window premise in its block chain, from only the marker and source word on the actual tape.
2. The certificate's expanded 202-node source DAG is kernel-proved equal to the repository's literal `KSource215.t215`; the result is composed with the repository's `RegisterPath.walk` semantics.

The exact repository pin is `aa66d0a33f1f8237a348899eb8095b045a502832`. The inherited 281 blocks, 234 roles, exact native K215 table, and their three proof modules are unchanged. The new proof reuses `K215Decoder.structure_checked` through a generic `edgeSpec_of_check` theorem, so no second literal structural certificate is needed.

## New endpoint

`DecoderSourceBinding.upstream_walk_reaches` assumes that the repository walk consumes `d` bits and reaches source primitive `e`, that the marker immediately before the current head is one, and that the tape contains those `d` consumed bits. It proves that the exact native K215 decoder:

- reaches a primitive entry bound to `e`;
- leaves the complete integer-indexed tape unchanged;
- ends at the final consumed bit, at head position `a + d - 1`;
- takes some `N` steps with `d - 1 <= N <= 7 * (d - 1)`.

The surrounding tape is arbitrary. Implicit zero padding and truncation in `RegisterPath.consume` are included in the adapter.

`source_tree_eq` is proved by kernel reduction (`rfl`) and has no axioms. The semantic endpoint reports only `propext`, `Classical.choice`, and `Quot.sound`. The build uses no `sorry`, `admit`, or `native_decide`.

## Scope and next integration step

This is a decoder traversal theorem, ending **before the primitive action executes**. The 97 primitive-entry bindings, register operation contracts, pointer return behavior, native-to-K230-label/zipper semantics adapter, and semantic replacement of `KSim.Covered` remain to be connected before this can replace `KSites215`. The theorem does not reduce the number of working machine states or independently rebuild the complete nonhalting/Con(ZFC) endpoint.

The useful next proof architecture composes this shared traversal with context-parametric primitive-and-return contracts, then supplies the resulting semantic coverage to the existing register-machine simulation. This removes repeated decoder-prefix proofs across the source's 4,751 primitive occurrences.

## Reproduce

With official Lean 4.32.0 installed:

```sh
python3 build.py --lean /absolute/path/to/lean --out /tmp/k215-source-paths-fresh
```

Use a nonexistent or empty output directory. The driver validates the packaged source identities, copies sources into that directory, and compiles all 15 modules from source. No Mathlib checkout or prebuilt project objects are required. It records compiler output and per-module source/object/log hashes. The `verification` folder records a successful same-session closure: ten upstream modules built from source, three inherited decoder modules built from source, and a final recompilation of the two new modules against those exact objects. It binds the source, object, and imported-object hashes. A subsequent attempted single fresh replay passed its first eight modules but was terminated by the operating system (exit −9) while rebuilding `KSource215Data`; it is recorded as a resource failure, not as a successful fresh replay. The supplied driver defaults to one worker and a 4 GiB memory limit and preserves partial receipts on failure.

The `reference` directory contains ten unchanged upstream modules needed for the exact source identity. Their hashes and origin are recorded in `source_index.json`. The three inherited decoder modules retain their original content; the two new modules are `DecoderPaths.lean` and `DecoderSourceBinding.lean`.

See `report_section.tex` for a detailed explanation suitable for inclusion in the surrounding report. The repository license is retained in `LICENSE.ProveIt`.
