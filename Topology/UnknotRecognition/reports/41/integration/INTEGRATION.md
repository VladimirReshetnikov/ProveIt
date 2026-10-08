# Proposed integration, not an applied patch

The inspected baseline is commit
`81a387aada56bb180649a98c21c078cb89efcfde`. Read `STATUS.json` before interpreting
any numbers as upstream evidence. No repository writes were performed.

## 1. Execute the source-pinned gateway

With a full local checkout:

```sh
python -B integration/check_upstream.py \
  --fast-root /path/to/ProveIt/Topology/UnknotRecognition/fast \
  --output results/upstream_gateway.json
```

The gateway refuses different Git blob hashes by default. Inspect changes
before using `--allow-unpinned`. A pass covers only the real `WordArena` bridge
and the existing selected-power formula, not the complete recognizer.

## 2. Preserve the producer/verifier separation

`prepare_step(arena, roots, alive)` imports the current literally cyclically
reduced words, solves all positive multiplier problems, and verifies the
optimization certificate. It returns a result and elementary macro records,
without modifying the list of source roots.

For an initial opt-in producer experiment, use `replay_in_arena`. It applies the
returned Whitehead records through the host's generic substitution and cyclic
reduction. Commit its returned roots and records together only after the whole
operation and the host's independent full-source replay succeed. Arena
allocations on failure are not transactional; use an isolated scratch arena or
charge abandoned allocations in the host's resource accounting.

The macro decomposition may temporarily increase length, although the atomic
result never does. No intermediate-length monotonicity or direct-constructor
rule bound is claimed for legacy replay.

## 3. Do not mix representatives

`install_prepared` bypasses generic reduction and returns a specific cyclic
rotation. Existing relator-overlap certificates refer to positions in the
legacy representative. Installing direct roots while recording only legacy
moves can therefore break subsequent replay even when the group is unchanged.

A new atomic-shear certificate version must define the root convention, signed
potential map, generator and relator identities, source presentation,
independent decorated-word replay, schema validation, and resource limits.
Only after that protocol is independently tested should direct construction be
used in maintained search. Retaining power nodes is necessary for the stated
constant-factor grammar-growth theorem; converting them after every phase
changes the representation bound.

## 4. Keep the existing fallback and defaults

The measured raw-stage advantage disappears after singleton elimination on
this small corpus, and the new step is slower on aggregate there. A bounded,
opt-in probe on highly compressed states is the supported next experiment.
Do not replace the default selected-direction policy on these data.

Benchmark baseline/control/new arms in shuffled order on real PD inputs, with
identical filters, provenance replay, time caps, and initial construction.
Record changed search traces, capped observations, full verdicts, and a second
run if the first suggests a material effect. Do not divide by a capped
baseline time. Keep the existing exact complete recognizer when the probe
stalls or exhausts its allowance.

## 5. Proof obligations before a general complexity claim

One polynomial compressed operation does not bound a complete search. Prove a
bound on the number of multiplier phases, control representation growth of
interleaved Tietze/relator operations, charge diagram-to-presentation extraction
and certification, and establish terminal completeness. The plateau family in
the article disproves completeness of strict automorphic shortening alone.
