# K226: transferring ProveIt reductions to Elliot Glazer's K230

Research contribution, 19 October 2026.

**Principal result: 226 working states, a binary tape alphabet, and a separate halt outcome.** The machine starts in state 0 on the all-zero two-way infinite tape; every transition moves left or right. Initialization is included. An ordinary mathematical proof, formalizable in ZFC, establishes

\[
\mathrm{ZFC}\vdash
\bigl(\neg\operatorname{Halt}(K226,\mathrm{blank})\leftrightarrow\operatorname{Con}(\mathrm{ZFC})\bigr).
\]

The report and exact evidence distinguish this result from a new Rocq/Lean endpoint. The inherited 230-state endpoint is formally checked in Rocq. This delivery supplies new source, local-block, initialization and unbounded symbolic-runtime proofs, with executable certificates and their ordinary mathematical soundness arguments. It supplies no new reduced-table Rocq theorem, serialized ZFC proof or internal PA derivation. It does not establish the consistency of ZFC or assert that the machine is unconditionally nonhalting.

## Read first

- [Report PDF](report/main.pdf) and [LaTeX source](report/main.tex).
- [Principal canonical table](machines/k226.tm), [inherited labels](machines/k226_old.tm), and [state map](machines/k226_state_map.json).
- [Complete final instruction catalogue](source/sites226.json).
- [Construction record](evidence/construction.json).
- [Full K226 runtime certificate](evidence/runtime226.json) and [all case records](evidence/runtime226_cases.json).

Canonical states are 0 through 225; start is 0, dispatcher 83, and halt 226. Each noncomment line of a `.tm` file is `state read write direction next_state`. The inherited-label versions use start 95, dispatcher 96 and halt 254. Some inherited working labels exceed 254; use the declared working-state set rather than assuming a numeric bound.

**Canonical K226 SHA-256:**

```text
f2c2fde39bcdb236a0ec53d5ca4867549fb5a85409a9aee38eb0cf9288f386bc
```

**Inherited K226 SHA-256:**

```text
30082fe31158b8ae049a1bf15f56acffaae71f9031642e6fa7ab75555e466be4
```

**Final source SHA-256:**

```text
200cfe32d7b16587bd56667650e5eb192c9e392a3f4764b3ec4ca4705a074f89
```

## What transfers

The two ProveIt predecessor-bit folds, 27 into 15 and 39 into 17 in inherited labels, are already present in K230. Four further state savings are obtained here:

1. **K230 → K229:** rotate the transfer-plus-one source loop at four exact occurrences, then merge 90 into 72 using the preceding tape bit.
2. **K229 → source-recompiled B229 → B228:** adapt the earlier source-boundary reduction. A constrained dynamic program reparses 49 ordered closed atoms while protecting shared decoder/helper contexts. Split 218 by the preceding bit and reuse helper 529, removing one state.
3. **B228 → K227:** apply delayed erasure, merging 169 into 80. The final runtime theorem is checked directly and does not assume an unproved all-tape right-neighbor invariant.
4. **K227 → rotated R227 → K226:** one closed source rotation at 210/177 makes it possible to merge 508 into 86 using existing helpers 182 and 177. Four one-step/three-step whole-tape identities justify the fold for arbitrary initial binary tapes.

The simpler **direct K228 companion** applies only steps 1 and 3. It is particularly easy to review: delete original K230 states 79 and 140 and replace eight retained rows, then renumber. See [the exact original-label patch](machines/k228_patch_original_labels.json). It is different from the boundary-derived B228 intermediate. The archive preserves both with distinct names.

The 49-atom dynamic program and the final rotation illustrate the useful new approach: choose source parenthesizations together with the entry tape contexts required by shared machine states. Minimizing only the abstract source DAG can break an arithmetic helper. The accepted proof checks the resulting literal machine, independently of the optimizer.

## Verification

| Property | Direct K228 | K227 | Principal K226 |
|---|---:|---:|---:|
| Working states | 228 | 227 | 226 |
| Literal transition rows | 456 | 454 | 452 |
| Source instruction occurrences | 5,121 | 5,121 | 5,121 |
| Guarded instruction cases | 6,656 | 6,656 | 6,656 |
| Symbolic rule applications | 1,614,426 | 1,591,422 | 1,596,687 |
| Maximum symbolic case length | 415 | 388 | 394 |
| Minimum concrete instruction duration | 13 | 13 | 13 |
| Maximum source depth | 40 | 37 | 37 |
| Maximum source zero-run | 6 | 6 | 6 |
| Blank bootstrap transitions | 409,835 | 409,835 | 409,835 |

Every literal row occurs in each respective complete proof. The quantified case family covers all independent natural register values, both decrement guards, any natural additional gap, an arbitrary first spare value and an arbitrary finite remaining spare list. Each nonhalting case proves the complete tape, head, state and source-successor contract. All durations are positive. The 4,000-rule limit is a bound on proof construction, with no bound on concrete counter sizes or execution time.

The initialized tape is checked in two independent representations. Its entire support has 351 one-cells; every other cell is zero. Its inherited dispatcher/head are `(96,-5)`, the marker is at −6, and the header is at 176. The logical seed is `(3,0,0,0,3,0,0,0,0)`, with 167 spare blocks of value 1 and extra gap 117. This is the actual K230 seed, not an assumed all-zero register file.

The source connection is explicit. An independent parser expands the literal Rocq `p230_tab`, obtaining exactly the released 5,125 leaves. A separate all-natural proof verifies the four loop replacements. Two independent source resolvers check the subsequent reassociations, every guarded successor and the no-stray-bit property that connects successive per-leaf runtime frames.

## Reproduce

Python **3.10 or later**, standard library only, with assertions enabled. Run from this archive root:

```sh
python3 -B reproduce.py --output-dir /tmp/k226-replay
```

This checks the shipped manifest when present, reconstructs every machine, verifies the upstream source/CI pins, source correspondences, complete startup and local folds, and freshly re-proves all 6,656 K226 runtime cases. The case records must match the shipped derivations exactly. The K228 and K227 full certificates are audited for integrity and coverage.

To freshly re-prove all three reduced runtime tables:

```sh
python3 -B reproduce.py --all-runtime --output-dir /tmp/k226-all
```

For a quick construction and finite-interface replay:

```sh
python3 -B reproduce.py --quick --output-dir /tmp/k226-quick
```

Quick mode verifies retained runtime evidence but explicitly does not rerun the universal derivations. Do not use `-O`, `-OO` or `PYTHONOPTIMIZE`. No network access or proof-assistant installation is needed for these commands.

To regenerate the report:

```sh
python3 -B report/generate_tables.py
cd report
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
```

## Pinned formal baseline

The K230 snapshot is from [elliotglazer/k230-rocq](https://github.com/elliotglazer/k230-rocq), commit `3142e4dd980f0be12f4abb636c4ae2528afc17eb`. Its machine hash is `e7ccbcec074534cfd955f0ab94d16f13594e81974074309dc2ce663b9dfd7ba8`.

The exact-commit [successful Linux workflow](https://github.com/elliotglazer/k230-rocq/actions/runs/39258562285) and its unmodified downloaded artifact are retained under `evidence/upstream-ci*`. The records match the shipped source manifest and record compilation of 216 proof sources, two closed final dependency reports, and a successful independent `coqchk` invocation. The runtime used here had no local Rocq installation; the new local audit checks the exact upstream source and CI evidence. It does not claim a local rebuild. The upstream snapshot documents its separate Rocq 9.1.0 / rocq-stdlib 9.0.0 build procedure and pinned 115-file external dependency.

The ProveIt reference is the 235-state delivery added in commit `0128d662fd46f72dc84505176ae8ec28affb2d9d`. Generic verification engines are retained byte for byte with provenance in [ATTRIBUTION.md](ATTRIBUTION.md).

## Additional research

The report compares K, raw EPSC/PSC, finite class/assignment kernels, pure equational rewriting, the cyclic E9/Df3 route and combinatory encodings, identifying the exact remaining interpreter and payload costs. The separate [E662 companion](alternatives/e662/README.txt) adds a fresh constant and changes the inherited E663 query conservatively, reducing its complete serialization from 663 to 662 bits. Its exact equations, query, proof, generator and verification are included. This does not save another K-machine state.

`discovery/` preserves the 49-atom layout problem and optional deterministic dynamic-programming replay, plus selected negative search records. Discovery is outside the logical proof dependency: the reconstruction checks the literal accepted layout and the final machine is proved independently. No claim of global state minimality is made.

## Attribution

The compact K theory and K230 formal calibration remain credited to Elliot Glazer and the K230 development. The ProveIt reductions retain their existing source attributions. The underlying calculus, proof search, formal reference and compiler retain the credits to Mira-Cult, Jeff Ketchersid, Andrew James Wade, ProveIt contributors and the named upstream libraries. See [ATTRIBUTION.md](ATTRIBUTION.md), [the retained K230 notices](vendor/k230-rocq/THIRD_PARTY.md) and their license files. No blanket license is assigned to upstream files with unspecified scope.
