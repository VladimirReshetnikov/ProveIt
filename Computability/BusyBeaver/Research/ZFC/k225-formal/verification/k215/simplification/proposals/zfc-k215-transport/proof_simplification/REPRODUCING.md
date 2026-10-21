# Reproducing and adopting the proof-simplification pilots

This directory is designed to remain usable after it is renamed or copied. Run
commands from the extracted `proof_simplification/` directory, or from a writable
copy of it. The shipped receipts and logs record the checks performed for this
research package. Running a driver again can replace its receipts and logs, so
use a copy when preserving the published evidence matters.

The repository snapshot used for these artifacts is:

```
b6c7087477e51c017003bd729e712c8969733223
```

The source pilots are proposed changes. They have **not** been substituted into,
or checked through, the full upstream K215 endpoint dependency closure.

## 1. Versions and the scope of the checks

The standalone Lean checks used **Lean 4.32.0**, release commit
`8c9756b28d64dab099da31a4c09229a9e6a2ef35`. They import only the core `Init`
library. Mathlib and the ProveIt project dependency closure are not needed for
these standalone checks.

The standalone Coq checks used **Coq 8.18.0**, built with **OCaml 4.14.1**.
Both `coqc` and the independent recursive `coqchk` check succeeded. The
repository's intended lane uses **Rocq 9.1.0 with rocq-stdlib 9.0.0**. The Coq
8.18 results are not a replacement for rebuilding with that pinned upstream
Rocq installation. The sources use `From Coq Require Import ...` for compatibility
with the compiler actually used here.

| Artifact | Check performed in this package | Important remaining boundary |
| --- | --- | --- |
| `PositiveStuttering.lean` | Lean 4.32.0 checks the generic transport theorem; its reported axiom set is empty. | Its theorem must be instantiated with a particular machine's invariant and exact transition obligations. |
| `PositiveStuttering.v` | Coq 8.18.0 compiles the generic transport theorem, reports closed assumptions, and passes `coqchk`. | Replay with the repository's pinned Rocq version before adoption in that lane. |
| `pilot/SharedTreesAudit.lean` | Lean 4.32.0 checks both equalities between original literal trees and shared trees by definitional equality, with no axioms. | This is a standalone syntax audit, not compilation of the replacement project module and its clients. |
| `rocq_pilot/Cert215CompactAudit.v` | Coq 8.18.0 checks equality of the entire original and compact 2,240-entry certificate lists by reflexivity, with closed assumptions, and passes `coqchk`. | Rebuild the replacement project module and all dependent correctness endpoints with pinned Rocq. |

No checking-time or peak-memory improvement is claimed. The measured reductions
are reductions in generated source bytes, with the mathematical values
preserved. The package does not include compiled `.olean`, `.vo`, `.vos`, `.vok`,
`.glob`, or `.aux` files.

## 2. Prerequisites and executable paths

Use Python 3.10 or newer, Lean 4.32.0, and a complete Coq 8.18.0 installation
including its standard library and `coqchk`. Place their executables on `PATH`.
The commands below pass **absolute executable paths** to the Python drivers.
This avoids ambiguity when a driver changes its working directory and also
works with drivers that resolve a `Path` argument before invoking a compiler.

In a POSIX shell, check the installations with:

```sh
python3 --version
lean --version
coqc --version
command -v lean
command -v coqc
command -v coqchk
```

`coqc` and `coqchk` must belong to the same installation. If using a compiler
extracted from distribution packages rather than an ordinary installation,
configure its library-search environment before running these commands. The
package's scripts deliberately do not embed the original machine's temporary
toolchain paths or environment.

The generators' default reference-input and output locations are relative to
the script file, not a fixed checkout directory. The commands here give
explicit output directories for the data pilots so the published pilot source
and receipts remain untouched. They require no network access.

## 3. Generic positive-stuttering transport theorem

For Lean:

```sh
lean PositiveStuttering.lean
```

The file prints the axiom dependency of its main theorem. The expected result
is an empty list of axioms. For another local module to import it, first create
an object file in the usual way:

```sh
lean -o PositiveStuttering.olean PositiveStuttering.lean
```

For Coq, the driver compiles the source, invokes `coqchk`, captures both exit
codes, and records the compiler version and source hash:

```sh
python3 check_transport_coq.py \
  --coqc "$(command -v coqc)" \
  --coqchk "$(command -v coqchk)"
```

Inspect `positive_stuttering_coq_receipt.json` and the corresponding kernel and
`coqchk` logs. Both recorded return codes must be zero. `Print Assumptions`
reports that the theorem is closed under the global context. An empty
`coqchk` log is compatible with successful quiet checking; the captured exit
code supplies the success evidence.

The theorem requires an invariant on the source configurations, preservation
of that invariant by a source step, preservation of terminal configurations,
and a **strictly positive finite target block** for every source step. The
state map may be noninjective. There is no requirement to supply a reverse
simulation or a uniform numerical bound on block length. The positivity
hypothesis must not be dropped when instantiating the theorem.

## 4. Lean shared-tree data pilot

Regenerate the source replacement and its standalone audit, then invoke Lean:

```sh
python3 share_trees.py \
  --out reproduced_lean \
  --lean "$(command -v lean)"
cmp pilot/KSource215Data.lean reproduced_lean/KSource215Data.lean
cmp pilot/SharedTreesAudit.lean reproduced_lean/SharedTreesAudit.lean
```

Read `reproduced_lean/sharing_receipt.json` and the generated kernel log. The
input is the pinned `reference/KSource215Data.lean`. The transformation shares
repeated constructor subtrees across `t215` and `tD`; it preserves the other
source bytes. It does not replace, reorder, or omit any source certificate
entry.

The result should have these measurements:

| Quantity | Value |
| --- | ---: |
| Original `KSource215Data.lean` | 456,548 bytes |
| Replacement `KSource215Data.lean` | 239,744 bytes |
| Reduction | 216,804 bytes (47.49%) |
| Shared constructor nodes across both roots | 427 |
| Primitive leaves in each original root | 4,751 |
| Forward certificate entries changed | 0 |

The two independent literal roots are retained in the standalone audit. Its
proofs check exact constructor-tree equality, rather than a heuristic such as
leaf-word equality. This is sufficient for the pilot's claim about generated
data, but the replacement project module still needs a fresh upstream build.

## 5. Rocq positive-binary path pilot

Regenerate the compact certificate module and full equality audit, then compile
and independently check the audit:

```sh
python3 compact_rocq_paths.py \
  --out reproduced_coq \
  --coqc "$(command -v coqc)" \
  --coqchk "$(command -v coqchk)"
cmp rocq_pilot/Cert215Offsets.v reproduced_coq/Cert215Offsets.v
cmp rocq_pilot/Cert215CompactAudit.v reproduced_coq/Cert215CompactAudit.v
```

Read `reproduced_coq/compact_paths_receipt.json` and its kernel and `coqchk`
logs. Both compiler and checker exit codes must be zero. The input
`reference/cert215_encoded.json` preserves all information needed to reproduce
the original literal certificate, including its formatting. The published
`rocq_pilot/upstream_binding.json` separately records the comparison of that
reconstructed original with the file retrieved at the pinned commit.

The representation uses a positive binary numeral with a terminating high bit:

```
code([b0, ..., b(k-1)]) = 2^k + sum_i (bi * 2^i).
```

The lowest bit corresponds to the list head. Thus the encodings of `[]`,
`[false]`, `[true]`, and `[true; false]` are respectively 1, 2, 3, and 5.
A transparent recursive `certPath` decodes the numeral back to `list bool`.
The public certificate type remains unchanged.

| Quantity | Value |
| --- | ---: |
| Original `Cert215Offsets.v` | 1,499,170 bytes |
| Replacement `Cert215Offsets.v` | 229,933 bytes |
| Reduction | 1,269,237 bytes (84.66%) |
| Certificate entries | 2,240 |
| Entries whose mathematical value changes | 0 |

The audit contains both complete lists and proves
`Cert215 = Cert215Literal` by reflexivity. The equality covers path lists,
offsets, successor identifiers, and entry order. No claim rests only on a hash
or on the Python generator's successful execution.

## 6. Bindings to the accepted sources

These SHA-256 digests identify the source bytes accepted for this package:

| File | SHA-256 |
| --- | --- |
| `PositiveStuttering.lean` | `69be9e02cabe240a9946f666e37ff1381edc9da871adec86209aac6c9608d947` |
| `PositiveStuttering.v` | `20747d3856d0a5012e8cfdb560b9de9af2db33c70f38923eeb30d59401fe6453` |
| `reference/KSource215Data.lean` | `43093f181bfdd86408a7c88bbf8c0d99ada494b5e3780ae9d93cff05502dbe67` |
| `pilot/KSource215Data.lean` | `b260068b969f2ba2128a46841c86b0f5e9728a722b3640d1e7bb97185f569fa3` |
| Original Rocq `Cert215Offsets.v`, reconstructed from the reference JSON | `32197f6f31bd3c7c7bf5fb94af0e721434f1238d64a64a715b8c9d2cbdd4e728` |
| `rocq_pilot/Cert215Offsets.v` | `d63797bf3d9e4f5758d07b41ce7a667259bb017c0b453aab4c9eb3e669b55157` |

Do not silently apply a pilot to a later generated file on the assumption that
its formatting and structure stayed the same. Rebind the reference input,
regenerate, and check the exact equality again.

## 7. Recommended adoption order and upstream gates

### First: the generic transport lemmas

Place the two positive-stuttering lemmas in the appropriate common semantics
layers. Instantiate them for the conditional-marker candidate using the exact
transition tables, the local tape invariant, and one-step/three-step blocks.
Keep the concrete finite table certificate separate from the reusable theorem.
The correspondence between the native halt identifier and the identifiers in
the existing formal sparse and dense machine definitions must be explicit
before composing the new equivalence with the existing K215 endpoint theorem.

Run the repository's normal axiom audit on the resulting endpoint. The generic
lemmas introduce no logical axioms; additional assumptions must arise, if at
all, from the existing semantics or the explicit instance and should remain
visible. Do not describe an instance with unproved table or invariant premises
as a completed machine-correctness proof.

### Second: source-data compaction, without changing theorem interfaces

Integrate each transformation into the maintained source generator so a normal
regeneration preserves the new representation. Avoid relying on edits to a
generated file that the next generator invocation would overwrite. Preserve
existing public definition names, certificate types, and theorem statements.

For the Lean replacement, the acceptance gate is a fresh build of
`Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSource215Data.lean`, all sixteen
forward-certificate checking shards, the `KSource215` facade, and every affected
endpoint dependency using the repository's pinned Lean installation. Run the
normal axiom and endpoint checks. The standalone audit alone does not satisfy
this gate. The primitive trees, 2,240-entry source certificate, and machine
transition data must retain their values.

For the Rocq replacement, the acceptance gate is a fresh build of
`Computability/BusyBeaver/Research/ZFC/k225-formal/rocq/rocq-extension/coq/215/Cert215Offsets.v`
and its dependent certificate and correctness modules, including the relevant
sparse and dense K215 endpoints, using **Rocq 9.1.0 and rocq-stdlib 9.0.0**.
Repeat the repository's assumptions reports and recursive independent checker.
The successful Coq 8.18 pilot is preliminary evidence for this gate, not the
same check.

For both lanes, use fresh object files for the changed module and dependent
clients. Record the repository revision, compiler versions, source hashes,
complete command exit statuses, and exact endpoint statements. Only after
these checks should the replacements be advertised as adopted into the checked
K215 proof.

### Third: reduce future certificate obligations

A separate, unimplemented refactor is to prove once that source programs have
the same semantics as a resolved primitive control-flow graph. Each graph row
must include the primitive register operation, every successor, and all halt
and control-only transitions. Equality of these resolved graphs could transport
correctness across reassociation or re-encoding without recreating paired
source-path certificates. Equality of primitive leaf words alone is insufficient.

This proposal is not included among the checked artifacts. It needs a generic
semantics theorem and an exact graph-equality check before replacing any current
proof obligation. It also does not, by itself, eliminate the machine-level
symbolic runs in the current site-checking batches or the exact boot traces.

If performance is a reason for adoption, measure the original and changed
upstream builds with the same toolchain, hardware, cache policy, and resource
limits. Source-size savings are already established; wall time and peak memory
remain to be measured.
