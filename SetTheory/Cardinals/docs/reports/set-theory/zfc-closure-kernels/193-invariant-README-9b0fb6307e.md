# Rocq components: terminal epilogues and state relabeling

Baseline reviewed: ProveIt `57541fe0cfe3af62b4cb58747d8d1d7c16b338d5`.

## TerminalDrain.v

This standalone theorem weakens the terminal condition in the repository's
`proposals/k215-transport/formal/PositiveStutter.v` without weakening positive
progress. The source is an optional successor function `stepA`; the target is
an optional successor function `stepB`; `R` relates complete configurations.

The two hypotheses are:

* `advance`: one source step produces a **positive** finite target run whose
  endpoint is related to the source successor;
* `finish`: a source terminal configuration related to a target configuration
  implies that this target configuration **eventually halts**.

The result is finite-halting equivalence. The backward implication uses only
`advance`; no immediate-stop equivalence is needed. Determinism comes from the
optional successor functions. A successful positive prefix of a terminating
run leaves a strictly shorter terminating suffix. This gives the induction
measure for reflection without a fairness assumption.

The file contains checked examples showing both boundaries: a source halt can
correspond to a target that needs two more steps, while allowing zero target
steps would relate an infinite source self-loop to an already halted target.

This is an adaptation of a prior proposal, not a new invention of stuttering
simulation. The repository also contains a terminal-drain proposal. Its useful
role here is to provide a small checked Rocq counterpart to the accompanying
Lean theorem. It is not wired into the maintained Rocq K215 proof.

The available compiler is Coq 8.18.0 / OCaml 4.14.1, not production Rocq 9.1.0.
Standalone compilation printed three closed assumption reports; recursive
`coqchk -o` reported no axioms or unsafe declarations. The full 237-module
K215/ZFC endpoint has not been rebuilt with this file.

## StateRelabel.v and the concrete Dense215 adapter

The functor takes two binary BusyCoq contexts, their existing semantic
modules, and a map on states. Passing the semantic modules preserves the
identities of their inductive step and halting relations. Its sole
machine-specific hypothesis is the total transition identity

```
target (decode q, b) =
  option_map (fun (w, d, q') => (w, d, decode q')) (source (q, b)).
```

This identity includes terminal states. The resulting theorem holds on every
input tape and relates a configuration to the configuration with the same tape
and the mapped control state. The state map needs no inverse, injectivity or
surjectivity. The reverse halting proof follows a source execution forward and
uses the existing `BusyCoq.progress_halts` principle on the target.

`relabel/K215F/Dense215.v` keeps the maintained literal tables, state map and
all finite transition checks, then obtains the public
`dense_sparse_halts_iff` theorem from the functor. The exact old-to-new patch is
provided separately. Current K215 files do not name the removed helper lemmas;
the public dense/sparse equivalence has the same statement.

The final component build compiled this concrete adapter with a closed
assumption report, and recursive `coqchk -silent -o K215F.Dense215` succeeded.
The complete imported-library context lists the existing BusyCoq `inj_pair2`,
standard-library proof irrelevance and `eq_rect_eq` axioms. The public
`dense_sparse_halts_iff` theorem depends on none of them, as its closed
assumption report shows. No type-in-type, unsafe fixpoint or assumed-positivity
declaration appears in the kernel-check context. This remains a Coq 8.18
component result, not a production Rocq 9.1 ZFC endpoint build.

The practical metric is important. Eight generated Dense modules contain the
same 74-line/2,883-byte transport block. They are already generated from a
common template, so there were not eight independent handwritten proofs.
Extracting a reusable semantic theorem reduces generated duplication and
per-variant proof work; it can increase the total source of a single endpoint
until more clients share the new module. This is therefore a component
demonstration, not a measured overall K215 proof-size or build-time saving.

Adoption must update the generator/template and module manifest, then rebuild
the production Rocq 9.1 closure and rerun the final assumption checks. A direct
edit to generated `Dense215.v` alone would be overwritten by regeneration.

## Reproduction

With `coqc` and matching `coqchk` available, run the supplied verification
script with an output directory outside the source package. Standard compiler
environment variables may be supplied in the shell. It records exact source
hashes and commands. It never changes the maintained repository.

```sh
python3 build_components.py --out /tmp/k215-rocq-components \
  --coqc coqc --coqchk coqchk
```

The output directory must not already exist. The script compiles both
components, checks the expected closed assumption reports, and runs
`coqchk -silent -o` recursively on both endpoints. Source hashes, compiler
and checker hashes, commands, outputs and return codes are retained in that
directory. The `seconds` fields record this component run only and are not
a benchmark against the maintained proof.

The `validation/` directory contains the successful final run's original
receipt and raw outputs. Both recursive checks ran without `-admit` or
`-norec`. The exact sources in this package match that receipt. The initial
module-alias experiment is not the supplied source: its explicit-module
replacement is explained in `ADOPTION.md`.

The BusyCoq sources in `relabel/BusyCoq/` are copied from the repository's
already vendored `checked-transport/adapter/BusyCoq/` dependency. Their license
and tactic-library license are included unchanged. The three literal K215
source files are copied byte-for-byte from the reviewed baseline. The new
proof components are derivative extractions/adaptations, with upstream
attribution preserved in the surrounding report.

`ADOPTION.md` also identifies the existing shorter implication proposals and
the producer and manifest work needed to adopt them. The separate
`prior-cd-adoption.patch` is an exact copy of those **existing** replacements;
it is outside this packet's fresh component build and is labeled accordingly.
