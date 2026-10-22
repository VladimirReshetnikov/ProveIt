# Rocq adoption map

Reviewed baseline: ProveIt `57541fe0cfe3af62b4cb58747d8d1d7c16b338d5`.
All paths below are relative to the repository root. This map separates the
newly checked components from pre-existing proposals.

## 1. Adopt the existing shorter implication derivations first

The exact existing candidates are:

| Maintained source | Existing replacement |
|---|---|
| `Computability/BusyBeaver/Research/ZFC/k225-formal/rocq/rocq-extension/coq/215/CD222.v` | `Computability/BusyBeaver/Research/ZFC/k225-formal/rho8cd/rocq-proposal/CD222.v` |
| `Computability/BusyBeaver/Research/ZFC/k225-formal/rocq/rocq-extension/coq/215/DomRho8.v` | `Computability/BusyBeaver/Research/ZFC/k225-formal/rho8cd/rocq-proposal/DomRho8.v` |

`prior-cd-adoption.patch` is the exact two-source replacement at that baseline.
It contains no newly invented derivation and has **not been freshly compiled
as part of this packet**. The repository's existing
`k225-formal/rho8cd/rocq-proposal/README.md` records Rocq 9.1 component checks
of these files and their immediate clients, and explicitly excludes a fresh
whole-closure compile and recursive endpoint check. Those historical checks
must not be relabeled as new validation.

The replacements preserve the caller interfaces `thm_K`, `thm_P`, `thm_B`,
`thm_S`, `DomImp`, and `rho8_all`. The selected files shrink from 45,538 to
23,197 bytes, a 49.1% source-byte reduction. This is not a whole-project metric.

### Producer changes required in the same adoption

The production generator is
`Computability/BusyBeaver/Research/ZFC/k225-formal/rocq/rocq-extension/regenerate215.py`.
Its `calculus_files` currently copies `CD222` from `coq/217` and generates
`DomRho8` with `generate_domrho8_rocq_compact.py`. Editing only the generated
files would therefore be undone.

In `calculus_files`, give `CD222` and `DomRho8` separate producer branches.
Use the existing `KF` path variable and the existing generator:

```python
producer = KF / "rho8cd" / "generate_domrho8_cd.py"
# CD222 branch:
subprocess.run([
    sys.executable, str(producer),
    "--derivation", str(KF / "rho8cd" / "derivation_luk.txt"),
    "--rocq-cd", str(output / "CD222.v"),
], check=True)
# DomRho8 branch:
subprocess.run([
    sys.executable, str(producer),
    "--derivation", str(KF / "rho8cd" / "derivation.txt"),
    "--rocq", str(output / "DomRho8.v"),
], check=True)
```

These commands describe the required producer wiring; this packet does not
present that wiring as a checked production patch. Retain the namespace
rewriting for the other copied files. Regenerate into a private directory and
compare all outputs before updating production sources. Update the generator's
description, the input/provenance accounting, `coq/regeneration215.json`, and
the `files` hashes in `rocq/rocq-extension/manifest.json`.

For these two replacements, no new logical module is introduced and the
existing `variants["215"]["compile_order"]` entries need no reordering:
`Thm222` precedes `CD222`; `DomRho8` precedes `ThmDom`. Rebuild the affected
callers (including `Prop222`, `G222`, `Interp222`, `Complete222`, `ThmDom`,
and the endpoint's downstream closure) and regenerate the dependency plan.

The production gate is
`Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/rocq/build.py`
with its documented pinned references, Rocq 9.1.0 / rocq-stdlib 9.0.0 switch,
private output directory, and `--kernel`. Preserve the sparse and dense
endpoint statements and their two closed assumption reports each. The final
recursive check must target `K215F.CorrectDense215` without `-admit` or `-norec`.

## 2. Shared dense relabeling is an optional family-level extraction

`Dense215.patch` supplies the concrete generated-file experiment;
`relabel/K215F/StateRelabel.v` supplies its new generic dependency. The proof
preserves `dense_sparse_halts_iff` and the literal table and state map. Existing
K215 callers do not reference the removed private helper lemmas.

The functor accepts the existing Dense and Sparse semantic modules. This avoids
creating fresh inductive step relations. Its instance is included in an explicit
`Module Relabel ... End Relabel` block: a direct module alias compiled but hit
a Coq 8.18 `coqchk` module-signature anomaly during development. The explicit
block is the version supplied for final validation.

The generic theorem holds for every tape and configuration; it needs the total
transition identity, including terminal states, and requires no inverse,
injectivity, or surjectivity of the state map. The concrete `decode_initial`
fact specializes the theorem to blank input.

To adopt it, update
`rocq/rocq-extension/templates/Dense229.v` and the relevant generators,
including `regenerate215.py`; arrange to emit/copy the shared module; add
`StateRelabel` before `Dense215` in the variant's manifest compile order; and
update all source/regeneration hashes. Repeat for other supported variants
only when they actually consume the module. Rerun the production endpoint
gate rather than transferring this packet's component result to it.

This extraction is useful when several variants share it. The old Dense215
source is 155 lines / 6,725 bytes; the concrete adapter is 92 lines / 4,226
bytes plus a 111-line / 3,966-byte shared module. Thus it does not reduce the
combined source of a single selected endpoint. Eight existing variants already
derive the repeated 74-line block from one generator template.

## 3. Keep TerminalDrain as a checked interface reference

`TerminalDrain.v` is a standalone positive-progress simulation theorem that
allows a target terminal epilogue. It is an adaptation of the repository's
existing simulation proposals. It is useful for comparing the Lean and Rocq
interfaces, but it has no production generator or compile-order change in this
packet. Rocq's current `Sim230Main.v` already uses `BusyCoq.progress_halts`
and has a short simulation proof; replacing it merely for language symmetry
would not establish a simplification.

## Validation boundary

`build_components.py` checks only the standalone TerminalDrain theorem and
the literal Dense215 relabeling component. Its receipts use Coq 8.18.0 and
must not be mistaken for the maintained Rocq 9.1.0 ZFC endpoint gate.
`prior-cd-adoption.patch` is outside that component script's build scope.
The validation receipt and raw logs identify the final checked sources.
