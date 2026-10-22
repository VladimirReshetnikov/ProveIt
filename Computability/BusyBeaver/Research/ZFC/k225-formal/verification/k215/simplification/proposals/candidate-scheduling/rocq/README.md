# Self-contained combined Rocq component check

This bundle contains the twelve exact source inputs for the combined scheduler
and shared-implication component check, plus its typed compatibility client.
The original source bytes are preserved before any namespace compatibility
translation. `source_provenance.json` records their hashes, origin, order,
and the pinned ProveIt main-branch commit:

`57541fe0cfe3af62b4cb58747d8d1d7c16b338d5`.

## Run

Python 3.9 or later and a complete Coq/Rocq installation are required. No ProveIt
checkout, network access, or precompiled project objects are needed:

```sh
python3 check.py --coqc /path/to/coqc --coqchk /path/to/coqchk \
  --out /tmp/fresh-combined-rocq
```

The output directory must not exist. `--coqc` and `--coqchk` default to the
executables on `PATH`. The script verifies every input hash, makes fresh build
copies, compiles all thirteen source files, checks the expected nine closed
assumption reports, and invokes recursive `coqchk`. It writes a receipt and
individual logs under the output directory. `COQPATH` is cleared; explicit
local namespaces point only to the fresh project files. The installed standard
library and its plugins remain toolchain dependencies.

The accepted checks used Coq 8.18.0, compiled with OCaml 4.14.1. For an 8.x
compiler, the driver explicitly substitutes `From Coq ` for `From Stdlib ` in
disposable copies only; both original and compiled hashes and substitution
counts are recorded. It makes no other source transformation. A compiler
outside the 8.x family receives the original source bytes.

The production K215 lane specifies Rocq 9.1.0 with stdlib 9.0.0. This bundle
does not claim a fresh check under that unavailable toolchain. Compiler and
kernel-checker executable hashes are recorded by the portable driver.

## Contents and evidence

* `src/`: twelve original proof-module sources and `Client.v`.
* `source_provenance.json`: original input hashes and provenance.
* `check.py`: portable offline build and kernel-check driver.
* `evidence/receipt.json` and `evidence/logs/`: the accepted repository-based
  combined component check, copied without editing.
* `portable_evidence/`: the independent fresh run of this portable driver.
* `LICENSE.ProveIt`, `THIRD_PARTY.upstream.md`, `NOTICE.md`, and `LICENSES/`:
  retained notices and all four license files linked by the historical
  upstream scope notice.

Historical absolute paths in the accepted evidence document the original
check. The portable driver does not use them. It reads only bundled sources,
its manifest, and the explicitly selected installed toolchain.

## What was checked

The generic scheduler and representation-independent implication core are
instantiated with the actual numeric code providers. The unchanged production
soundness proof and updated completeness proof yield the existing
`seedPerm_iff_thm` contract. The compatibility client checks the types of all
three `DomImp` record fields, the unrestricted rho8 theorem, and the existing
seed completeness, soundness, and equivalence theorems. Nine assumption
reports are closed under the global context. Recursive kernel checking
includes their dependency closure.

The self-contained numeric providers are exact hash-recorded production
sources preserved in the earlier checked-transport packet. They are not the
simplified providers used by the older shared-core experiment.

The full physical Turing-machine endpoint and complete ZFC equivalence chain
are outside this focused build. The associated source patches and producer
replay evidence are supplied in the separate Rocq component directories.
No transition table is altered by this bundle.
