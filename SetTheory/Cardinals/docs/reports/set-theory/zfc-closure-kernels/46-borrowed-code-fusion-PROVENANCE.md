# Fusion experiment provenance and license scope

## Inspected revisions

- ProveIt: [`61e77836565f63582561f54745f633d50efd9c7d`](https://github.com/VladimirReshetnikov/ProveIt/tree/61e77836565f63582561f54745f633d50efd9c7d),
  inspected on 2026-10-17.
- Jeff's busy-beaver source: [`297ab8df7e5de329605c3875b4934643b371a5e3`](https://github.com/jeff87654/busy-beaver/tree/297ab8df7e5de329605c3875b4934643b371a5e3),
  vendored by that ProveIt revision under `lib/jeff-busy-beaver-zfc254`.
- This experiment was produced on 2026-10-17. New files are `search.py`,
  `verify.py`, this documentation, and the generated data/table files.

## Unchanged vendored helpers

These files are included so the quick check works offline. The integrity
manifest `data/fusion/sha256.json` records each copy's exact bytes.

| Bundle path under `code/fusion/vendor/` | Upstream path and pin |
|---|---|
| `source08_rm_verifier.py` | ProveIt pin above: `SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/08-schema-machine-verify_rm_certificate.py` |
| `TMBuilder.py` | Jeff pin above: `ZF/generator/TMBuilder.py` |
| `tm.py` | Jeff pin above: `ZF/generator/tm.py` |
| `tmdb.py` | Jeff pin above: `ZF/generator/tmdb.py` |
| `LICENSE.cardinals` | ProveIt pin above: `SetTheory/Cardinals/LICENSE` |
| `LICENSE.proveit` | ProveIt pin above: `LICENSE` |
| `LICENSE.wade` | Jeff pin above: `ZF/generator/LICENSE.wade` |

The independent source-08 helper is copied without changes, but the wrapper
uses only its `Machine` path interpreter. Its original command-line `verify`
entry point hardcodes the earlier 219-node source hashes and is not suitable
for the new 284-node fused reference. The wrapper therefore supplies the
generalized all-record certificate check itself.

## Adapted functions and data derivation

`verify.py`'s register-certificate traversal follows
`Computability/BusyBeaver/Research/ZFC/layout_grammar_experiment.py`, function
`independent_check`, at the ProveIt pin. It adds explicit checks, strict JSON
key parsing, input hashes, and malformed-input rejection checks.

Its compiler adapter and read-sensitive decision-edge inversion are adapted
from ProveIt's
`SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/08-schema-machine-rebracket_axioms.py`,
functions `compile_dag` and `reextract`; the former also attributes
`recover_wade_dag.py`. Its normalization follows
`Computability/BusyBeaver/Research/ZFC/full_grammar_experiment.py`, function
`normalize`. The delivered numeric table is parsed by separate code without
using Wade's table parser.

`search.py` reuses the pinned ProveIt modules `theory_backend_experiment`,
`recover_wade_dag`, `full_grammar_experiment`, and
`layout_grammar_experiment`. It introduces the logical row fusion, enumerates
the stated recipe grid, and charges the entire generated framework. Its
source logical formulas come from Jeff's `ZF/m254/tools/logic/spec.py`; its
original 219-node decoder comes from `ZF/m254/coq/prog/Dag254.v`.
The nonlogical bundle and complete baseline layout come from the source-19
ProveIt experiment. None of these inherited elements is claimed as a new
result of this artifact.

## Licensing

The ProveIt root license and the more local Cardinals license are both
**MIT No Attribution**, copyright 2026 their respective contributors. Copies
are included. The Wade generator has its explicit **MIT No Attribution**
notice, copyright 2025 Andrew James Wade, also included. Attribution is
retained despite the licenses' lack of an attribution requirement.

The bundled helper copies and adaptations have the license provenance above.
No directory-wide license for all of Jeff's `ZF` program data was present in
the inspected vendored snapshot. `LICENSE.wade` should not be represented as
a blanket license covering every upstream file. The generated DAGs and table
derive from that attributed program; this bundle does not assert additional
permissions over the upstream program data. The relevant source pins and
derivation are preserved so the repository maintainers can assess that scope.

No part of this packaging establishes a new formal correctness theorem or
changes the stated licensing of an upstream work.
