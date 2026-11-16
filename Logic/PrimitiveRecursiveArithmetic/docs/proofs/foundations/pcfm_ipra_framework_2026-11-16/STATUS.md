# Verification status

## Completed in this artifact

- Repository audit pinned to ProveIt commit
  `7fa3ba48e8f62e8018ed954faaa48b908217eaf1`.
- Fully developed LaTeX report.
- Compiled PDF.
- Exact-integer/rational Python reference models.
- Automated Python regression tests.
- Lean-oriented source skeletons and proposed theorem signatures.
- Source and limitation ledger.

## Not claimed

- The `lean/` files were not compiled in this runtime because Lean is not
  installed.
- The framework is not yet committed to the ProveIt checked
  `IPRADerivations` library.
- No general Faltings, Siegel, analytic-continuation, compactness, or modulus
  theorem is claimed.
- Python tests are executable evidence, not object-iPRA proofs.
- A Foundation-to-Concise open bridge theorem is reduced to concrete lemmas but
  not claimed implemented here.

## Status vocabulary used in the paper

- **upstream checked**: already present in the pinned ProveIt repository.
- **paper proof**: fully argued mathematically in the report.
- **planned Lean**: exact definition/signature and dependency path supplied,
  but not compiled.
- **executable evidence**: Python exact-arithmetic test or demonstration.
- **residual producer**: a bound, modulus, gap, cover, or similar mathematical
  input that remains an explicit object-theory hypothesis.
