# Package 66's fifteen-positive points at the compact44 ports

Package 66's 30 / 78, 26 / 87 and 24 / 88 (package 58's integral-root circuits,
`p15_degree{30,26,24}`) have native, standard and equality-only iPRA endpoints:
`Compact44/IPRAPositive66p78`, `IPRAPositive66p87` and `IPRAPositive66p88`.

- **Tuple.** The JSONs name a `COEFFICIENT_BINDING.json` missing from 66 and 58,
  but both packages' hash lists pin it (`0599543212…`) and its four gzip
  payloads. The tree's retained copies under
  `candidates/free-j-polarized-positive/source/positive/coefficients/` match, and
  their K decodes to the compact44 original-order payload (raw `c6d523bd…`), as
  for the 64 and 65 endpoints.
- **Route.** The forms are reduced to the fifteen-positive Short15 route of the
  121x8801 tuple (`Mixed121/Short15*`): the first carrier forces `Y = s·q³`; for
  the two `J = 3j + 1` forms `q ≡ 2 (mod 3)` makes `q` and `H` coprime, so the
  second carrier forces `X = w·q`. Then every residual is a Short15 residual and
  the port-generic `Short15Facts.facts_core` / `Short15Index.oracle_gap` apply,
  ending in `CompactLeafFactsHalt.halts_of_facts`. The converse reads
  `CompactHaltFirstGamma.halt_first_gamma` (`C44Short15ConvData.canonical`); the
  `J = 3j + 1` forms also need `w < γ` (`gamma_gt`).
- **Binding.** [`tools/generate_short15_c44.py`](tools/generate_short15_c44.py)
  `--check` checks the tuple pins and each literal graph against its pinned JSON
  (and package 58's source circuit). The payload-to-port binding is an external
  byte comparison, as for 64 and 65; the exact degrees are the package's claims.
