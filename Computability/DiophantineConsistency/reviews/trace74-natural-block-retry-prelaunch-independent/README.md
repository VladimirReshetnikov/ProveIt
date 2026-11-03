# Natural-block import retry: scoped prelaunch review

**GO for one direct-pin author retry** using source SHA-256 `49d908e5b290c76613da30d72523670243c66731b474c03634bab30d6b0013f7` and runner SHA-256 `a8937166f3831e6c9a1c8de6201823655589f361fac5fa0f5d1f2869255ca373`. No Lean was run in this review.

Retained attempt01 terminal SHA-256 `a24a0cb1a8a8e807ffd2ec8d19aba33d87856a49a076c3108d9c4256508de804` records Lean exit 1, FAIL, with no timeout. Its log begins with missing `LO`/model namespaces and further errors; author reports actual tool session 5878 exited 1 and was reaped. No theorem is accepted from this run. Source diff against retained snapshot adds only `DiophantineConsistency.ArithmeticSaturation` import; theorem assumptions/body are unchanged. Runner diff updates source hash and pins the corresponding direct object SHA-256 `7270ac9e040b9be18433f25b2956f6f9c53d17d3832b40e1a43ac36467fc017e`.

Independently reran the 11 actual report-parser controls and actual read-only pin/resource preflight, both PASS. Original source review's natural truncated-subtraction analysis and prior direct-pin runner limits remain. Actual tool exit and accepted theorem/report need post-audit. The theorem remains conditional on explicit natural rank representative, q and digit bounds; no graph-zero implication, guard or iPRA endpoint is claimed.
