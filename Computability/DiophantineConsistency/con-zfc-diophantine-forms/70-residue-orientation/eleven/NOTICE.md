# Attribution and dependency boundary

This contribution was prepared against Vladimir Reshetnikov's ProveIt
repository at commit `9cca523d9f27ad39d52993f4065cbd7e58f8bdd4`.
Byte-identical retained data, proof texts and license files are enumerated
with SHA256 and Git blob identities in `SOURCE_PINS.json`.

The coherent fixed coefficient tuple and native source proof are retained
from package 44 (`44-b4-sparse/native`). The normalized positive auxiliary
reconstruction and first congruence carrier come from package 61
(`61-congruence-carriers`). The adaptive main Pell modulus comes from
package 65 (`65-shared-taps`). The preceding positive component proves the
weighted combination used here. Its construction helper and sparse-ring
checker informed the small standard-library helpers in this component.

Package 52 (`52-sparse-pell/positive`) already develops a conjugate norm,
conditional radical separation, positive Pell majorants, quotient
absorption, and a unit-product finalizer. Its complete
`Y_ABSORPTION_PROOF.md` is retained for precise comparison. These generic
techniques are not claimed as new. The degree 325 construction instead
uses the normalized auxiliary square to obtain a direct octic sum norm,
keeps the adaptive main equation separate, strengthens the strong
ordinate by q(q-1) for elementary denominator recovery, and transfers
the two signed roots into the first positive transport coordinate.

The source still uses the inherited native compiler and K215 refutation
calibration. This is not a replacement machine-independent calibration
or an end-to-end proof-assistant certificate. The finite scripts check
the explicitly described algebra and data, not the unbounded semantic
theorems. Original licenses and notices for the retained data are in
`licenses/`; new files follow the accompanying `LICENSE`.
