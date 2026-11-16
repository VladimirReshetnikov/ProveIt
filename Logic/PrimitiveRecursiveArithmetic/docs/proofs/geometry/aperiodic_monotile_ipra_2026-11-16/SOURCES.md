# Sources and provenance

## Mathematical source

David Smith, Joseph Samuel Myers, Craig S. Kaplan, and Chaim Goodman-Strauss,
**An aperiodic monotile**, *Combinatorial Theory* 4(1), 2024, article 6.

- arXiv: `2303.10798` (version 3 inspected)
- Theorem 1.1: the hat is an aperiodic monotile.
- Section 2: metatile/supertile construction and existence.
- Section 3: chevron/comet coupling proof.
- Appendix A: alignment.

## Exact geometry and substitution constants

Repository: `isohedral/hatviz`

- `geometry.js`, Git blob SHA `46e19f05545ed0152776c5fbeec74547932273f1`
  - 13 axial hat vertices and affine helper formulas.
- `hat.js`, Git blob SHA `d8c1839bd4861c6f871eba83d6a42d010f1d9551`
  - initial metatiles, 29-placement scaffold, and four child selections.

The archive does not copy the complete upstream programs.  It transcribes only the finite
mathematical constants needed by the certificate and gives independent Python code.

## iPRA infrastructure

Repository: `VladimirReshetnikov/ProveIt`, branch `main`, inspected 2026-11-16.
Relevant paths:

- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/`
- `Logic/PrimitiveRecursiveArithmetic/Derivations/`
- `Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/IPRADerivations/Core/`

The report specifically targets `Core/Pairing`, `Core/Search`, `Core/Pigeonhole`,
`Core/Parity`, `Core/DescentEx`, `Core/Integers`, `Core/LinearAlgebra`, and the transfer
theorem `pra_iff_native`.

## Related Lean staging work

`jsm28/AperiodicMonotilesLean` was inspected for its decomposition of tiling, hierarchy,
extension, and geometric bridge tasks.  No code was copied.
