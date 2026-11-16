# Repository close-out check

- Formalization target pinned in this package:
  `9df5cbdf39e6220be823f611987bd584d37711fd`.
- Repository `main` at close-out:
  `976e82c3b27401ac97038100d257680973e72dc6`.
- Close-out head timestamp: 2026-11-16 05:38:44 UTC.
- The inspected head commit modifies only Busy Beaver/PA files, not the iPRA
  subtree used by this package.
- Blob hashes checked unchanged between the pin and close-out head:
  - `Logic/PrimitiveRecursiveArithmetic/README.md`:
    `d53135eba9ca576ac79d0f9bb76840b075a011dd`;
  - `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/PR.lean`:
    `3251631592070d9ed3687cc0bf7dbd5eb452e46f`;
  - `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/NativeBiInterpretation.lean`:
    `ccfe499b9687ea0e176f832686d8e492fe15544b`.

The earlier commit remains the reproducible target because the report, Lean
variable layouts, and source audit were prepared against it.
