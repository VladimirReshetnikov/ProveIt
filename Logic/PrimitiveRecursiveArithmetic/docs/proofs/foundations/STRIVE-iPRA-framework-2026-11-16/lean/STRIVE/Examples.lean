import STRIVE.CompiledFormula
import STRIVE.Kernel

/-!
# STRIVE-iPRA example targets

These signatures correspond to the JSON examples in the packet.  They are
kept as explicit formalization milestones rather than semantic Lean theorems.
-/

namespace LeanProofs.IPRA.STRIVE.Examples

open LeanProofs.ConciseIPRA
open LeanProofs.IPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

/-!
Example 1: `∀ q < 4, ∃ z < 4, ∀ e < 3, (z+q) mod 4 = 0`.
The generated positive strategy table selects `z = (4-q) mod 4` and stores
three trivial atomic certificates for each universal `e` response.

Target:

```
theorem modularChallenge :
  ([] : List (Fm PTm 0)) ⊢[PRAAx] modularChallengeFormula := by
  exact (compileModularChallenge.valueCorrect.iffMp ...)
```

Example 2: `∀ q < 3, ∃ z < 2, ∀ e < 2, q < z` is false.  The generated
negative certificate chooses the least counterchallenge `q = 1` and stores a
negative table for both candidates `z=0,1`.

Target:

```
theorem failedChallenge :
  ([] : List (Fm PTm 0)) ⊢[PRAAx] Fm.neg failedChallengeFormula := by
  exact compileFailedChallenge.ofNegativeCheck canonicalNegativeEquation
```
-/

end LeanProofs.IPRA.STRIVE.Examples
