# Actual decimal215 arithmetic import collision

The first new `ArithmeticMachineGraph215` replay stopped at its imports,
before theorem elaboration, with exit code 1:

```
import Mathlib.LinearAlgebra.Matrix.Defs failed,
environment already contains 'Matrix.map' from Foundation.Vorspiel.Matrix
```

The exact decimal machine dependency graph contains seven custom modules:
`DecimalMachine215`, `KDense215`, `KDenseBridge`, `KTable215`, `KTableCore`,
`KZip`, and `Core`. Only `DecimalMachine215` imports all of `Mathlib.Tactic`.
The other custom modules have no external import beyond `Init`. Its separate
`Mathlib.Data.Fin.Basic` import is already narrow.

A source-traced path from the broad import is:

```
Mathlib.Tactic
Mathlib.Tactic.NormNum.Irrational
Mathlib.Analysis.SpecialFunctions.Pow.Real
Mathlib.Analysis.SpecialFunctions.Pow.Complex
Mathlib.Analysis.SpecialFunctions.Complex.Log
Mathlib.Analysis.SpecialFunctions.Log.Basic
Mathlib.Analysis.SpecialFunctions.Exp
Mathlib.Analysis.Complex.Asymptotics
Mathlib.Analysis.Complex.Basic
Mathlib.LinearAlgebra.Complex.Module
Mathlib.LinearAlgebra.Matrix.ToLin
Mathlib.LinearAlgebra.Matrix.Notation
Mathlib.LinearAlgebra.Matrix.Defs
```

`Foundation.Vorspiel.Matrix` defines a vector `Matrix.map`; the mathlib matrix
module declares the same name. Neither vendor is edited. The proposed minimal
repair is to replace only `import Mathlib.Tactic` in the actual decoder with
`import Mathlib.Algebra.BigOperators.Group.Finset.Basic`. All machine data,
definitions and proof bodies remain unchanged. A scratch file importing the
actual Foundation PRF stack plus the two narrow mathlib imports compiled with
`-M6000 -j1 -DElab.async=false`. It checked Nat finite sum/product recurrences,
finite kernel decisions, `Equiv`, and `Int.toNat`. This is import feasibility,
not a replay of the complete decimal decoder.

At creation of this receipt the accepted decoder has not been edited, and the
new graph has not passed. A fresh complete decoder and focused check replay is
required after the root reviews the proposed import-only change.

Pinned evidence:

- `/tmp/arithmetic215-actual-private/ArithmeticMachineGraph215-stage1.log`: `0b01a11699cc01ca7269fedd2ae3103a048f21afad9ca45167981b123d2dd9b8`.
- `/tmp/arithmetic215-actual-private/ArithmeticMachineGraph215-stage1.json`: `d7e057c6a78693215ce1ad81aef5ba8e95efb1dba3ceeb36eb8f4b0180683d66`.
- `/tmp/arithmetic215-actual-private/NarrowImports.lean`: `31a1f72dbdef2e48d6a5bbab218b151cec1891f9df80268f3ecedbff38cc1e19`.
- `/tmp/arithmetic215-actual-private/NarrowImports.log`: `42659d0278f1904edc46c75ffd308ce1a672ac0c5a48870c02731d0cf3dda517`.
