import FermatIPRA.Program

/-!
Executable examples, to be run after installing the pinned Lean toolchain.
These commands were not executed in the preparation environment.
-/

namespace FermatIPRA

#eval witness 2
#eval witness 5
#eval witness 13
#eval witness 17
#eval witness 29
#eval witness 37
#eval witness 41
#eval witness 61

#eval ([2, 5, 13, 17, 29, 37, 41, 61].map fun p =>
  let ab := witness p
  (p, ab, representsB p ab.1 ab.2))

end FermatIPRA
