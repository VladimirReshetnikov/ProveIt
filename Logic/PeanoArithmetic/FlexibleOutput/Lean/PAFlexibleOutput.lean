import PAFlexibleOutput.Halting
import PAFlexibleOutput.Provability
import PAFlexibleOutput.Search
import PAFlexibleOutput.Main
import PAFlexibleOutput.Functionality

/-!
# A divergent program with every possible output in a model of PA

Import surface of the project. The main theorem is `PAFlexibleOutput.flexibleOutput` in
`PAFlexibleOutput.Main`: there is a program `e` that diverges on every input, such that for
every input `x` and every `o : Option ℕ` some model of `𝗣𝗔` computes the value `o` for `e` on
`x`.

The main theorem uses four modules.

* `PAFlexibleOutput.Halting`: the halting formula, the value of a program inside a structure,
  the value formula, and the standard semantics.
* `PAFlexibleOutput.Provability`: the provable numeral instances of a formula are recursively
  enumerable.
* `PAFlexibleOutput.Search`: a recursively enumerable relation has a partial recursive selector.
* `PAFlexibleOutput.Main`: the main theorem.

One module is independent of the main theorem.

* `PAFlexibleOutput.Functionality`: the halting formula is `𝚺₁`, and functional in every model
  of `𝗣𝗔⁻`.
-/
