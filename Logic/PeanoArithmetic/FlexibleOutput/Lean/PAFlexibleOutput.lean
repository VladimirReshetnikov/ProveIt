import PAFlexibleOutput.Halting
import PAFlexibleOutput.Functionality
import PAFlexibleOutput.Refutations
import PAFlexibleOutput.Search
import PAFlexibleOutput.Main

/-!
# A divergent program with every possible output in a model of PA

Import surface of the project. The main theorem is `PAFlexibleOutput.flexibleOutput` in
`PAFlexibleOutput.Main`: there is a program `e` that diverges on every input, such that for
every input `x` and every `o : Option ℕ` some model of `𝗣𝗔` computes the value `o` for `e` on
`x`.

* `PAFlexibleOutput.Halting`: the halting formula, the halting sentences, the value of a
  program inside a structure, and the standard semantics.
* `PAFlexibleOutput.Functionality`: the halting formula is functional in every model of `𝗣𝗔⁻`.
* `PAFlexibleOutput.Refutations`: the outputs refuted by `𝗣𝗔` are recursively enumerable.
* `PAFlexibleOutput.Search`: a recursively enumerable relation has a partial recursive selector.
* `PAFlexibleOutput.Main`: the main theorem.
-/
