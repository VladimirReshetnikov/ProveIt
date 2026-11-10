import PAFlexibleOutput.ProofCore
import PAFlexibleOutput.MathlibAssembly
import PAFlexibleOutput.Statement
import PAFlexibleOutput.Arithmetization
import PAFlexibleOutput.Functionality
import PAFlexibleOutput.Refutations
import PAFlexibleOutput.Search
import PAFlexibleOutput.Main

/-!
# A divergent program with every possible output in a model of PA

Import surface of the project. The main theorem is
`PAFlexibleOutput.exists_partrec_flexibleOutput` in `PAFlexibleOutput.Main`: there is a
partial recursive `f : ℕ →. ℕ` such that for every `o : Option ℕ` some model of `𝗣𝗔` computes
the value `o` for `f 0`.

* `PAFlexibleOutput.Statement` defines the halting formula, the halting sentences and the
  named propositions. It proves nothing.
* `PAFlexibleOutput.ProofCore` proves the logical core over an abstract interface (namespace
  `FlexibleOutput`). The final proof does not use it.
* `PAFlexibleOutput.MathlibAssembly` obtains the self-referential program from Mathlib's
  `Nat.Partrec.Code.fixed_point₂`, for an abstract arithmetic bridge and proof search
  (namespace `FlexibleOutputMathlib`).
* `PAFlexibleOutput.Arithmetization`: partial recursiveness, standard semantics and
  `𝚺₁`-completeness for the halting sentences; the divergence sentence.
* `PAFlexibleOutput.Functionality`: the halting formula is functional in every model of `𝗣𝗔⁻`.
* `PAFlexibleOutput.Refutations`: the outputs refuted by `𝗣𝗔` are recursively enumerable.
* `PAFlexibleOutput.Search`: search through a recursively enumerable relation.
* `PAFlexibleOutput.Main`: the bridge for `𝗣𝗔`, the proof search and the main theorem.
-/
