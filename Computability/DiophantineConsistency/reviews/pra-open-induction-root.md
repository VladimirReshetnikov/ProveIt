# Candidate PRA open induction and left addition zero

`PRAOpenInduction.modelOpenInduction` extracts parametric open-formula
induction with primitive successor from the candidate theory's actual
induction schema, in every equality model. `PRAAdditionZeroLeft` applies it
to derive `0+x=x` in every such model and uses completeness to obtain the
closed object-theory derivation `PRA ⊢ zeroLeftSentence`. These results do
not establish that the candidate presentation is equivalent to standard PRA,
or derive commutativity or the Q order clause.

An independent fresh replay at `/tmp/pra-open-zero-root-rc42fm5l` passed all
four files without warnings. Their object hashes agree with the author
provider; axiom reports contain only `propext`, `Classical.choice`, and
`Quot.sound`. The direct `PRAAddOne`, `PRAAddition`, and `PRAExhaustion`
provider objects were rebuilt from the current merged sources, and the driver
checks the source and object hashes. Foundation, Mathlib, PRATheory, and
other inherited prerequisite caches are not a fresh transitive source audit.
The [evidence](pra-open-induction-root-replay/) includes the current-source
refresh, root run, and author exploratory attempts, including the first
zero-left attempt that failed because its overlay omitted OpenInduction.
The refresh state also names an unfinished commutativity probe, which is not
accepted by this checkpoint.
