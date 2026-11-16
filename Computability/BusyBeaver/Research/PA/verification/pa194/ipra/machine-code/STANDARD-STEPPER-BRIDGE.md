# Standard-input and literal blank-run model bridges

`PA194StandardCodeBridge.modelStandardCode` proves, for each finite PRA
function code and each external natural-number input tuple, that evaluating
the code on the corresponding numerals in any candidate PRA model gives the
numeral of its standard-natural-number value. The proof uses external mutual
structural induction over codes and external induction over each fixed natural
recursion input. It covers arbitrary codes, including the PA194 physical
stepper, and is not a uniform internal statement for nonstandard code or input
values.

`PA194StandardStepperBridge.literalBlankRun_allModels` combines this result
with the checked standard zipper/stepper correspondence. Given a kernel-checked
literal PA194 blank-run certificate of any fixed standard length, it obtains
an exact packed-stepper equation in every candidate PRA model, with the
endpoint represented by the numeral of the packed configuration.
`PA194PackedNumeralBridge.literalBlankRun_explicitEndpoint` further
separates the result into model control, left-tape, and right-tape numerals,
which can be composed with physical controller theorems. In particular, an
independently checked 58,154-step dense startup certificate can be substituted
without expanding the potentially enormous tape numeral.

The bridge itself assumes the literal run certificate. It does not establish
that run, prove an arbitrary model-length source simulation, derive a uniform
internal PA/PRA/iPRA formula, or prove either PA consistency reduction.

The bridge theorems were rebuilt in a suffix check against retained, separately
checked prerequisites, and their printed axioms exclude `sorryAx`.
An earlier version of `check-standard-stepper-bridge.sh` completed a nested
replay of the first two modules against the `IPRA_LEAN_OVERLAY` and
`IPRA_FOUNDATION_OVERLAY` prerequisites described in this directory's README.
The updated wrapper includes the packed-numeral module; its full nested replay
has not yet been completed.
