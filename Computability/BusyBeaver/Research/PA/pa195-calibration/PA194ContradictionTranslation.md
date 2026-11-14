# Translation of the distinguished source contradiction

In the PA194 named numerical source encoding, code `1` is the membership atom
with both variable labels zero. `PA194ContradictionTranslation.lean` defines
its standard arithmetic translation `contradiction` as `bitTranslation 0 0`.
This is a formula with free label zero; it does not say that the constant
arithmetic values zero and zero are the two membership arguments.

`positive_code_one` proves that the positive component of the fixed
candidate-PRA source translator at input `1` is exactly the Foundation quote of
this formula in every nonempty candidate-PRA model with an IΣ₁ arithmetic
reduct and equality interpreted as equality. The theorem uses the previously
fixed certified source decoders, so it has no decoder-certificate premises.

Independently, `ISigma1_proves_not_contradiction` constructs an object-theory
proof that IΣ₁ proves the universal closure of the formula's negation;
`PA_proves_not_contradiction` transfers that fixed-formula theorem to PA.
The proof uses the internal fact that bit membership implies strict numerical
inequality. Lean reports only `propext`, `Classical.choice`, and `Quot.sound`
for the three results, with no `sorryAx`.

This is an identification and object-theory refutation of one fixed standard
translated formula. It does not translate arbitrary or nonstandard source
derivations into arithmetic proof codes, prove soundness of the entire
source calculus, connect a nonstandard PA194 computation to such a derivation,
or establish either machine/consistency implication.

Run `check-contradiction-translation.sh` with the audited `IPRA_LEAN_OVERLAY`
and `IPRA_FOUNDATION_OVERLAY` set. It rebuilds the source translator and the
standard-template quotation dependencies before checking this module.

An independent fresh Linux replay passed with the audited overlays, rebuilding
the local dependency chain. The all-model identification and the IΣ₁ and PA
object-theory proof theorems reported no `sorryAx` dependencies.
