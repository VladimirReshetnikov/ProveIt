# First-root quotient model equivalence

The 41-variable Lean literal is checked row by row against the pinned
170-operation candidate. In every IΣ₁ model and for arbitrary integer ports,
`AdaptiveQF41Model.shifted_no_zero_iff` proves both directions of the positive
zero-set equivalence with the 42-variable parent. It decomposes both sums of
squares, transports the 31 common residuals, and handles the two remaining
parent residuals separately.

The parent norm and positive scale supply an integral quotient by the checked
`scaled_quotient` theorem; positivity of the old root makes the quotient
positive. In the other direction the map reconstructs the old root as
`scale*t` and the removed square coordinate as `scale²`. The argument makes
no assumption about the signs of integer ports. The [model replay](../../reviews/adaptive-qf41-model-replay/README.md)
uses the accepted 42-native peer and inherits its two-provider and transitive
ancestry; it does not itself prove an iPRA endpoint. The separately replayed fixed-port
`IPRAQF41Native.literal_equivalence` proves the native-theory equivalence with
the negation of Foundation's mapped ZFC refutation predicate.
