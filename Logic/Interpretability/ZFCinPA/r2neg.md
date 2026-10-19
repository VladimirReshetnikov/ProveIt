# Fresh check of internal negation translation

The unchanged upstream [`R2Neg`](Lean/ZFCinPA/R2Neg.lean) proves that encoding
Foundation's negation-normal-form dual gives a validator formula equivalent
to implication into falsity. `encode_neg` covers every internal well-formed
semiformula and arbitrary encoder environments, stacks and streams in IΣ₂
models. Its Π₂ induction uses the checked finite propositional calculus and
quantifier monotonicity; it does not restrict formula codes to standard naturals.

The [actual check](results/r2neg-verification.json) passes nine named axiom
probes and twelve typed callers, including both implications and quantified
transport. Source and audit took 12.476 and 2.377 seconds, at default proof
limits with one thread, 4,096 MiB and a shared 120-second deadline. Axiom
reports contain only standard Lean axioms. The unchanged source has one
unused-section-variable warning at the private `sigma1_to_pi2` helper; the
audit has none. No linter was disabled and the successful source was not edited.

The direct guard reuses 25 exact project source/object pairs from the actual
R2Ctx check, seven inherited external boundaries and Init/Omega. It preserves
R2Ctx's separate existing source warning. It verifies the selected providers
without claiming a fresh attestation of the complete Foundation namespace
overlay or rehashing unrelated ancestor inputs. The
[publication record](results/r2neg-publication.json), [guard and logs](r2neg/)
and [history](r2neg/history.json.gz) preserve that scope.

This is one prerequisite of the upstream R2 translation. The remaining
quantifier, axiom and interpretation units, full validator equivalence and
final binary240 PA composition require their own checks.
