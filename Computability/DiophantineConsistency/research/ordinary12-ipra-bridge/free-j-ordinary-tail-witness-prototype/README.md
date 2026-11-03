# Constructing the ordinary factor from tail witnesses

For any model of `IΣ₁`, coefficient tuple, and 12-coordinate valuation,
`ordinary_unit_of_witnesses` proves that the exact free-J literal's third
signed factor represents `+1` when there are difference-ring elements `i,u`
satisfying

```
q = d*i*i,     n = i+u,
(1-q)*(z+u)^2 + q*z^2 - 1 = 0.
```

Here `q,d,z,n` are the actual four graph expressions exposed by `parts`,
evaluated in the model's difference ring; they are not independent graph ports.
The theorem does not assume an internal graph zero, positive coordinates, or a
standard model. It follows by an exact ring factorization of the polarized
tail and the existing checked graph-residual identity.

This is an implication from specified witnesses, not their construction. It
does not establish the first two factor equations, positive coordinates, the
link from a model halt to these witnesses, coefficient calibration, or an iPRA
proof. Difference-ring existence alone is weaker than a construction of the
specific natural coordinates needed for the final 12-variable graph.

The bounded author attempt 02 exited 0 in 3.728 seconds with no warnings or
`sorryAx`. Source SHA-256 was
`2f8fe6cf44a614817cb1af692eea58b1a95e70bbbd8f27c1690f42f39ea074cf`;
the object `/tmp/free-j-ordinary-tail-witness-author-cdbrbrco/FreeJOrdinaryTailWitness.olean`
had SHA-256
`b36cc3c0c13c6aba7538ec3587933b816907706432cb38d8419391f8799474fe`.
Direct dependency and companion guards, including the imported signed-transport
object, and all 70 live files of its selected coexistence author provider were
unchanged. This is not an independent replay or an audit of inherited
package-transitive and dynamic dependencies. The axiom report is `propext`,
`Quot.sound` for the ring identity, and additionally `Classical.choice` for the
model factor theorem; these are Lean metatheoretic dependencies.

Attempt 01 elaborated with exit 0 but the runner rejected a style warning; its
source, log and receipt are preserved. Attempt 02 removed the warning without
changing either theorem statement.
