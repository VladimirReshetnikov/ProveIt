# Conditional natural four-block bridge

The all-ring four-block identity is already checked. This draft proposes a
bridge to the natural-number block equation required by saturation, assuming
that the signed rank has a specified natural representative, `0<C<=q`,
`F<q`, `HP*J>=1`, and `q=beta*J+1`. The assumptions are individual bounds:
the desired reverse guard `F+C<q` is not assumed.

The first Lean attempt exited 1 because the source did not import the
model-arithmetic namespace; it accepted no theorem. Its exact source, runner,
logs, result and separately observed outer exit are in `observations/attempt01`.
After adding `ArithmeticSaturation`, attempt02 passed Lean in actual outer
session 93585, exit 0. The source SHA-256 is
`49d908e5b290c76613da30d72523670243c66731b474c03634bab30d6b0013f7`,
the captured result SHA-256 is
`9c08bc856d21fd487315a4ebd3e65460d4bd64be1a8ff2b9810a582d4f0f2346`,
and the object SHA-256 is
`63cac4c4534d9c5fb79a5e261f8d236c76be9dbc874c3a06631ba0da62682352`.
The named report lists `propext`, `Classical.choice` and `Quot.sound`.
The source's 'unchecked draft' comment predates this successful run.
An [independent result audit](../../reviews/trace74-natural-block-result-independent/README.md)
checked the direct pins and conditional statement; project/package/dynamic
ancestry and search-path shadowing remain inherited.

The theorem does not show that a positive 74 graph zero supplies any natural
representative or range assumptions, the population bounds, the guard, or the
iPRA equivalence.
