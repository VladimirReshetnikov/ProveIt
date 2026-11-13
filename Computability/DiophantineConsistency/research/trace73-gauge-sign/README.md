# Conditional negative-`B` centered witness

For a commutative ring with a compatible strict linear order, let `h=p₀v₀`,
`q=h+1`, and `s=(p₁+v₅)q+1`.  The checked theorem
`Trace73GaugeSign.positive_zero_to_negative_B` assumes

* `h≥1` and `p₁+v₅≥0`;
* all ten coordinates are positive;
* the original centered coordinate satisfies `v₇>s`; and
* the actual literal 73-row graph evaluates to zero.

It constructs another positive ten-coordinate zero of the same literal
graph, at the same ports, with `B<0`.  The companion theorem proves that the
single gauge step makes `B` negative under the stated scalar hypotheses.

This is conditional: it does not produce the starting zero or establish its
center bound.  In particular, it does not refute equivalence of existence of
positive 73-row and 75-row zeros, and it does not supply a natural-valued
witness in every nonstandard model.  At `R=ℤ`, its positive coordinates are
positive integers.  This result cannot be used to assert an unconditional
counterexample or the reverse 73-to-75 implication.

Author attempt04 exited 0 and produced
`/tmp/trace73-gaugesign-h910a9nh/Trace73GaugeSign.olean` with SHA-256
`735a09a4bce63b9c329e7e2e661e291437da744a3ac1a962e48aeea148ecbccc`.
Both theorem axiom reports are `[propext, Classical.choice, Quot.sound]`.
The source SHA-256 is `4101fe161d5fc36f8dc062494b67de217a502bf51dbd3e09074f231c77a2cdb4`,
runner SHA-256 is `1521fe020d58fb01ca6017d8ef76fd3c008fd408ada78e4020bfaa28c2c4baba`,
and terminal record SHA-256 is `475db86865292a2504ea311c3235c337b1c4e455da7b82df9199b6212b904047`.
Three previous failed attempts remain in `observations/`.

The runner pins the direct gauge, literal, centered graph and newly imported
ordered-ring and tactic objects, and checks the first selected objects for the
two newly imported Mathlib modules.  It inherits the other provider and
package ancestry and is not a complete transitive build or independent
Lean replay.
