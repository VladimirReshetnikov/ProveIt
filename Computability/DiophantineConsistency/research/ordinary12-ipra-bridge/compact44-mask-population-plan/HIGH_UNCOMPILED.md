# Proposed compact44 high-mask population cut (uncompiled)

For the original retained compact44 native high-mask recipe, write ρ = 2^67,
L = 8807, and μ = 2^51−2. The finite support consists of radix-ρ digits:
position 0 has 4; positions 4393 and 5495 have μ; positions 1013–1022,
1065–1073, 2195 and 3296 have 1; positions 8792–8804 have 2^65−1; and
position 8805 has 2^19−1. All other positions have 0. The pinned finite
recipe audit independently confirms these positions and the native-versus-
shifted high-port relation; it is not an all-model graph-port theorem.

The expected population is 1 + 2·50 + 10 + 9 + 2 + 13·65 + 19 = 986.
Together with the separate proposed symbolic low-mask population 589083,
this gives d = 590069. Position zero also gives HP mod 8 = 4 and HP > 0.

Possible proof: define an explicit standard finite list of radix-ρ digits by
position; prove its digits below ρ, its natural value equals the symbolic
finite high-mask expression without expanding the integer, and its finite sum
of bitcounts is 986, splitting the disjoint ranges. Apply the all-model
`ArithmeticMaskConstants.population_ofDigits` and `dig_ofDigits` lemmas for
the cast list value, plus a remainder lemma for the origin. The exact available
API, definability and range/cardinality proof details must be checked. One must
still prove the high graph port is this symbolic value plus β, and bind that
expression to retained MF bytes. Neither the no-carry premise nor the machine
simulation or an internal PRA derivation follows from these finite facts.
