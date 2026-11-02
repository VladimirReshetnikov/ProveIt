# Concrete compact support and symbolic mask recipe

The Lean source defines the finite support S as the union of `[0,943)`,
`[983,993)`, `[1003,1012)`, `[1013,1032)` and
`{1063,1064,1095,2195,3296}`, with position 1 erased. It proves S lies below
8,807 and contains positions 0 and 1063. From the generic finite-list identity,
Lean proves, without expanding the resulting numeral, that the associated
mixed mask list has natural value

```
(2^67)^8807 − 1 − ∑(j ∈ S) (2^67)^j − 2 * (2^67)^1063.
```

Lean also rewrites this equality symbolically into the bit-exponent form
`2^590069 − 1 − ∑(j ∈ S) 2^(67*j) − 2*2^(67*1063)`, matching
the shape of the retained builder recipe. The special slot's total defect is 3 (one from S plus the final 2); slot 1 has
defect zero. For the cast of this explicitly defined list value into every
IΣ₁ model, the source derives the mask's three-class digit bound, word-size
bound and ordinary origin digit. The support ranges match the independently
checked retained builder recipe in the external `compact44-selector-recipe`
checks and the finite support packet aabfd87212. That comparison to the
retained builder and compressed MC bytes is external: no Lean equality between
this list value and the retained MC bytes, equation's graph port, or any input
literal is claimed here. The machine checker and PRA proof remain open.

The first exploratory session 37727 exited 1 because finite-set `decide`
reached its recursion limit and a target membership was not simplified.
Session 43679 exited 0 after symbolic finite-set simplification; session 91264
exited 0 after adding the model digit/size/origin results; session 42308 exited
0 after adding the bit-exponent form. The initial source
and the three logs are retained. The subsequent paired replay and provider
audit are recorded separately.
