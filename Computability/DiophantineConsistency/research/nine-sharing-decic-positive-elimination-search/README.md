# Positive-gate decic elimination search

This search repeats the pinned sign26 positive direct-variable substitution
exploration, allowing residual syntactic degree at most five at each step,
which yields a square-sum degree upper bound of ten. It visits 22 ordered
states; their smallest witness count is 23, in the same six q3/ell/Delta
orders as the octic search. Thus this restricted stepwise search finds no
22-witness decic improvement on the existing 22-witness degree-12 candidate.
It does not exclude other transformations, variable encodings, signed-gate
arguments, cancellation or globally smaller equations, and it proves no Lean,
model bridge, exact algebraic degree, or iPRA claim.

`python3 -I -S -B search.py > result.json` exited 0. Source seed SHA-256:
`36efa7dd3b2ea06d210b8975db2cbfc4f7494549c87204ada18747a720cb1f25`;
search SHA-256:
`0b082cda64cb1ef19f3fc6e9cad4e3c9961582bf14a11e2622fe2093efeabe83`;
result SHA-256:
`dffa4d01a7b8f094dfb1bc66f073dbba612c93e00b2e61e47649017d622c9767`.

The [independent audit](../../reviews/nine-sharing-decic-positive-elimination-independent/README.md)
passed; the search packet is frozen.
