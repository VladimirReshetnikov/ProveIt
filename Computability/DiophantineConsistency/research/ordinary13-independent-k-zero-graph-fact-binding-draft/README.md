# Independent-k child: proposed zero-k norm bindings

`IndependentKZeroGraphFacts.lean.src` is an **unelaborated Lean source proposal** connecting the exact 84-row child's unit/norm interface to the fixed-compact conditional client at `v 10=0`. It keeps the same fixed tuple, embedded valuation and literal main root throughout.

The draft defines the actual child model-natural values `q=beta*J+1`, `X=q*w`, `Y=q³*(n_s+1)`, `U=Y*q²`, `a=X*Y+Y`, and `H=3+4a`. It proposes literal first-field identities and derives the zero-k first norm from `IndependentKUnitBridgeDraft.signed_norms`. It also proposes the literal main-root shape and main signed norm at k=0, again using that same signed-norm interface. The generated graph's slot 10 is the independent k coordinate.

The signed graph rank is explicitly defined as

```text
rankRing = (alpha+(q-F)*beta*J)*(q²−1) + J*(MC+q*MF)
```

with subtractions in `DiffRing V`. The final proposed conditional graph client requires an **explicit** model natural `R` and `rankRing=ι R`; it does not assume a natural subtraction or prove that this rank representation exists. A separate effort is investigating that step. The client then calls the fixed-port first-rank obstruction with the graph's main signed root and the same R. The proposed fixed-port source also supplies J positivity and the compact beta/K0/mask assumptions, conditional on its own dependencies.

The checker pins the source, generated child, unit bridge, fixed-port client and cast provider, checks direct graph row and interface names, and evaluates 1,000 bounded actual graphs at k=0 against the proposed first, rank, root and norm expressions. These controls do not prove the equalities in all models or check Lean elaboration. In particular, the source's `simp`, `convert`, `ring`, rewrites, instances, port casts and all transitive providers remain unverified. There is no proof yet of existence of R, a parent-child zero map or an iPRA endpoint.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B research/ordinary13-independent-k-zero-graph-fact-binding-draft/check.py | cmp - research/ordinary13-independent-k-zero-graph-fact-binding-draft/receipt.json
```
