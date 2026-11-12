# Eta-natural unit factors to signed and natural norms

This is a **conditional, unelaborated source draft**. It takes the exact `+1`
factor equations as assumptions; it does not show that a graph zero forces
those equations, bind the graph ports, or prove an endpoint. Its variables
are model naturals in an arbitrary intended IΣ₁ model, with signed roots and
factor equalities in `DiffRing V`. Eta is arbitrary, including zero.

The first factor assumption is

```
1 + z² − b² * (1 + ell*(ell+k)) = 1,
ell = (X*Y²)*k.
```

A free-ring identity rewrites the parenthesized term as
`1+(X*Y²)*(X*Y²+1)*k²`. `first_norm_of_unit` proposes to apply the existing
`Residue90SignedNormsDraft.first_natural_norm` once `b>0` is supplied. That
helper obtains a natural signed magnitude and applies
`ArithmeticAdaptiveQuotients2011.scaled_quotient`; it is a graph-independent
fact-level source, not a theorem about this prototype's zero.

The second factor uses

```
a=X*Y+Y, c=eta+Y*k, H=3+4*a, delta=H+a², U=Y*q²,
P=U*(X+a*c)+H*(U*gamma+R+1), N=H*k,
1 + (P−N)² − U²*(1+delta*c²) = 1.
```

The `P−N` expression matches the eta-natural structural prototype's Dstar
at its stated cut: `kbase=k−1` as a signed equality, and the graph's shift is
`U*gamma+R+1−k`. In particular this carrier has **no `X*Y*q` term**; the
residue-90 graph wrapper does contain such a term and is not applied here.
The draft explicitly requires that the signed `P` and `N` are represented by
these model naturals. The actual graph's signed rank expression can be
identified with natural `R` only after the relevant order and truncated
subtraction conditions are justified.

`main_pair_of_unit` proposes the natural magnitude equation via
`Residue90SignedNormsDraft.main_pair_norm`, which uses
`P72Root.ι_magnitude_sq` and injectivity of the model embedding.
`main_natural_of_unit` additionally assumes `U>0` and proposes the square
root via `main_natural_norm` and the scaled-quotient theorem. Finally,
`rank_congruence_of_main_unit` passes the exact magnitude norm to
`EtaZeroEarlyCongruenceDraft.rank_congruence_of_main_norm`, with its `q>0`,
`Y=q³*s`, `Y≥8`, and `k>0` hypotheses explicit. Its conclusion is only
`q⁴ ∣ magnitude (R+1,k)`, not the full early index, eta-zero contradiction,
or a graph-zero equivalence. The separate strong/auxiliary factor declarations
only rearrange or restate signed factor equations; they do not manufacture
natural subtraction or positivity of `f` and `y`.

The unit-factor bridge is a separate task. It must provide **these exact**
factor equations, the precise signed first root `z`, and the natural
representations/bounds; product equal to one alone is not assumed sufficient
here. The exact literal prototype, all four factor-to-unit proofs, positive
`b` and `U`, natural rank/port casts, main and first-root sign/quotient facts,
fixed compact-port bindings, and source/provider compatibility remain open.
The existing signed-norm and early-congruence sources themselves have not
been elaborated as this client. No `#print axioms` output, Lean build, physical
PDF binding, or internal-iPRA theorem is claimed.

`check.py` pins the selected source bytes and prototype, checks selected
literal DAG rows, and verifies the two cut identities in a sparse free
commutative polynomial ring over the integers. These checks do not prove the
model embeddings or source elaboration. From `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary13-eta-natural-unit-norm-adapter-draft/check.py | cmp - research/ordinary13-eta-natural-unit-norm-adapter-draft/receipt.json
```
