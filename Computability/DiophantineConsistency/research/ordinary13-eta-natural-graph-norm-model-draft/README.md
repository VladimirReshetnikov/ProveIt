# Eta-natural graph: proposed first/main natural norms

This is an **unelaborated source-only client** for the exact generated
eta-natural structural prototype. It imports its signed norm proposal,
the graph's J client and the graph-independent signed-norm quotient draft.
It assumes ports are integer casts of a natural tuple `p`; no fixed compact
constant or physical PDF is identified. The prototype and all imported
research sources/providers remain unbuilt.

The proposed field declarations bind the literal graph's evaluated
`b`, `k`, `ell`, `U`, `c`, and `Delta` to natural model values:

```
b=J*beta, q=1+b, X=q*v6, Y=q³*(v7+1), k=v9+v10+1,
m=X*Y², ell=m*k, U=Y*q²,
c=v9+Y*k, a=X*Y+Y, Delta=3+4a+a².
```

`v9` is eta itself, so eta=0 is allowed; zeta is `v10+1`. The checker
verifies all six expressions and `1+ell*(ell+k)=1+m*(m+1)*k²` as
polynomial identities against the pinned actual prototype, with arbitrary
formal variables. The proposed Lean field proofs additionally require the
natural-to-integer-to-difference-ring port cast (`P72Root.cast_port`) and
must be elaborated to validate their simplification and tactic details.

At graph zero the previous `signed_norms` source proposes the actual graph's
first and main squared identities. With `b>0`, `first_natural_norm` retains
the literal first signed root and proposes a natural `tau` satisfying
`tau²=1+m*(m+1)*k²`. With `U>0`, `main_natural_norm` retains the literal
main signed root and proposes a natural `g` satisfying
`g²=1+Delta*c²`. Both use the existing graph-independent signed magnitude
and exact scaled-quotient sources. These roots are witnesses to norms;
the latter theorem does not identify its g with an oriented main quotient
or a Pell-index x coordinate. It needs neither positive C nor an equality
between the graph's signed rank and a natural rank. No original free-J
`core.z` is silently substituted.

`natural_norms_of_graph` proposes both roots from graph zero and explicit
positive model beta, using the previous eta-natural J positivity draft to
show `b>0` and the always-positive `q`, shifted s to show `U>0`. Neither
positive X nor eta positivity is assumed. The J proof itself needs the natural
second port K0 and the exact first-factor unit bridge, so those dependencies
are inherited.

The separate `EtaNaturalGapRankDraft` defines the same model X and m, proves
a proposed positive gap, and gives `rank_representation` from the explicit
`F≤q` premise, using `P72Root.ι_tsub`; its compact window client also has
fixed mask/source dependencies. This packet deliberately does not copy or
reprove that work. Connecting `g`, the first-index witness, the signed
main-root orientation and exact index uses those and further source-level
clients. Model port/byte/PDF provenance, all graph zero maps, coherent
providers, actual `#print axioms` results and internal-iPRA equivalence are
not established here. Proposed commands in `.lean.src` have not run.

From `Computability/DiophantineConsistency` the following reproduces the
read-only pinned source and polynomial receipt:

```
python3 -I -S -B research/ordinary13-eta-natural-graph-norm-model-draft/check.py | cmp - research/ordinary13-eta-natural-graph-norm-model-draft/receipt.json
```
