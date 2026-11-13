# Independent review: C-fold witness algebra draft

No concrete algebraic, order-hypothesis or stated model-interface mismatch was
found. The draft is unelaborated and does not prove either graph evaluator
binding, the positive witness hypotheses, an all-model bridge or an iPRA
endpoint. The authored receipt and this review's checker reproduce.

The pinned graphs have the same witness/port order and differ in exactly the
first-root `k*Bt` versus `k*C` gate. For the fact-level roots, substitution
`r_old=rho+k*(Bt-C)` cancels the skew difference exactly; the inverse
`rho=r_old-k*(Bt-C)` is the reverse ring identity with no positivity implied.
The sphere identity follows once the other three residual values and the two
first-norm scales are the same. For the switched map, the stated substitutions
`M=q3*b`, `Y=q3*s`, `Bt=b*t` reduce the child root to
`M*(tau-s+t)+q3*s*b-q3*b*t=M*tau`. These are free commutative-ring
identities; neither signed integer examples nor the identities alone bind a
Lean expression to a JSON graph.

The `bt_gap` hypotheses are sufficient in a linearly ordered ring: q>=2,
C>=1, X>=q² and K>=0 give `X+Kq-1>=0`, so

```
Bt-C = C*(X+Kq-1)-Fq
     >= q²-1-(q-2)q = 2q-1.
```

The inequality is sharp, for example q=2, C=1, X=4, K=F=0. Its use for an
actual zero still requires the model-Cal conclusion and port/rank casts. The
direct positive map needs only positive rho, k>=0 and C<=Bt. The switched
map's stated assumptions C>=1, k>=0, `s<tau-ell` and t>=0 make its displayed
coordinate positive. The missing parent root, quotient and Pell-gap witnesses
remain separate facts.

For `[ORingStructure V]` with V modelling IΣ₁, the cited
`ModelDifferenceRing` source declares the commutative ring, linear order and
strict ordered-ring instances, and its `ι_nonneg` and `ι_lt_ι` signatures match
the representative draft. The prospective `positive_as_successor` source
accepts an explicitly positive difference-ring value and returns
`ι(n+1)=D`; it matches both wrappers. The direct wrapper starts from
`ι(rho+1)`, correctly representing a positive-shifted coordinate. These are
source inspections only: the ring/order instances, coercions, tactics and
helper theorem have not been elaborated together.

The imports `CfoldWitnessAlgebra` and `PositiveGapRepresentation` are
prospective local module names; the inspected standard project source tree
contains no corresponding `.lean` modules. A future selection must map them to
the pinned `.lean.src` files or their reviewed copies and check transitive
providers, namespace resolution and tactics. No specific missing mathematical
import was established from this bounded inspection, and import sufficiency is
unproved. The `Fin 13` coordinate-8 update and whole-output equality are also
still required.

The checker verifies pinned source/interface text, the exact graph delta,
2,500 signed wiring controls and the ordered bound's equality case; it also
reproduces the author's exact free-ring receipt. These finite controls are not
a substitute for the ring arguments above or Lean elaboration. From
`Computability/DiophantineConsistency` run:

```
python3 -I -S -B reviews/adaptive87-current-cfold-witness-algebra-independent/check.py | cmp - reviews/adaptive87-current-cfold-witness-algebra-independent/receipt.json
```

No Lean, build, staging, provider replay or author-evidence mutation occurred.
