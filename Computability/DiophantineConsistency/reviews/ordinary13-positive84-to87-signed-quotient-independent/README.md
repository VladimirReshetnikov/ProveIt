# Independent source review: 84/87 signed quotient interface

No mathematical mismatch was found in the reviewed quotient interface. This
is a bounded source-level review, not Lean elaboration, provider validation,
or a proof that an 87 graph zero satisfies the pending binding.

For the actual 87 graph, let `b=J*beta`, `h=(1+b)^3`, `Y=v 7`, and take
`t=ell+k+r-k*Bt`. Its root rows give
`z=h*b*t+Y*b-h*Bt`; its vanishing first residual gives
`z²=(h*b)²*(1+ell*(ell+k))`. The proposed `ScaledFirstCut` asks for exactly
this root equation and a natural represented norm factor `n`; it does not
silently infer either from the graph. The forward binding separately requires
that the actual signed beta port equals the embedded natural beta in the
same model. Positivity of Y comes from the positive valuation.

The inherited `positive_quotient_of_signed_norm` applies the existing signed
square-divisibility interface with `h>0`, yielding `h | z`. The root equation
then gives `h | Y*b`. The displayed Bézout identity
`h-b*(b²+3b+3)=1` cancels b without assuming beta positive or a model gcd
calculation. The signed-to-natural interface has the required exact type,
so it proposes a natural quotient `Y=h*s`, and Y>0 gives s>0. This includes
the b=0 case, where h=1. In `forward_of_norm_binding`, the represented port
and the cast of the same quotient supply the required `ScaledY`, while
`q=1+b>0` supplies nonzero q.

The actual graph-to-`ScaledFirstCut` construction and the separate reverse
positive-root witness remain explicit open obligations. The checked source
also depends on an unelaborated quotient proof and its signed-square,
reflection and model providers; their presence and type signatures here do
not establish correct elaboration or sound provider ancestry. A root equation
without the norm does not imply the quotient conclusion.

Reproduce from `Computability/DiophantineConsistency`:

```
python3 -I -S -B reviews/ordinary13-positive84-to87-signed-quotient-independent/check.py
```

The receipt pins the inspected sources, checks the exact graph rows and
interface signatures, and evaluates bounded integer controls. It does not
run Lean or prove the result in arbitrary models.
