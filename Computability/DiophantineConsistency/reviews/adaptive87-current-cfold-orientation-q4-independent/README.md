# Independent review: current C-fold orientation and q⁴ congruence

No concrete mathematical or literal-binding mismatch was found within the
packet's stated ordinary-integer hypotheses. Its conclusion is conditional on
positive graph inputs, the stated port nonnegativity, `C>0`, and the first and
main norm equations. It does not establish the remaining index alignment,
Cal, zero equivalence, a model-level theorem, or an iPRA endpoint.

## Literal binding and first norm

The independent checker verifies 64 exact named rows in the pinned C-fold
literal, including both complete first/main residual chains, the signed rank,
the `k*C` skew and the `(k-R)-1` shift. It also independently evaluates 100
signed-port wiring controls and reproduces the author's receipt. The numerical
controls are not a universal proof. The port nonnegativity and beta bounds are
inherited from the pinned current-payload receipt; Lean-to-payload and PDF
semantics are outside this review.

With `b=J*beta`, `q=b+1`, `M=q³*b`, and positive beta and witnesses,
`M>0`. From `A0=0`, integer square divisibility gives `M|Z` independent of
the sign of Z. The exact first-root formula modulo q³ yields `q³|Y*b`;
`gcd(q,b)=1` gives `q³|Y`. Reduction modulo b also yields `b|Bt`, because
`q³≡1 (mod b)`. This second fact and any sign of Bt are unnecessary for
the orientation/congruence proof.

## Orientation and the factor three

`C>0` implies `q-F>alpha>0`, so `G>0`; nonnegative MC/MF then gives `R>=0`.
As `c=eta+Y*k>Y*k`, `U=Y*q²`, `q>=3`, `Y>=1`, and `a>=2`, one has
`U*a*c > q²*Y²*a*k > (4*a+3)*k = H*k`. Thus the exact main-root expression
is strictly positive even if `R+1-k` is negative. Together with `A1=0`,
standard integer square divisibility provides `Dstar=U*d` with positive
integer d and `d²=1+Delta*c²`.

Writing `Y=q³*s`, the main balance gives q⁵ divisibility of
`H*(E*q+R+1-k)`. Since `H=3+4*q³*s*(X+1)`, any prime common to H and q is
3. If 3 divides q then `H≡3 (mod 9)`, so its 3-adic valuation is exactly
one; otherwise their gcd is 1. Consequently `gcd(H,q⁵)=gcd(3,q)` divides q.
The elementary integer gcd divisibility rule therefore leaves a factor q⁴ in
`E*q+R+1-k`, and q⁴ also divides `E*q`, proving `q⁴ | R+1-k` even when the
last expression is negative. No cancellation of 3 as a unit is assumed.

The checker independently exercises q divisible and not divisible by 3,
including multiples of 9, and signed congruence values. These finite controls
supplement the argument above; the source `scaled_quotient` has natural-model
arguments and would require explicit signed/magnitude and graph bindings in a
future model proof.

From `Computability/DiophantineConsistency` reproduce with:

```
python3 -I -S -B reviews/adaptive87-current-cfold-orientation-q4-independent/check.py | cmp - reviews/adaptive87-current-cfold-orientation-q4-independent/receipt.json
```

No Lean, build, staging, provider replay, or modification of author evidence
was performed.
