# Independent review: zero-ordinate main obstruction

The conditional arithmetic argument is sound as stated. In an integral difference ring, `z²=U²` splits into `z=U` and `z=-U`. The given main-root shape then yields respectively `H ∣ U*(X-1)` and `H ∣ U*(X+1)`. When `X=0`, the first branch uses `L=1`; otherwise `X=q*w` and `q≥2` give `X≥2`, so `L=X-1` is positive. The second branch uses `L=X+1`. In every case `0<L≤X+1`.

The pinned signed-to-natural divisibility interface has the exact required direction: `ι H ∣ ι (3*q²*L)` implies `H ∣ 3*q²*L`. The independent checker verifies the divisibility certificate as an exact multivariate polynomial identity. Since `q³≤Y` and `q≥2`, `q²≤Y`, giving `0<3*q²*L≤3*Y*(X+1)<3+4*Y*(X+1)=H`; positive divisibility contradicts this strict bound. The natural subtraction cast in the first sign case is used only after the source derives `1≤X`.

The checker independently compares the relevant probe rows: eta=zeta=0 makes `c=0`, and the actual root becomes `U*X+H*(U*gamma+R+1)` with `H=3+4*Y*(X+1)` and `U=Y*q²`; the main residual then becomes `z²-U²`. It also reproduces the author's deterministic receipt. These structural observations do not derive the main residual's vanishing from a zero of the product graph: unit-factor extraction, graph/model/port bindings and `q≥2` remain separate obligations. The theorem does not address eta>0 at zeta=0, nor establish a zero map or a reduction.

Run from `Computability/DiophantineConsistency`:

```
python3 -I -S -B reviews/ordinary13-eta-zeta-zero-main-obstruction-independent/check.py | cmp - reviews/ordinary13-eta-zeta-zero-main-obstruction-independent/receipt.json
```

This is a source and algebra review. All proposed Lean terms, especially ordered-model inequalities and divisibility coercions, remain unelaborated; provider closure and an iPRA endpoint are not established.
