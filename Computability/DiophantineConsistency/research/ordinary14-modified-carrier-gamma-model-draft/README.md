# Source-only modified-carrier gamma>w bound

`CarrierGamma.lean` is an **unelaborated and uncompiled source proposal** for the reverse 84→85 positive-coordinate step. It does not import a graph or establish a model theorem, endpoint, provider replay, or PDF/JSON/gzip binding. The two proposed facts state all required carrier, Pell-coordinate, order and positivity hypotheses explicitly.

`gamma_gt_from_carrier` assumes `R≥3`, `X≤a`, `w≤a`, `H=4a+3`, the exact main Pell coordinates `c=ycoord R a` and `d=xcoord R a`, and the natural balance `d+H*W=X+a*c+H*gamma`. It uses existing internal sources rather than a new induction:

1. `ArithmeticHalfBinomialSandwich.power_le_ycoord a 2`, `ArithmeticPow.power_succ`/`power_one`, and `ArithmeticPellRecurrence.ordinate_strictMono` give `c≥(2a+3)²`.
2. The factored inequality `(2a+3)²>a+(4a+3)*a≥X+H*w` gives `c>X+H*w`.
3. `ArithmeticPellPowerRecovery.x_gt a R` gives `d>(a+1)c`. If gamma≤w, the carrier says `d+H*W≤X+a*c+H*w<(a+1)c<d`, contradicting `d≤d+H*W`. This argument needs no natural subtraction gamma−W, no lower-bound theorem for a projection quotient, and no new induction.

`gamma_gt_from_modified_balance` is the graph-shaped fact-level corollary. With positive U,Y, `1≤q`, `X=q*w`, `a=X*Y+Y`, the exact index relation `k=R+1+U*W`, the modified natural carrier balance and the same Pell/index premises, it first derives X,w≤a and cancels positive U to obtain the preceding balance. Neither theorem derives the displayed hypotheses from a graph zero. In particular, **R≥3 and the actual main Pell coordinates must come from the exact-index theorem**; the graph client must supply them. A finite R=2 example shows the index bound cannot simply be omitted.

This addresses only the requested model-level gamma>w ingredient. The 84↔85 client still needs literal signed main-root orientation and quotient extraction, q⁴ rank/index and `P72Exact.indices_ordinary` binding, exact carrier equality, port casts and positive slot updates. The separately drafted `../ordinary14-modified-carrier-model-facts-draft/` addresses some conditional pieces but is also uncompiled. Parent bridges, source/object/Init and transitive provider compatibility, compact byte association, disk/resource guard, exclusive Lean allocation, and iPRA endpoint remain open. Source scripts, arithmetic rewrites, theorem interfaces and resource behavior are untested by Lean; the finite checker is not a model proof or preflight.

From `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary14-modified-carrier-gamma-model-draft/check_source.py > /tmp/modified-carrier-gamma-source.json
cmp /tmp/modified-carrier-gamma-source.json research/ordinary14-modified-carrier-gamma-model-draft/observation.json
```

Independent source review is recorded in
`../../reviews/ordinary14-modified-carrier-gamma-model-draft-independent/`.
