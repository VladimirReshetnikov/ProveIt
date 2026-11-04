# Factored `n=6,r=11` upper endpoint certificate

This source-only arithmetic plan is not yet checked in Lean. It replaces the 397-term bivariate positivity expansion whose [Lean author attempt](../trace74-n6-r11-scalar-draft/README.md) timed out. No resource hotspot is inferred from the timeout.

Let `x≥32`, `t≥T`, where `T=x⁵+10x⁴+45x³+120x²+210x+260`, and put `a=x+1`, `d=xt²+2`, `z=ta+2`. Let `y₀(u)=0`, `y₁(u)=1`, `yₙ₊₁(u)=u yₙ(u)−yₙ₋₁(u)`, `ky=t y₆(d)`, and `c=y₁₁(z)`. The checker verifies

```text
y₆(2+u) = u⁵+10u⁴+36u³+56u²+35u+6
y₁₁(2+u) = Σ(j=0..10) cⱼuʲ
cⱼ = [11,220,1287,3432,5005,4368,2380,816,171,20,1].
```

Since `t≥T≥1`, all omitted terms in `ky` are nonnegative and `tʲ≤t⁹` for `0≤j≤9`. Thus, with `C=Σ(j=0..9)cⱼaʲ`,

```text
ky ≥ x⁵t¹¹,       c ≤ a¹⁰t¹⁰+C t⁹.
```

Put `D=x⁵T−a¹⁰` and `P=DT−C`. After `x=32+u`, their coefficient lists have respectively 6 and 11 strictly positive entries, verified by the checker. Since `x⁵≥0` and `t≥T≥1`, `x⁵t−a¹⁰≥D>0`, so `(x⁵t−a¹⁰)t−C≥DT−C=P>0`. Multiplying by positive `t⁹` yields `ky>c`. Hence any strict scalar gap `ky<c` forces `t<T`.

Run `python3 -I -S -B research/trace74-n6-r11-upper-compact-certificate/check.py` from `Computability/DiophantineConsistency`. The receipt captures exact results and negative controls. This is a conditional scalar upper bound only; no Lean, graph, fixed-port or endpoint claim is made.

The [independent arithmetic audit](../../reviews/trace74-n6-r11-upper-compact-certificate-independent/README.md) passed the recurrence identities, univariate coefficients, and conditional inequality argument. It does not establish Lean or graph binding.
