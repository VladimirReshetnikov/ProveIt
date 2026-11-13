# Independent arithmetic review of the wider index windows

The ordinary-integer argument in the reviewed note is valid under its
explicit hypotheses, including `Y≥q³`, the same-tuple Pell gap and weighted
projection. The source note SHA-256 is
`a5637f53f1bfec207b86f64c9cef3c3f417d467ee55a33e231807fcf065174c6`;
the finite checker SHA-256 is
`4c1fbde22ef703974ef6b6363d5a617c879ff9c4fd0065a2636de93b1c9c7cd6`.

Independent exponent comparison: the Pell gap and a hypothetical failure
of the height lower bound give
`Y^(n−3c)<2^(5c−1) h^c K^(2c)`. The stated size bounds force the
opposite when `n≥4c`: after dividing the power of `q` used to bound `h^c`,
the base-two exponent surplus is
`(90−2c)n−305c−2c²+1`, whose minimum at `n=4c` is 76, 61 and 26 for
`c=3,4,5`, respectively. The graph's cubic size bound is required for
this particular estimate; replacing it by `Y≥q²` does not justify the
same thresholds.

The checker was rerun with `python3 -I -S -B` and exited zero, reporting
those three margins. It checks finite exponent bookkeeping, not the
universal inequalities, graph assumptions, or a Lean theorem. No model
formalization, 74-operation reverse guard, or iPRA endpoint is claimed.
