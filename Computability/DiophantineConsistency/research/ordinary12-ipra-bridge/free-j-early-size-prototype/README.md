# Free-J early size and the later integral-solution boundary

For the exact free-J zero in any `IΣ₁` model, positive coordinates and β,
and explicit model bounds `MC < β` and `MF < 2β`, Lean proves
`(a+2)·Δ(a)² < c` and `2R < c`. It uses the early comparison of the first
and main Pell indices; neither a strong norm nor final index matching is a
premise. The four ports are arbitrary naturals satisfying the displayed
bounds, not yet a formal interpretation of the compact44 tuple.

The historical theorem `ArithmeticPellIntegralSolution.integral_solution_tsub`
has the exact scalar inputs and premises

```
(a c p i f : V)
0 < p; 0 < i; 0 < f; c = ycoord p a;
(i*c*c)*(i*c*c) = delta a * (f*f-1);
(a+2)*delta a*delta a < c.
```

The replayed index-comparison chain provides a positive main Pell index `p`
and its `c=ycoord p a` equation, and this theorem provides the final size
inequality. The graph has `f=t+1`, structurally positive, but its specific
model binding is not proved in this packet. More importantly, the positive
ordinary multiplier `i` and its strong-norm equality are **not** established.
They require the separate ordinary-tail adjacent-coefficient integrality
descent; the historical integral-solution theorem itself assumes the strong
norm and cannot be used to prove that premise. A graph-specific invocation,
compact44 checker calibration and object-level iPRA proof remain open.

Fresh historical replay session 70563 exited 0 and printed
`PASS_BOUNDED_FREEJ_EARLY_SIZE
a8d63f37e23973b148db16b6eedc3c6a88b0d15ef248d6db14608d142867b865`.
The receipt records the axiom report, direct imports, source/object hashes,
and inherited fresh comparison/provider replay. Exploratory session 68676
also exited 0. This is a single-author model replay, not a matched full
project build or a dynamic/package-transitive dependency audit.
