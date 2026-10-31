# Bounded first/main Pell-family screen

`screen-first-main-family.py` exactly screens one restricted family for the necessary congruence imposed by **first and main factor = 1**. It takes `q=2..6`, `Y=n*q³` with `n=1..4`, and `X=1..100`. For `t=X*Y²`, it generates the first five positive powers of `(2t+1)+2√(t(t+1))`; their ordinates are candidate `k=eta+zeta`, satisfying the first discriminant square. For `a=Y*(X+1)`, it generates the first sixteen positive powers of `(a+2)+√(a²+4a+3)`; their ordinates are candidate `c=eta+Y*k`, satisfying the main discriminant square. It keeps only `eta=c-Y*k` with `1≤eta<k`, so `zeta=k-eta>0`.

For each surviving pair and either sign of the main Pell root `d`, the code checks the necessary divisibility `H ∣ U*(±d-L)`, where `H=3+4a`, `U=Y*q²` and `L=X+a*c`. This follows from the main-root expression `D=U*L+H*(...)` and the assumed first/main factor equations, which require `D=±U*d` in the chosen integer Pell subfamily. Exact integer arithmetic checks each generated Pell norm.

The saved result has 160,000 index combinations, 24 with positive eta and zeta, and **zero** passing that divisibility check. Reproduce with `python3 Computability/DiophantineConsistency/research/adaptive-gap85/screen-first-main-family.py` from the repository root. This does not enumerate arbitrary Pell solutions or general 85 witnesses, does not use the real fixed constants, does not prove the reverse bound, and cannot establish minimality or absence of a full zero. The other factor units and the integer feasibility of F, C, r and gamma are not checked.

A separate repeat in another process returned successfully with output byte-identical to `SCREEN-FIRST-MAIN.out`. It confirms this bounded computation and does not enlarge the stated search scope.
