# Independent review: compact first-root n=2 boundary

The [reviewed packet](../../research/ordinary13-f-unshift-compact-first-root-n2-boundary/README.md) correctly supplies an actual F-probe first-norm assignment at the fixed symbolic compact ports with `J=1`, `F=0`, `C=beta`, `X=q` and first Pell index n=2. Its two separate reasons that this assignment cannot also satisfy the main norm are sound over the ordinary integers. I found no mismatch in the first root, rank bound or third/fourth Pell-ordinate gap. This is not a full graph zero or a general exclusion of the F=0 positive-gap branch.

For M=q⁷, the second first-Pell iterate has `k=8M+4` and `tau=8M²+8M+1`. The specified natural r and `Bt=beta*(q+K0)` make the exact graph first root `Z=beta*tau`. Thus its first residual vanishes, with eta=0 and `n_zeta=k−1`; this does not imply the main equation.

The compact-mask argument applies more broadly within `J=1, F=0, C=beta` when **both** residuals vanish. The previously independently reviewed signed-root argument then supplies `2n≡R+1 mod q⁵`. The actual rank identity gives `R+1≡MC mod q`; the low mask is even with `0<MC<q`, so any natural solution of `2n≡MC mod q` has `n≥MC/2`. Its least base-2⁶⁷ digit is `2⁶⁷−2`, hence `MC/2≥2⁶⁶−1`. This excludes n=2 in that extremal-C slice; it is not a bound for arbitrary C.

Independently, for X=q, s=1 and first index n=2, put `Y=q³`, `k=8q⁷+4` and `A=Y(q+1)+2`. The third and fourth main Pell ordinates are `4A²−1` and `8A³−4A`. I independently expanded the differences `Yk−(4A²−1)` and `(8A³−4A)−(Y+1)k` in powers of q−2; all coefficients are nonnegative and both constants are positive. Therefore for any eta<k,

```
y₃ < Yk ≤ c=Yk+eta < (Y+1)k < y₄.
```

The ordinary positive Pell recurrence/classification has strictly increasing ordinates beginning at y₀=0, y₁=1, so the main norm has no solution in that interval. This second argument uses no mask bound; it is tied to X=q, s=1 and the n=2 first-Pell coordinate, not to arbitrary witnesses. The pinned `ArithmeticPellClassification.solution_index` is a relevant unelaborated source interface, not a replayed model proof here.

The receipt reproduces the author and predecessor review checkers, pins the exact graph and source interfaces, independently checks the two polynomial gap certificates and extremal rank arithmetic, and evaluates four finite first-root controls. Those controls do not replace the written general arguments. No Lean/build, provider or axiom audit, parent-child zero map or iPRA endpoint was established. From `Computability/DiophantineConsistency` run:

```
python3 -I -S -B reviews/ordinary13-f-unshift-compact-first-root-n2-independent/check.py | cmp - reviews/ordinary13-f-unshift-compact-first-root-n2-independent/receipt.json
```
