# Independent review: fixed F=0 positive-gap norm congruences

The [reviewed argument](../../research/ordinary13-f-unshift-fixed-positive-gap-norm-congruences/README.md) correctly derives its listed necessary conditions over ordinary integers from the **two residual equations** at the exact fixed symbolic compact tuple, in the explicitly restricted slice `J=1`, `F=0`, `C=q−alpha>0`. I found no mathematical mismatch in X positivity, the first-Pell classification, parity or the two q⁵ congruences. It does not extract these residuals from a product zero, exclude the branch, treat J≠1, or provide a Lean/model/iPRA proof.

The actual F-probe's first root and rank rows give `Bt=C(X+K0)`, `Z=beta(ell+k+r−kBt)−Bt`, `ell=Mk`, `M=XY²`, and `R=(q²−C)(q²−1)+MC+qMF`. Its main shift uses `r0=kbase−R=k−1−R`; hence its signed main root is `U(X+ac)+H(U gamma+R+1−k)`. The checker independently inspects these exact rows and the shifted-k input.

From the first norm, beta² divides Z², so beta divides Bt; `q≡1 mod beta` then gives `beta | C(w+K0)`, without assuming a sign for Z. From the main norm, U divides Dstar and yields a signed d with `d²−Delta*c²=1`. If X=0, the root says `H | U(d−ac)` and the identity `(d−ac)(d+ac)=1+Hc²` makes d−ac a unit modulo H. Thus H|U, hence H|3q² because H=4Y+3. But H≥4q³+3>3q², contradiction. This sign-free argument uses neither an already represented nonnegative rank nor a positive eta.

With X>0, M>0. The retained `positive_parameter_solution` source uses Q=M and Pell parameter `2(M−1)+1`, i.e. multiplier `2M+1` with an even ordinate. Independently, for a first-norm solution `(x,k)` the inverse unit gives `k'=(2M+1)k−2x`: k=1 falls between consecutive squares, while k≥2 gives k'≥0 because `(2M+1)²k²−4x²=k²−4`; also k'<k since x>Mk. The inverse x-coordinate is positive and the norm is preserved, so finite integer descent reaches `(1,0)`. The forward recurrence yields `k≡2n mod 4M`. The independently reviewed main-ordinate bound gives k>q≥2, hence n≥2.

At the fixed tuple q is a power of two, and H=4a+3 is odd. Since U=q⁵s, the exact signed main-root equation and U|Dstar imply `q⁵ | H(R+1−k)`, so H is cancellable modulo q⁵ and `k≡R+1 mod q⁵`. Also `M=q⁷ws²`, so q⁵ divides 4M and `2n≡R+1 mod q⁵`. Reducing the actual rank modulo q gives `R≡C+MC`; the low source digit is even, so even k and q force C odd. The bounds `1≤C≤q−1` follow from C>0 and the shifted alpha≥1.

The receipt reproduces the author and independent q-bound checkers, pins the exact graph and Pell interface, checks the inverse identities as integer polynomials and performs 117 complete bounded descents plus finite cancellation/parity controls. These are controls accompanying the written universal proof. No Lean process, coherent provider/axiom replay, full graph zero or reverse equivalence was established. From `Computability/DiophantineConsistency` run:

```
python3 -I -S -B reviews/ordinary13-f-unshift-fixed-positive-gap-norm-congruences-independent/check.py | cmp - reviews/ordinary13-f-unshift-fixed-positive-gap-norm-congruences-independent/receipt.json
```
