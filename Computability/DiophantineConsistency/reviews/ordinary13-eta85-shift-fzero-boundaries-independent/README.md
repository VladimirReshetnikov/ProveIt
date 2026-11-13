# Independent review: shift probes and the F=0 boundary

The two [shift probes](../../research/ordinary13-eta85-shift-boundary-probes/README.md) are exact 84-row deletions of the F and alpha increments from the pinned 85-row parent. Their stated parent-to-child maps increment the corresponding child input by one. I independently reproduced both complete zeros at the stated **signed noncompact** ports and the parent output 9 at the same tuple. These are pointwise boundary examples, not compact-port zeros or proofs against a witness-changing reverse map.

The F-probe's `F=0, C≤0` exclusion is mathematically sound over ordinary naturals under the exact hypotheses: both first and main residuals vanish; beta>0, J>0 and K0>0; `0<MC<beta`; and `0≤MF<2beta`. In particular, these hypotheses are not extracted from a product zero by the argument. The graph retains `k=eta+n_zeta+1≥1`, `Y=q³s>0`, `b=beta*J=q−1>0`, `B=C(X+K0)` and `ell=XY²k≥0`.

If C<0, K0>0 makes B strictly negative. The signed first root then exceeds `b(ell+k)`, whose square is at least the first-norm right side, a contradiction. If C=0, B=0; the independently checked expansion

```
(ell+k+r)²−(1+ell(ell+k))
  = ell*k + k²−1 + 2r(ell+k) + r²
```

forces k=1, r=0 and ell=0, hence X=0. With F=0 and alpha=q the graph's signed rank is the natural `R=q²(q²−1)+W`, where `W=J(MC+q*MF)`. Its r0 is `kbase−R=k−1−R`, so the main root at k=1 is indeed `U*(...)+H*(U*gamma+R)`.

Here U=q⁵s and H=3+4Y, with q³|Y. Integer square divisibility gives U|Dstar and q⁵|HR; the factor-three cancellation loses at most one q factor, giving q⁴|R even when 3 divides q. The strict mask bounds yield `0<W<(q−1)(1+2q)<2q²`; since `R≡W−q² (mod q⁴)` and q≥2, divisibility forces W=q². Then q divides J*MC. Because q=1+beta*J, gcd(J,q)=1, so q divides MC, contradicting `0<MC<beta≤q−1`.

The separate [positive-gap boundary](../../research/ordinary13-eta85-Fzero-positive-gap-boundary/README.md) correctly supplies a natural F=0, C>0 assignment satisfying the first norm, including for arbitrary positive beta and K0. Its k=2 violates the independently reviewed main-norm square gap, so it is not a full zero. It does not settle the remaining positive-gap branch. The later [independent k>q review](../ordinary13-eta85-main-ordinate-q-bound-independent/README.md) gives the stronger main-norm-only restriction for the same shifted-k graphs.

The receipt reproduces both author checkers, independently checks both exact row deletions and signed-port zeros, verifies the first-norm polynomial identity and tests the rank contradiction on 11,200 finite cases, including 2,680 with q divisible by three. Those controls do not replace the uniform proof. There was no Lean execution, source/provider or axiom validation, compact full-zero proof, reverse existential map or endpoint proof. From `Computability/DiophantineConsistency` run:

```
python3 -I -S -B reviews/ordinary13-eta85-shift-fzero-boundaries-independent/check.py | cmp - reviews/ordinary13-eta85-shift-fzero-boundaries-independent/receipt.json
```
