# Independent review: actual-rank coordinate slice

The source-only audit `research/ordinary13-independent-k-actual-rank-boundary-audit/` concerns the fixed compact tuple and the slice `J=1, F=1, alpha=2, w=s=1`. Its actual graph rank is

```text
R=(beta²+2)*(q²−1)+MC+q*MF,  q=beta+1.
```

Here q is even, beta is odd, and the compact low mask is even, so R is odd. Using `MC≤q−2` and `MF≤2q−3` gives `R≤q⁴−2q³+4q²−5`, and the resulting window slack is at least `(q−4)*(q²−1)`. This confirms `n=(R+1)/2` is integral and the displayed scalar rank window holds. The cited shared-index construction's **growth argument** uses q≥24 and n≥14; its separate illustrative condition q≥2n+2 is not required when the actual-rank window is established directly here. The natural Pell constructions do not supply signed graph roots or a full zero.

For the actual graph first root, a zero of A0 forces beta to divide the graph's `B`, since `beta² | Z²` implies `beta | Z` and the other term in Z is a multiple of beta. In this slice

```text
B=(beta−2)*(beta+1+K0)−1
 = beta*(beta+K0−1)−(2K0+3),
```

so beta must divide `2K0+3`.

The pinned kernel has its largest term `rho^8807*rho^42`, where `rho=2^67`; after subtracting `rho^42*(rho^8807−1)`, the remainder K′ is positive. The other exponents are at most 5495, selectors are bounded by `1+2^51`, and the 41 copy coefficients by `2^50`. Consequently `K′≤T*rho^5495<rho^5496`, with the displayed integer `T<rho`. Since `rho^8807≥8*rho^5496`, it follows that `0<2K′+3<beta`, so `beta ∤ (2K0+3)`. Thus A0 cannot vanish on this slice.

The reproducible checker pins sources, reproduces the author's certificate, checks key literal rows and the kernel recipe, and exercises bounded controls for parity, rank and carrier formulas. The uniform inequalities and divisibility reasoning above are not replaced by finite controls. No Lean, build, staging, arbitrary-model interpretation or unrestricted zero-map claim is made.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary13-independent-k-actual-rank-boundary-second-independent/check.py | cmp - reviews/ordinary13-independent-k-actual-rank-boundary-second-independent/receipt.json
```
