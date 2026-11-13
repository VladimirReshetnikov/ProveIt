# Independent review: coarse-bounds i-unshift zero

The [reviewed packet](../../research/ordinary13-eta-zeta84-unshift-i-coarse-bounds-zero/README.md) gives a sound standard-natural symbolic zero of the 84-row i-unshift graph at `(beta,K0,MC,MF)=(127,87,54,139)`, with the parent nonzero at the same tuple. I found no mismatch in its rank, root equations, natural-coordinate bounds or power-matching estimates. These ports satisfy the listed coarse compact-like inequalities and residues, but are **not** the fixed compact tuple. The example does not rule out an existential witness replacement or establish a Lean/iPRA result.

The pinned parent-to-child transformation removes exactly `i=n_i+1` and uses `n_i` in its place. The stated finite arithmetic gives `n=9,437,340`, `m=n+2172=9,439,512`, and the actual graph rank `R=18,874,679=2n−1`. Since m≡5 mod 7, `X=2^m≡32 mod 127`; with C=1, F=119 and K0=87, the actual first carrier `Bt=X−32` is divisible by beta. The stated first-root witness is natural and yields `Z=beta*tau`. Since `M/U=2^(m+L−14)`, the main gamma correction is integral; the Pell congruence makes its other summand integral and positive. Both exact signed roots therefore have their claimed norms.

For the delicate eta interval, write `P=2XY`, `Q=4XY²`. The checker independently verifies the exponent identity `P^(m−1)=2Y Q^(n−1)` as a polynomial identity in L, using `n=L(2L+1)` and `m=n+L`. If a Pell multiplier is A≥2, its jth ordinate lies between `(2A−1)^(j−1)` and `(2A)^(j−1)`: the recurrence identity `A*y_j−x_j=y_(j−1)` and increasing ordinates give both bounds. The main lower base is `P+2Y+3`, whereas the first upper base is `Q+2`. Their relative increments satisfy `(2Y+3)/P>1/X>2/Q`, and m>n; combined with the matched leading powers, this yields c>Yk.

For the other direction, the main upper base is at most `P(1+2/X)`, while the first lower base exceeds Q. Hence `c/(Yk)≤(1+2/X)^(m−1)`. The stated `m<2²⁴` and `L+26<m` imply `4(m−1)Y<X`; the elementary geometric bound gives the latter ratio strictly below `1+1/Y`. Thus `0<c−Yk<k` and both eta and zeta=k−eta are natural. This argument uses symbolic exponents only and does not iterate the large Pell indices.

With f=1, child i=0 and auxiliary y=1, its strong residual is zero and auxiliary factor one. The first/main factors are also one, so the child output is zero. The parent uses i=1 at the same inputs, making the output c⁴>0. An additional independent q=4, L=12 control reconstructs and evaluates every row of both graphs with a different small power match; its c has 101,076 bits and is not the claimed large witness.

The receipt reproduces the author's checker, verifies the exact graph deletion, coarse arithmetic and exponent identity, and executes the independent finite control. It does not materialize the claimed large X or Pell numbers, establish the actual fixed compact case, run Lean or validate providers/axioms/PDF semantics. From `Computability/DiophantineConsistency` run:

```
python3 -I -S -B reviews/ordinary13-eta-zeta84-unshift-i-coarse-bounds-independent/check.py | cmp - reviews/ordinary13-eta-zeta84-unshift-i-coarse-bounds-independent/receipt.json
```
