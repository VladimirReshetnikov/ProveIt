# Independent review: eight compact first-carrier w classes

The reviewed `research/ordinary13-f-unshift-fixed-small-power-w-gcd/` proves the following conditional standard-integer statement: at the exact fixed compact ports, if J=1, F=0, C>0 and the first residual vanishes, then every `w≡2^e (mod beta)` for `e=0,…,7` forces `C=beta` and `alpha=1`. It does not exclude those classes, assert a full graph zero, cover other w or J, or establish a Lean/iPRA theorem.

The literal first root has the form `Z=beta*(ell+k+r−kB)−B` with `B=C*(X+K0)` and `X=q*w`. From the first norm, `beta² | Z²`; integer square divisibility gives `beta | Z` and hence `beta | B`. Since `q=beta+1`, this becomes `beta | C*(w+K0)`.

The fixed kernel is `K0=beta*rho^42+K′`, with `rho=2^67`. The independent checker parses the exact 943 source rows and 41 slot positions, accumulates their selector weights by exponent, and uses base-rho Horner evaluation to reconstruct K′. This uses a different construction from the author's shifted-power summation. Exact integer gcd then independently confirms `gcd(beta,K′+2^e)=1` for all eight e. The largest operand is 590,069 bits in memory; only bit lengths and gcd values are recorded, not the large integers themselves.

If `w≡2^e mod beta`, then `w+K0≡2^e+K′`, so it is invertible modulo beta. The first-carrier divisibility therefore gives `beta|C`. The hypotheses `C=q−alpha>0` and `alpha≥1` give `1≤C≤q−1=beta`, hence `C=beta` and `alpha=1`. This reasoning depends only on the residue of w, so it applies to each entire congruence class, including arbitrarily large natural representatives.

The checker pins the exact source recipes and child rows, reproduces the author's receipt, and performs its own exact kernel and gcd computation. It does not prove product-zero factor extraction, rule out any of the eight classes, cover arbitrary model arithmetic, or check Lean/provider dependencies.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary13-f-unshift-small-power-w-gcd-second-independent/check.py | cmp - reviews/ordinary13-f-unshift-small-power-w-gcd-second-independent/receipt.json
```
