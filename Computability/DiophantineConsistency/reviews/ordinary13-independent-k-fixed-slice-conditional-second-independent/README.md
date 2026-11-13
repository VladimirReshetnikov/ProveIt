# Independent review: conditional fixed-port slice

The reviewed packet `research/ordinary13-independent-k-fixed-slice-conditional/` gives a sufficient conditional construction over the ordinary integers. Its two stated conditions remain **undecided**; it does not exhibit a graph zero or prove a parent-child reduction.

The pinned kernel decomposition `K0=rho^42*beta+K′` and `0<2K′+3<beta` make `F=K′+1` and `alpha=beta−K′−1` positive. With the specified J, w and s, direct graph substitution gives `C=1`, `B=beta*(rho^42+1)` and the stated actual rank. The displayed r is natural because the Pell first coordinate satisfies `tau>M*k`, beta and h are positive, and its substitution gives the exact signed first root `Z=beta*tau`.

For the main Pell recurrence at multiplier `a+2` and `H=3+4a`, the identity `x_{j+1}−a*y_{j+1}=2*(x_j−a*y_j)+H*y_j` gives `g−a*c≡2^R (mod H)`. Thus `H | 2^R−q` is exactly the integrality condition for the proposed positive main-root gamma. The quotient is positive because `g−a*c≥c>q`; `k−R−1=4*q^7*sFirst=U*(4*q²*sFirst)` supplies the other term. These statements are conditional on the main divisibility and the cited Pell growth argument.

For the strong factor, the determinant-one Pell matrix is invertible modulo c². Its cyclic orbit contains the identity again after a positive period at most the number `c^8` of 2-by-2 matrices. For that period, the Pell ordinate is a positive multiple of c², and the chosen i gives `i²*c⁴=Delta*(f²−1)`, so the strong residual is zero. This is ordinary finite arithmetic, not a formal model result.

For odd auxiliary Pell index j, the Pell x-coordinate is divisible by I. Either sign of `V=xj/I` then gives `yj²−I²*(yj²−V²)=1`. The separately stated natural-T equation exactly matches the graph's `V=f²*(T*c−R)−c`; if it holds, the auxiliary factor is one. Both the existence of such a j/sign/T and the main divisibility remain open.

The independent checker reproduces the author's receipt, checks graph rows, and runs small exact controls for the first carrier, main congruence, finite strong periods and odd-index auxiliary identity. The uniform matrix, congruence and Pell arguments above are not replaced by finite controls. No Lean, build, staging, arbitrary-model theorem or endpoint is claimed.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary13-independent-k-fixed-slice-conditional-second-independent/check.py | cmp - reviews/ordinary13-independent-k-fixed-slice-conditional-second-independent/receipt.json
```
