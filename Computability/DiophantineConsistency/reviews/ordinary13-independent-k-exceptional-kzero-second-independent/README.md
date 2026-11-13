# Independent review: fixed-compact exceptional k=0 branch

The reviewed source-only packet is `research/ordinary13-independent-k-exceptional-kzero-audit/`. The checked argument establishes a positive first-factor gap for zeros in the **ordinary integers at the specific symbolic compact tuple**. It does not itself establish a model-level theorem, eliminate k=0 in the positive-gap branch, or prove a zero correspondence.

The independent unit/norm review reproduces four exhaustive mod-four exclusions. At a standard integer zero, the four integer factors multiply to one, so each is ±1; none is −1, and the first and main residuals vanish. The graph-specific first-norm split gives the exceptional case `k=r=0` and `B=−(q−1)` when the gap fails. With `d=X+K0` and `qF=q−F`, the resulting equation `qF*(d+1)=alpha*d+1` and `d≥7` imply `qF≥1`, `alpha=qF+t`, and `d*t=qF−1` for a natural t. Since `F≥1`, `7t≤q−2=J*beta−1`.

The pinned compact port recipe has little-endian low-mask digit `B−1` at index 8806, with `B=2^67`, and beta `B^8807−1`. Thus `6MC−5beta≥(B−6)*B^8806+5>0`; the stated strict upper mask bound comes from the source's special deficient digit. The symbolic kernel contains the positive `rho^30` summand, hence K0≥7. These facts are for the exact fixed tuple, not an arbitrary second port or arbitrary low mask.

The actual k=0 main norm gives `q | Dstar` and hence `q | 3*(R+1)` because `q | U` and `H≡3 mod q`. No cancellation of 3 is used. The actual graph's rank gives `R+1 ≡ u=J*MC+1−t (mod q)`. From `7t<beta*J` and `6MC>5beta` one gets `3t<3*J*MC−2*J*beta`, so `2q<3u`. The bound `MC<beta` gives `u<q`, hence `3u<3q`. Thus no multiple of positive q can equal `3u`, a contradiction.

The separate checker reproduces the independent factor review and the author's receipt, checks the rank and main-root rows, the specific fixed-port source recipes and bounded controls of the rank identity and interval. The universal proof is the arithmetic above and in the reviewed packet; the finite controls do not replace it. No Lean, build, staging, factor extraction in arbitrary models, or provider replay was performed.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary13-independent-k-exceptional-kzero-second-independent/check.py | cmp - reviews/ordinary13-independent-k-exceptional-kzero-second-independent/receipt.json
```
