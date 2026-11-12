# Independent source review: eta-zero index/parity contradiction

The proposed theorem's complete hypothesis list is identical to the separately drafted eta-natural `indices_ordinary` list after substituting eta=0 and simplifying `c=0+Y*k` to `c=Y*k`; no first-index, rank-window, main-index/norm, strong-norm or signed auxiliary-offset assumption is omitted. The call passes eta as zero and supplies the required equality `c=0+Y*k`.

The proposed parity orientation is correct. The exact-index client gives `m=R` and `2n=R+1`, so `(R+1)%2=0` and `R%2=1`. The first Pell coordinate writes k as twice a model natural, so `c=Y*k` is divisible by 2 and `c%2=0`. The main ordinate premise is `ycoord m a=c`; the separate parity draft gives `c%2=m%2=R%2=1`, a contradiction. These are model-natural arithmetic statements conditional on both source clients, not a standard-index extrapolation.

Both imported module names are unelaborated research drafts with unresolved source/provider closure. The theorem assumes all its arithmetic facts; it does not extract factor units, roots, rank bounds or the auxiliary offset from an eta-unshifted graph, nor prove any zero map, port binding or iPRA endpoint. The pinned source signatures and finite parity controls were independently checked and the author's receipt reproduces; no Lean run or axiom report was performed.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary13-eta-zero-index-parity-contradiction-independent/check.py | cmp - reviews/ordinary13-eta-zero-index-parity-contradiction-independent/result.json
python3 -I -S -B research/ordinary13-eta-zero-index-parity-contradiction-draft/check.py | cmp - research/ordinary13-eta-zero-index-parity-contradiction-draft/result.json
```
