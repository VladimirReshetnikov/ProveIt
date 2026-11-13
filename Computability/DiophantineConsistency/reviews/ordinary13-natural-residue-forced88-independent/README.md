# Independent review of the 13/88 mixed graph

The 88-row graph is exactly the 81-row positive parent under the documented mixed substitution, with 13 natural coordinates and seven shifts. Its six unshifted coordinates are J, w, f, y, gamma and r. The checker reconstructs all rows, checks liveness, pins the independently reviewed parent and compact ports, and proves degree exactly 60 at those ports by the A1 cancellation upper bound and an independent ray over prime 1,000,000,009 (leading coefficient 993725773). The compact P72/P115 bytes satisfy `beta>=46` and `K0+1<=(beta+1)²`. Both independent and candidate receipts reproduce.

The 81- and 82-row parents have identical common gates except for the main shift: 81 has `X=q*w` and `shift=U*gamma-(k-R-1)`; 82 treats X as input and adds `E*q` to that shift. In the X=0 forcing branch E=X*Y=0, so that additional term vanishes, and the earlier main-norm divisibility obstruction applies. Since q>0, X>0 forces w>0. The first, strong and auxiliary norm arguments for J, f and y retain the same wiring. The corrected r forcing from the 89 graph applies to X=q*w when beta and K0 are suitably represented and `K0+1<=q²`; the compact byte computation is not itself a model-cast proof.

For gamma=0 this graph's actual main shift is `R+1-k`, with no `X*Y*q` term. The same standard-integer first-norm/Pell and compact rank-window estimates as in the 90 review imply `R+1<k`, supplying the sign needed for the main norm contradiction. Its use of Pell descent and the inherited positive-parent calibration remain standard-integer claims. The source-only model analogues, compact bound representation, provider replay and iPRA endpoint are not established by this review. The graph is exactly the positive polynomial at the mixed substitution; the reverse comparison to the fully shifted graph uses the zero maps, not polynomial identity at the same tuple.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary13-natural-residue-forced88-independent/check.py | cmp - reviews/ordinary13-natural-residue-forced88-independent/result.json
python3 -I -S -B research/ordinary13-natural-residue-forced88-degree60/check.py | cmp - research/ordinary13-natural-residue-forced88-degree60/receipt.json
```
