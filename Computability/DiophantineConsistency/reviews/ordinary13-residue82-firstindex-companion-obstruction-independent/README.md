# Independent review: first-index companion obstruction

The source's Pell recurrence preserves `tau²-m*(m+1)*k²=1`. Independent free-polynomial checks verify the stated updates for the auxiliary natural witnesses in `tau=1+2*m*h` and `k=2*j+4*m*w`. Starting from `(tau,k,h,w)=(1,0,0,0)`, the recurrence preserves positivity, gives k>=2j, and its norm gives tau>m*k. Consequently the symbolically specified coordinates, including `zeta=k-1` and `r=45*k+1+tau-m*k`, are positive. These are ordinary finite integers even though the complete values are not materialized.

For the stated toy ports, `m=q⁷`, index `n=4,825,609`, and `2n=R+1+q⁴`. The invariant makes `k≡2n≡R+1 (mod q⁴)`, while the graph's first root becomes `46*tau` and its first norm is exactly zero. The companion carrier remains B=0 and `X=q<q²`; the scalar port and rank-window bounds hold. Independent 2-by-2 modular matrix exponentiation and evaluation of every 82 graph row give strong residual 330566 and full output 937166 modulo 1,000,003, both nonzero. This establishes that the complete output is nonzero without materializing the enormous witness.

The example refutes deductions from the explicitly listed **partial** first-norm, first-index and congruence facts. It is not a full zero, does not use the authenticated compact ports, and does not settle implications requiring the remaining residuals, exact-index conclusion, global zero existence, or an iPRA endpoint. The author's receipt reproduces. No Lean or provider check was run.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary13-residue82-firstindex-companion-obstruction-independent/check.py | cmp - reviews/ordinary13-residue82-firstindex-companion-obstruction-independent/result.json
python3 -I -S -B research/ordinary13-residue82-firstindex-companion-obstruction/check.py | cmp - research/ordinary13-residue82-firstindex-companion-obstruction/result.json
```
