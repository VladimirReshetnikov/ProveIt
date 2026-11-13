# Independent review: thirteen-input unshifted-s obstruction

The [obstruction packet](../../research/ordinary13-natural87-unshift-s-obstruction/README.md) correctly demonstrates that deleting the `s=n_s+1` node from the reviewed natural-88 graph admits a zero with `s=0`, including at the authenticated compact ports. At the stated toy ports, the original 88 graph is nonzero at the same natural input vector. These facts rule out a proof that every candidate zero has `s>0` and that particular unchanged-coordinate transfer. They do not establish different global zero-existence truth values or any Lean/iPRA theorem.

The independent checker pins both graph JSON files, verifies all remaining rows of the exact gate deletion and replacement, checks topology and liveness, and evaluates the graph using an independent arithmetic interpreter. It checks the stated toy vector, including the 88-parent value, and an additional set of positive toy ports. It independently reauthenticates all four P72 payloads against both P72/P115 binding records, using zlib's gzip decoder and unsigned little-endian interpretation, then constructs and evaluates the candidate witness at those authenticated values. The candidate and review receipts both reproduce.

The witness calculation is coherent: the residue choice makes `B=q*w+K0−1` a positive multiple of `beta`; with `k=R+1` and `r=k*B+B/beta−k+1`, the graph's `Z=beta*(k+r−k*B)−B` equals `beta`. Setting `s=0` makes `Y=U=ell=0`, while the chosen `eta`, `T`, `zeta`, `f`, `i` and `y` give the displayed remaining factors all equal to one. These checks concern the external graph and concrete byte snapshots. They do not prove source-level Lean correspondence, physical PDF binding, provider closure, or optimality.

Run from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/ordinary13-natural87-unshift-s-obstruction-independent/check.py | cmp - Computability/DiophantineConsistency/reviews/ordinary13-natural87-unshift-s-obstruction-independent/result.json
```
