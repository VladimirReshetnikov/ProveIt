# Independent review: thirteen-input unshifted-Y obstruction

The [obstruction packet](../../research/ordinary13-natural96-unshift-y-obstruction/README.md) correctly exhibits a zero with `Y=0` after deleting the `Y=n_Y+1` gate, both for the stated toy ports and for the authenticated compact ports. At the stated toy input vector, the 97-gate parent is nonzero. Consequently the candidate's zeros do not all force `Y>0`, and that particular unchanged-coordinate transfer fails. These observations do **not** decide whether the two equations have the same global zero-existence truth value, or establish a Lean/iPRA result.

The independent checker pins both graphs, compares every surviving row under the exact gate deletion, and verifies the 96-row graph's topology and liveness. A separate arithmetic interpreter evaluates the stated toy witness and parent, an additional toy assignment, and the constructed witness for the actual fixed ports. It independently checks the P72/P115 binding hashes and lengths and decompresses each payload with zlib before interpreting it as unsigned little-endian bytes. Both the original and independent receipts reproduce.

The witness arithmetic is consistent with the displayed general construction. The residue choice gives `X ≡ 1−K0 (mod beta)` and hence `Bt=X+q*(K0−1)` is a positive multiple of `beta`. With `r=Bt/beta+1`, the graph's first residual has `Z=q³*beta=M`, so `A0=0`; with `Y=0` the named auxiliary values reduce to those listed in the packet and the remaining three constraints vanish. These checks concern the external graph and the sampled payload bytes. They do not establish a source-level Lean theorem, physical PDF binding, provider closure, global equivalence or minimality.

Run from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/ordinary13-natural96-unshift-y-obstruction-independent/check.py | cmp - Computability/DiophantineConsistency/reviews/ordinary13-natural96-unshift-y-obstruction-independent/result.json
```
