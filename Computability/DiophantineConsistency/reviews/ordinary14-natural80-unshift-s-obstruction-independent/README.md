# Independent review: unshifting s admits a zero

The [obstruction packet](../../research/ordinary14-natural80-unshift-s-obstruction/README.md) gives a valid natural zero with `s=0` for its 80-gate graph at both the stated toy ports and the authenticated compact ports. The separate 81-gate parent has nonzero output at the same toy coordinates. Thus neither forced positivity of `s` nor an unchanged-coordinate zero transfer holds in the asserted scope. These facts do **not** show that the graphs have different zero-existence truth values, nor settle consistency, Lean elaboration or an iPRA theorem.

The graph comparison removes exactly the parent node `s=n_s+1` and substitutes `n_s` at its consumers. For the general witness, let `beta>=2`, `K0>=0`, `MC,MF>0`, choose positive `w≡1−K0 (mod beta)`, and set `q=beta+1`. The packet's `R` is positive, and `(q*w+K0−1)/beta` is a nonnegative integer, so all displayed natural coordinates are legal. Substituting `s=0`, `eta=1`, `zeta=R`, `T=R`, `f=2`, `i=3`, `r=y=1` gives `Y=U=ell=0`, `c=1`, `k=R+1`, `Dstar=0`, `Q=9` and `V=-1`. The first, main, auxiliary, strong and guard factors are all one; in particular `C=1` and the prescribed quotient makes the guard `q*w+K0-beta*n_h=1`. This is an unbounded algebraic construction in the stated port range, rather than an inference from finite samples.

The independent receipt checks the full 81-to-80 graph edit, constructs the witness from its ordinary coordinates, and evaluates the entire graph exactly. It confirms the toy vector, all five factor values, and nonzero parent output at that same vector. It separately reauthenticates and decompresses the four P72/P115 ports with zlib, verifies the hypotheses, constructs the corresponding integer witness, and evaluates all 80 gates exactly at those ports. This is an external check of pinned source and byte data; no source-to-Lean or PDF binding is asserted.

Run from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/ordinary14-natural80-unshift-s-obstruction-independent/check.py | cmp - Computability/DiophantineConsistency/reviews/ordinary14-natural80-unshift-s-obstruction-independent/result.json
```
