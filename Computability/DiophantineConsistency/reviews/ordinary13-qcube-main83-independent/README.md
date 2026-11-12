# Independent review: thirteen-input q-cubed modified carrier

**PASS, external standard-integer mathematics.** At the authenticated
compact44 ports, the 13-input 83/60 graph and its 84/56 parent have equivalent
positive-zero existence. The exact degree at those ports is 60. This replay
uses the cited source theorem statements and previously reviewed arithmetic;
it is not a Lean theorem for this graph, an arbitrary-model bridge, provider
replay, PDF/JSON binding, or a global minimum claim.

For a parent zero, the already reviewed 84-to-87 and auxiliary-root maps
restore a positive free-J graph zero. The actual construction in
`FreeJ13Halt.forward` preserves J, F, alpha, X and Y; hence it preserves q
and rank when producing the 12-input literal zero. The stated
`FreeJPowerFinish.graph_power` and `FreeJPowerProjection.graph_projection`
then give `X=2^R` and `q | 3X`. For the actual `beta=2^590069−1`, the
alternative `q=3·2^j` contradicts `q≡1 (mod beta)` by cyclic binary rotation;
therefore `q | X`. Positive `w=X/q` and `gamma_prime=gamma_old+w` give a
positive new witness, and the changed carrier is identical.

For a new zero, the unscaled first norm yields `b | Bt` and a positive root
`tau`; since `tau<ell+k`, positivity of the new first coordinate forces
`Bt>0`. The actual `K0≥0` and positive X,q then force `C>0`. The explicit
`Y=q³s` and the unchanged first/main/strong/auxiliary norms supply the
fact-level hypotheses in the independently reviewed modified-carrier replay:
the rank window and `q⁴ | R+1−k` give `P72Exact.indices_ordinary` with
`mu=q⁴` and `i_prime=i`. The direct auxiliary coordinate is converted to
positive `u=y−V` using the separately reviewed auxiliary-root map; no old
graph zero is assumed. Positive main orientation gives
`d=X+ac+H(gamma_prime−W)` for `W≥0`, and the exact index and power theorem
give `X=2^R`. The same-index projection recurrence then gives
`gamma_prime=gamma0+W` with `gamma0≥2^(R−2)>X/q=w`; consequently
`gamma_old=gamma_prime−w>0`. Substituting these coordinates restores a
positive parent zero. The old literal-zero wrappers cannot be invoked on the
new graph directly; this is a fact-level replay.

The checker independently reconstructs all 83 source rows, checks topology
and liveness, verifies the main-carrier substitution in an exact sparse
integer polynomial ring, pins the relevant source theorem statements, and
replays the author's finite receipt. It authenticates P72/P115 port bytes
and computes a different weighted affine degree ray modulo 1,000,000,009.
The written degree upper bound is 60; the independent nonzero ray supplies
the matching lower bound. The small Mersenne controls do not replace the
unbounded cyclic-binary argument, and finite checks do not replace the
unbounded positive-witness proof.

From `Computability/DiophantineConsistency`, run:

```
python3 -I -S -B reviews/ordinary13-qcube-main83-independent/check.py
```

Compare stdout with `result.json`. No Lean process is run.
