# Model-indexed near-diagonal Pell height

`Trace74NearDiagonalHeightModel.lean` proves, in any model of `IΣ₁`, the height estimate

```text
power Y (j+1) < 8 X²
```

from `X ≥ 2`, `Y ≥ 1`, the shifted index bound `s ≤ j+4`, and the explicit strict Pell gap

```text
(2Y) y_(j+3)(2(XY²−1)+1) < y_(s+1)(Y(X+1)−1).
```

Here `y` is the repository's paired Pell ordinate and `power` is represented model exponentiation; the ordinary-integer note's indices are `n=j+3` and `r=s+1`. The first theorem takes the corresponding strict power gap, raises the upper exponent to `j+4`, uses model power product and addition identities, and cancels positive factors. The second theorem derives that power gap from the stated Pell gap by the previously checked `Trace74NearDiagonalPellModel.trace74_strict_power_gap`.

These theorems do not derive the strict Pell gap or the near-diagonal bound from a graph zero, establish the larger height inequality needed by the projection contradiction, settle the reverse guard, or prove an iPRA endpoint.

An author check ran the following command, exited 0, and reported `[propext, Classical.choice, Quot.sound]` for both theorems:

```text
LEAN_PATH=/tmp:/tmp/trace74-direct-four-block-1zltaw2f/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  timeout 120 /home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean \
  -M3000 -j1 -DElab.async=false --root=Computability/DiophantineConsistency/research/trace74-near-diagonal-height-model \
  Computability/DiophantineConsistency/research/trace74-near-diagonal-height-model/Trace74NearDiagonalHeightModel.lean \
  -o /tmp/Trace74NearDiagonalHeightModel.olean
```

SHA-256: source `c511d4273eadbb29518c180c00ba7a6c6584a39db686440ed9e8ea24eaf24de2`, imported `Trace74NearDiagonalPellModel.olean` `af9a5f302648ea6bab75b3bb62c8ba74e48c3922f68b0af30364b22991d621bb`, output object `d98ee6ac00adc72d8b2e95aa40b3653f125a6e2644f2fd7ba8eaec2e4ceac797`, Lean executable `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`. Earlier attempts failed before the corrected check. The temporary provider paths, their transitive dependencies, and search-path resolution have not been independently audited here; this is not a clean current-source rebuild or independent replay.
