# Two-norm model remainder inequality

`P64ModelRemainderGap.remainder_gt` proves in the indicated IΣ₁ models that
positive `X,s,eta,zeta`, `s≤Y`, `k=eta+zeta`, and the two displayed Pell
norm equations in the Lean statement imply `s<r`. The first norm uses the
root `ell+r`, with `ell=XY²k`; the second is the main Pell norm at
`a=XY+Y`, `c=eta+Yk`. It combines the checked `8XY²+4≤k` two-norm gap
with the ordered-ring remainder inequality.

This is a model lemma with explicit hypotheses. It does not itself extract
the norms from an 80-graph zero, construct a positive 81 witness, establish
zero-existence equivalence, or supply an iPRA endpoint.

On 2026-11-04 Lean 4.32.0 exited 0 with no warnings or `sorryAx` and reported
axioms `[propext, Classical.choice, Quot.sound]`. From the repository root,
after building the two checked local input objects:

```sh
LEAN_PATH=/tmp/p64-independent-captured-replay/lib:/tmp:/tmp/trace74-direct-four-block-1zltaw2f/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  timeout 120 /home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean \
  -M4000 -j1 -DElab.async=false \
  --root=Computability/DiophantineConsistency/research/fourteen-p64-qcube-absorb-remainder-draft \
  Computability/DiophantineConsistency/research/fourteen-p64-qcube-absorb-remainder-draft/P64ModelRemainderGap.lean \
  -o /tmp/P64ModelRemainderGap.olean
```

Source SHA-256:
`fde982cd3ea22825c6b08fb4a3c16a52264b49758b05b5825b23ca86ac0987ca`;
output SHA-256:
`bb9d8daa37634ddf0a66c6d0dce250f3316c81c6e73891c5829cce58d5ee5460`.
The local `P64RemainderGap.olean` and `Absorb88TwoNormGap.olean` input hashes
were `421e4aaf8745227d3cba9518d7e7d0d2a45dfd281af1bb03a11429c4521c29fb`
and `ff1f89e6c669f00370641823a9a0f6c841eb0411ecb7db1d225d10efc04c5536`.
The captured-provider chain's full transitive source/object, package,
dynamic-library and search-path ancestry was not independently audited.
