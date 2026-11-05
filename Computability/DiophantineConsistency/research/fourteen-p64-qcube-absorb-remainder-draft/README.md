# Conditional first-root remainder bound

`P64RemainderGap.remainder_gt` is a checked ordered-ring lemma. For
`s,r≥0`, `ell≥s²`, and `k≥2s+1`, the equation

```
(ell+r)² = 1+ell*(ell+k)
```

forces `r>s`. This may support replacing the checked 81 graph's `rho+s`
by one independent positive variable, provided its full graph zero supplies
the displayed hypotheses and the reverse positive witness map is proved.
This file does not define an 80-operation graph, bind its residuals, prove
existence equivalence, or establish an iPRA endpoint.

On 2026-11-04, Lean 4.32.0 exited 0 with axioms `[propext, Classical.choice,
Quot.sound]`, no warnings and no `sorryAx`. The command from the repository
root was:

```sh
LEAN_PATH=/tmp/p64-independent-captured-replay/lib:/tmp:/tmp/trace74-direct-four-block-1zltaw2f/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  timeout 120 /home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean \
  -M4000 -j1 -DElab.async=false \
  --root=Computability/DiophantineConsistency/research/fourteen-p64-qcube-absorb-remainder-draft \
  Computability/DiophantineConsistency/research/fourteen-p64-qcube-absorb-remainder-draft/P64RemainderGap.lean \
  -o /tmp/P64RemainderGap.olean
```

Source SHA-256:
`42defa3f1870dea45877d5d604e7a47672096cb4783f54a2dfd22c9db093c0ae`;
output SHA-256:
`421e4aaf8745227d3cba9518d7e7d0d2a45dfd281af1bb03a11429c4521c29fb`.
The direct `ModelDifferenceRing.olean` hash was
`d0fb8f9664675190dbfc25915a687cef203b8362681d9256606f1022a6dbde74`.
The temporary captured-provider chain and its complete transitive ancestry
were not independently audited in this check.
